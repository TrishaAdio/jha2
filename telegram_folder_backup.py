"""Interactive Telegram shared-folder video backup utility."""

from __future__ import annotations

import asyncio
import contextlib
import getpass
import inspect
import json
import math
import os
import re
import sys
import tempfile
import time
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Awaitable, Callable, Sequence, TypeVar, cast
from urllib.parse import parse_qs, urlparse

from rich.align import Align
from rich.console import Console
from rich.markup import escape
from rich.panel import Panel
from rich.progress import (
    BarColumn,
    DownloadColumn,
    Progress,
    SpinnerColumn,
    TextColumn,
    TimeRemainingColumn,
    TransferSpeedColumn,
)
from rich.prompt import Prompt
from rich.table import Table
from rich.text import Text
from telethon import TelegramClient, helpers, types, utils
from telethon.errors import (
    ChatForwardsRestrictedError,
    FileReferenceExpiredError,
    FloodWaitError,
    MediaEmptyError,
    PasswordHashInvalidError,
    PhoneCodeExpiredError,
    PhoneCodeInvalidError,
    InviteHashExpiredError,
    InviteHashInvalidError,
    InviteRequestSentError,
    RPCError,
    ServerError,
    SessionPasswordNeededError,
    TimedOutError,
    UserAlreadyParticipantError,
    UserPrivacyRestrictedError,
)
from telethon.network import MTProtoSender
from telethon.tl.alltlobjects import LAYER
from telethon.tl.functions import InvokeWithLayerRequest, channels, chatlists, messages
from telethon.tl.functions.auth import (
    ExportAuthorizationRequest,
    ImportAuthorizationRequest,
)
from telethon.tl.functions.upload import GetFileRequest, SaveBigFilePartRequest
from telethon.tl.types import chatlists as chatlist_types

SESSION_FILE = "heartvault"
STATE_FILE = ".heartvault_state.json"
# Short waits are absorbed; anything longer pauses that account and moves its
# work to a healthy session instead of blocking or failing videos.
MAX_FLOOD_WAIT = 90
# Only videos at or below this size are backed up; larger ones are skipped.
MAX_VIDEO_BYTES = 100 * 1024 * 1024
# 512 KiB parts evenly divide Telegram's 1 MiB block and satisfy the upload
# 512 KiB part limit, so the same size works for parallel download and upload.
PART_SIZE = 512 * 1024
MAX_UPLOAD_PARTS = 4000
# Extra connections opened per transfer. Each connection gets its own slice of
# the file, so throughput scales roughly linearly with this until bandwidth or
# Telegram throttling is the limit.
MAX_TRANSFER_CONNECTIONS = 4
# Maximum number of extra worker accounts that can share the workload.
MAX_WORKERS = 10
# Minimum spacing between two join requests from the same run. Joining chats
# back to back is what triggers Telegram's long join FloodWaits, so links are
# consumed one by one with a small breather in between.
JOIN_INTERVAL = 4.0
# A single file part is retried this many times before the video is failed.
# Telegram frequently times out or briefly drops individual part requests on
# large transfers, and one slow part must not abort the whole file.
PART_RETRIES = 6
# Transient errors worth retrying at the part level (timeouts, server hiccups,
# and dropped connections). Builtin TimeoutError is asyncio's timeout in 3.11+.
TRANSIENT_TRANSFER_ERRORS = (
    TimedOutError,
    ServerError,
    ConnectionError,
    TimeoutError,
)
HEART = "💗"
TITLE_SUFFIX = f" ~ {HEART}"
SMALL_CAPS = str.maketrans(
    {
        "a": "ᴀ",
        "b": "ʙ",
        "c": "ᴄ",
        "d": "ᴅ",
        "e": "ᴇ",
        "f": "ꜰ",
        "g": "ɢ",
        "h": "ʜ",
        "i": "ɪ",
        "j": "ᴊ",
        "k": "ᴋ",
        "l": "ʟ",
        "m": "ᴍ",
        "n": "ɴ",
        "o": "ᴏ",
        "p": "ᴘ",
        "q": "q",
        "r": "ʀ",
        "s": "s",
        "t": "ᴛ",
        "u": "ᴜ",
        "v": "ᴠ",
        "w": "ᴡ",
        "x": "x",
        "y": "ʏ",
        "z": "ᴢ",
    }
)

console = Console()
T = TypeVar("T")


@dataclass(slots=True)
class Session:
    """One logged-in account participating in the backup (main or worker)."""

    client: TelegramClient
    label: str
    user_id: int
    name: str = ""
    # Monotonic timestamp until which this session is paused (Telegram throttle).
    cooldown_until: float = 0.0


@dataclass(slots=True)
class ImportedFolder:
    title: str
    chats: list[types.Chat | types.Channel]


@dataclass(slots=True)
class BackupResult:
    source_title: str
    backup_title: str
    destination: Any | None
    invite_link: str | None = None
    copied: int = 0
    failed: int = 0
    skipped: int = 0
    error: str | None = None


class StateStore:
    """Durable, brand-keyed checkpoints shared across every folder and run.

    Backup groups are keyed by a "brand" derived from the source name (see
    ``brand_key``) so that sibling channels such as "Chochlate qt" and
    "Chochlate haha" reuse a single group. Copied message ids are tracked per
    source inside each group to keep de-duplication correct even when several
    channels share one destination.
    """

    def __init__(self) -> None:
        self.path = Path(__file__).resolve().parent / STATE_FILE
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            self.data = raw if isinstance(raw, dict) else {}
        except FileNotFoundError:
            self.data = {}
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"Could not read backup state: {error}") from error

        self.groups: dict[str, dict[str, Any]] = self.data.setdefault("groups", {})
        self._migrate_legacy()

    def _migrate_legacy(self) -> None:
        """Fold the old per-folder, per-peer layout into brand-keyed groups."""
        folders = self.data.get("folders")
        if not isinstance(folders, dict):
            return
        for folder in folders.values():
            old_groups = folder.get("groups", {}) if isinstance(folder, dict) else {}
            for source_key, record in old_groups.items():
                if not isinstance(record, dict) or "destination_id" not in record:
                    continue
                title = record.get("source_title") or ""
                brand = brand_key(title)
                group = self.groups.get(brand)
                if group is None:
                    group = {
                        "backup_title": record.get("backup_title"),
                        "destination_id": record.get("destination_id"),
                        "access_hash": record.get("access_hash"),
                        "invite_link": record.get("invite_link"),
                        "sources": {},
                    }
                    self.groups[brand] = group
                group["sources"].setdefault(
                    source_key,
                    {
                        "title": title,
                        "copied_message_ids": record.get("copied_message_ids", []),
                    },
                )
        self.data.pop("folders", None)
        self.save()

    def save(self) -> None:
        temporary = self.path.with_suffix(".tmp")
        try:
            temporary.write_text(
                json.dumps(self.data, ensure_ascii=False, indent=2, sort_keys=True),
                encoding="utf-8",
            )
            temporary.replace(self.path)
        except OSError as error:
            temporary.unlink(missing_ok=True)
            raise RuntimeError(f"Could not save backup state: {error}") from error


def banner() -> None:
    console.print(
        Panel(
            Align.center(
                "[bold bright_magenta]H E A R T  V A U L T[/bold bright_magenta]\n"
                "[dim]Telegram group & folder video backup · original quality[/dim]"
            ),
            border_style="bright_magenta",
            padding=(1, 4),
        )
    )


def normalize_text(value: str) -> str:
    """Turn common Unicode display alphabets into clean text."""
    normalized = unicodedata.normalize("NFKD", value)
    cleaned = "".join(
        character
        for character in normalized
        if not unicodedata.combining(character)
        and unicodedata.category(character) not in {"Cc", "Cf", "Cs"}
    )
    return re.sub(r"\s+", " ", cleaned).strip()


def canonical_source_name(value: str) -> str:
    """Remove an existing HeartVault wrapper to avoid double-styled names."""
    cleaned = normalize_text(value)
    wrapped = re.fullmatch(r"\{(.*)\}\s*~\s*💗", cleaned)
    if wrapped:
        cleaned = wrapped.group(1)
    return re.sub(r"\s*~\s*💗\s*$", "", cleaned).strip()


def small_caps(value: str) -> str:
    return canonical_source_name(value).lower().translate(SMALL_CAPS)


def backup_chat_title(source_title: str) -> str:
    styled = small_caps(source_title) or "ᴜɴᴛɪᴛʟᴇᴅ"
    max_inner = 128 - len(TITLE_SUFFIX)
    return f"{styled[:max_inner].rstrip()}{TITLE_SUFFIX}"


def brand_key(source_title: str) -> str:
    """Group sibling channels under a shared key from the first name word.

    Decorations and case are normalized first, so "Chochlate qt",
    "𝗖𝗵𝗼𝗰𝗵𝗹𝗮𝘁𝗲 haha" and "chochlate 18+" all map to "chochlate" and reuse a
    single backup group. Names with no usable word fall back to the whole
    normalized string.
    """
    base = canonical_source_name(source_title).lower().strip()
    if not base:
        return "backup"
    tokens = base.split()
    first = tokens[0]
    trimmed = re.sub(r"^[\W_]+|[\W_]+$", "", first, flags=re.UNICODE)
    return trimmed or first


def backup_folder_title(source_title: str) -> str:
    styled = small_caps(source_title) or "ʙᴀᴄᴋᴜᴘ"
    return f"{styled[:9].rstrip()} {HEART}"


def video_caption(message_id: int) -> str:
    return f"ᴠɪᴅᴇᴏ ~ {HEART} {message_id}"


TELEGRAM_HOSTS = {"t.me", "telegram.me", "telegram.dog"}
# Finds shared-folder links inside free text (used to follow folder links that
# a group advertises in its description).
FOLDER_LINK_IN_TEXT = re.compile(
    r"(?:https?://)?(?:www\.)?t(?:elegram)?\.(?:me|dog)/addlist/([A-Za-z0-9_-]+)"
    r"|tg://addlist\?slug=([A-Za-z0-9_-]+)",
    re.IGNORECASE,
)


@dataclass(slots=True)
class Target:
    """One pasted link, normalized into something we can join.

    ``kind`` is one of:
      folder   – t.me/addlist/... shared folder (many chats at once)
      public   – @username / t.me/username public group or channel
      invite   – t.me/+hash or t.me/joinchat/hash private invite
      internal – t.me/c/<id>/... link to a chat this account already knows
    """

    kind: str
    value: str
    label: str
    origin: str = "paste"

    @property
    def key(self) -> str:
        return f"{self.kind}:{self.value.lower()}"

    @property
    def is_folder(self) -> bool:
        return self.kind == "folder"


def _checked_slug(value: str, what: str) -> str:
    slug = value.strip()
    if not re.fullmatch(r"[A-Za-z0-9_-]+", slug):
        raise ValueError(f"The {what} link has an invalid code.")
    return slug


def _checked_username(value: str) -> str:
    name = value.strip().lstrip("@")
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]{2,31}", name):
        raise ValueError("This is not a valid Telegram username or link.")
    return name


def parse_target(raw_link: str) -> Target:
    """Normalize any pasted Telegram link into a joinable :class:`Target`."""
    value = raw_link.strip().strip(",;")
    if not value:
        raise ValueError("The link cannot be empty.")

    if value.lower().startswith("tg://"):
        parsed = urlparse(value)
        query = parse_qs(parsed.query)
        host = parsed.netloc.lower()
        if host == "addlist":
            return Target(
                "folder", _checked_slug(query.get("slug", [""])[0], "shared-folder"), value
            )
        if host == "join":
            return Target(
                "invite", _checked_slug(query.get("invite", [""])[0], "invite"), value
            )
        if host == "resolve":
            return Target(
                "public", _checked_username(query.get("domain", [""])[0]), value
            )
        raise ValueError("This tg:// link is not a chat or folder link.")

    if value.startswith("@"):
        return Target("public", _checked_username(value), value)

    looks_like_link = "://" in value or re.match(
        r"(?:www\.)?t(?:elegram)?\.(?:me|dog)/", value, re.IGNORECASE
    )
    if not looks_like_link:
        # Bare username pasted without any decoration.
        return Target("public", _checked_username(value), value)

    parsed = urlparse(value if "://" in value else f"https://{value}")
    host = parsed.netloc.lower().removeprefix("www.")
    if host not in TELEGRAM_HOSTS:
        raise ValueError("Only t.me links are supported.")
    parts = [part for part in parsed.path.split("/") if part]
    if not parts:
        raise ValueError("This t.me link points at no chat.")

    first = parts[0]
    lowered = first.lower()
    if lowered == "addlist":
        if len(parts) < 2:
            raise ValueError("The shared-folder link has no code.")
        return Target("folder", _checked_slug(parts[1], "shared-folder"), value)
    if lowered == "joinchat":
        if len(parts) < 2:
            raise ValueError("The invite link has no code.")
        return Target("invite", _checked_slug(parts[1], "invite"), value)
    if first.startswith("+"):
        return Target("invite", _checked_slug(first[1:], "invite"), value)
    if lowered == "c" and len(parts) >= 2 and parts[1].isdigit():
        return Target("internal", parts[1], value)
    if lowered in {"s", "proxy", "socks", "share", "iv", "login"}:
        if lowered == "s" and len(parts) >= 2:
            return Target("public", _checked_username(parts[1]), value)
        raise ValueError("This t.me link is not a chat link.")
    return Target("public", _checked_username(first), value)


def parse_target_list(raw: str) -> tuple[list[Target], list[str]]:
    """Split a pasted blob into ordered, de-duplicated targets.

    Returns the targets plus the pieces that could not be understood, so the
    run can report them without stopping.
    """
    targets: list[Target] = []
    rejected: list[str] = []
    seen: set[str] = set()
    for piece in re.split(r"[\s,]+", raw.strip()):
        if not piece:
            continue
        try:
            target = parse_target(piece)
        except ValueError as error:
            rejected.append(f"{piece} ({error})")
            continue
        if target.key in seen:
            continue
        seen.add(target.key)
        targets.append(target)
    return targets, rejected


def folder_slugs_in_text(text: str) -> list[str]:
    """Pull every shared-folder slug out of a chat description."""
    slugs: list[str] = []
    for match in FOLDER_LINK_IN_TEXT.finditer(text or ""):
        slug = match.group(1) or match.group(2)
        if slug and slug not in slugs:
            slugs.append(slug)
    return slugs


class FloodTooLongError(RuntimeError):
    """Raised when Telegram asks for a wait longer than we will tolerate.

    Subclasses RuntimeError so existing handlers still catch it, while the
    worker pool can catch it specifically to pause that account.
    """

    def __init__(self, seconds: int, label: str) -> None:
        self.seconds = seconds
        super().__init__(
            f"Telegram requested a {seconds}s wait during {label}; "
            "progress is saved, so rerun later to resume."
        )


async def rpc_call(
    label: str,
    operation: Callable[[], Awaitable[T]],
    *,
    retries: int = 3,
    retry_server_errors: bool = True,
) -> T:
    """Run a Telegram operation with bounded FloodWait/server-error handling."""
    attempt = 0
    while True:
        try:
            return await operation()
        except FloodWaitError as error:
            wait_for = max(1, int(error.seconds)) + 1
            if wait_for > MAX_FLOOD_WAIT:
                raise FloodTooLongError(wait_for, label) from error
            console.log(
                f"[yellow]Telegram rate limit:[/yellow] {escape(label)}; "
                f"waiting {wait_for}s"
            )
            await asyncio.sleep(wait_for)
        except ServerError as error:
            attempt += 1
            if not retry_server_errors or attempt >= retries:
                raise
            delay = min(2**attempt, 10)
            console.log(
                f"[yellow]{escape(label)} failed ({type(error).__name__}); "
                f"retrying in {delay}s[/yellow]"
            )
            await asyncio.sleep(delay)


async def finish_two_factor_login(client: TelegramClient) -> None:
    for attempt in range(1, 4):
        password = getpass.getpass("Two-step verification password (hidden): ")
        try:
            await rpc_call(
                "two-step verification",
                lambda: client.sign_in(password=password),
            )
            return
        except PasswordHashInvalidError:
            if attempt == 3:
                raise RuntimeError(
                    "Two-step verification failed three times."
                ) from None
            console.print("[yellow]Incorrect password. Please try again.[/yellow]")


async def finish_otp_login(client: TelegramClient, phone: str) -> None:
    for attempt in range(1, 4):
        otp = getpass.getpass("OTP code (hidden): ").replace(" ", "")
        try:
            await rpc_call(
                "sign in",
                lambda: client.sign_in(phone=phone, code=otp),
            )
            return
        except PhoneCodeInvalidError:
            if attempt == 3:
                raise RuntimeError("The OTP was invalid three times.") from None
            console.print("[yellow]Invalid OTP. Please try again.[/yellow]")
        except PhoneCodeExpiredError:
            raise RuntimeError(
                "The OTP expired. Start the script again for a new code."
            ) from None
        except SessionPasswordNeededError:
            await finish_two_factor_login(client)
            return


async def login_client(
    session_name: str, api_id: int, api_hash: str, role: str
) -> tuple[TelegramClient, Any]:
    session_path = Path(__file__).resolve().parent / session_name
    client = TelegramClient(str(session_path), api_id, api_hash)
    await client.connect()

    if not await client.is_user_authorized():
        phone = Prompt.ask(
            f"[bright_cyan]{role} phone number[/bright_cyan]", default="+"
        )
        await rpc_call("send login code", lambda: client.send_code_request(phone))
        await finish_otp_login(client, phone)

    me = await client.get_me()
    if me is None:
        raise RuntimeError(f"{role} login succeeded but returned no user profile.")
    display_name = utils.get_display_name(me) or str(getattr(me, "id", "unknown"))
    console.print(
        f"[green]{role} connected as[/green] [bold]{escape(display_name)}[/bold]"
    )
    return client, me


async def authenticate() -> tuple[TelegramClient, Any, int, str]:
    console.print("\n[bold bright_magenta]Login[/bold bright_magenta]")
    api_id_text = Prompt.ask("[bright_cyan]API ID[/bright_cyan]").strip()
    if not api_id_text.isdigit():
        raise ValueError("API ID must contain digits only.")
    api_id = int(api_id_text)

    api_hash = getpass.getpass("API Hash (hidden): ").strip()
    if not re.fullmatch(r"[0-9a-fA-F]{32}", api_hash):
        raise ValueError(
            "API Hash must be the 32-character value from my.telegram.org."
        )

    client, me = await login_client(SESSION_FILE, api_id, api_hash, "Main")
    return client, me, api_id, api_hash


async def authenticate_workers(
    api_id: int, api_hash: str, count: int, existing_ids: set[int]
) -> list[Session]:
    """Log in extra accounts that share the workload. They reuse the main
    application's API credentials; each just needs its own phone/OTP once,
    after which the session persists to disk. Accounts already used (as the
    owner or another worker) are skipped so duplicates do not silently reduce
    the number of distinct workers."""
    workers: list[Session] = []
    seen = set(existing_ids)
    for number in range(1, count + 1):
        console.print(
            f"\n[bold bright_magenta]Worker {number} login[/bold bright_magenta]"
        )
        try:
            client, me = await login_client(
                f"{SESSION_FILE}_worker{number}", api_id, api_hash, f"Worker {number}"
            )
        except (RPCError, RuntimeError, ValueError) as error:
            console.print(
                f"[yellow]Worker {number} skipped ({escape(str(error))}).[/yellow]"
            )
            continue
        if int(me.id) in seen:
            console.print(
                f"[yellow]Worker {number} is the same account as another "
                f"session; skipping the duplicate.[/yellow]"
            )
            await disconnect_client(client)
            continue
        seen.add(int(me.id))
        workers.append(
            Session(
                client=client,
                label=f"w{number}",
                user_id=int(me.id),
                name=utils.get_display_name(me) or "",
            )
        )
    return workers


def peer_entity_map(
    chats: Sequence[Any],
) -> dict[int, types.Chat | types.Channel]:
    return {
        utils.get_peer_id(chat): chat
        for chat in chats
        if isinstance(chat, (types.Chat, types.Channel))
    }


async def resolve_input_peers(
    client: TelegramClient,
    peer_refs: Sequence[Any],
    chats: Sequence[Any],
) -> tuple[list[Any], list[types.Chat | types.Channel]]:
    by_id = peer_entity_map(chats)
    input_peers: list[Any] = []
    entities: list[types.Chat | types.Channel] = []

    for peer in peer_refs:
        entity = by_id.get(utils.get_peer_id(peer))
        if entity is None:
            continue
        try:
            input_peer = await client.get_input_entity(entity)
        except (TypeError, ValueError):
            continue
        input_peers.append(input_peer)
        entities.append(entity)
    return input_peers, entities


async def imported_filter_title(client: TelegramClient, filter_id: int) -> str:
    filters = cast(
        Any,
        await rpc_call(
            "load imported folder",
            lambda: client(messages.GetDialogFiltersRequest()),
        ),
    )
    for dialog_filter in filters.filters:
        if getattr(dialog_filter, "id", None) == filter_id:
            title = getattr(dialog_filter, "title", None)
            return getattr(title, "text", None) or str(title or "Backup")
    return "Backup"


def is_chatlists_full(error: Exception) -> bool:
    return "CHATLISTS_TOO_MUCH" in str(error)


async def join_channels_individually(
    client: TelegramClient, entities: Sequence[Any], label: str
) -> None:
    """Join each source channel directly, creating no folder.

    Used when the account already has the maximum number of Telegram folders
    (CHATLISTS_TOO_MUCH): we still need channel membership to download, but we
    do not need the folder itself.
    """
    for entity in entities:
        if not isinstance(entity, types.Channel):
            continue
        name = utils.get_display_name(entity) or "channel"
        try:
            await client(
                channels.JoinChannelRequest(cast(Any, utils.get_input_channel(entity)))
            )
        except UserAlreadyParticipantError:
            pass
        except FloodWaitError as error:
            console.print(
                f"[yellow]{label}: joining '{escape(name)}' is rate-limited "
                f"({int(error.seconds)}s); public channels still read without "
                f"joining.[/yellow]"
            )
        except (RPCError, RuntimeError):
            # Public channels can be read without joining, so keep going.
            pass


_last_join_at = 0.0


async def pace_joins() -> None:
    """Keep at least ``JOIN_INTERVAL`` seconds between two join requests."""
    global _last_join_at
    wait = JOIN_INTERVAL - (time.monotonic() - _last_join_at)
    if wait > 0:
        await asyncio.sleep(wait)
    _last_join_at = time.monotonic()


async def join_public_chat(
    client: TelegramClient, username: str, label: str
) -> types.Chat | types.Channel:
    """Resolve a public @username and join it (no-op when already a member)."""
    entity = cast(
        Any,
        await rpc_call(
            f"{label}: resolve @{username}",
            lambda: client.get_entity(username),
        ),
    )
    if not isinstance(entity, (types.Chat, types.Channel)):
        raise ValueError(f"@{username} is a user, not a group or channel.")
    if isinstance(entity, types.Channel):
        await pace_joins()
        try:
            await rpc_call(
                f"{label}: join @{username}",
                lambda: client(
                    channels.JoinChannelRequest(
                        cast(Any, utils.get_input_channel(entity))
                    )
                ),
                retry_server_errors=False,
            )
        except UserAlreadyParticipantError:
            pass
    return entity


async def join_invite_chat(
    client: TelegramClient, invite_hash: str, label: str
) -> types.Chat | types.Channel:
    """Join a private chat from a t.me/+hash invite and return its entity."""
    checked = cast(
        Any,
        await rpc_call(
            f"{label}: check invite",
            lambda: client(messages.CheckChatInviteRequest(invite_hash)),
        ),
    )
    already = getattr(checked, "chat", None)
    if isinstance(checked, types.ChatInviteAlready) and isinstance(
        already, (types.Chat, types.Channel)
    ):
        return already

    await pace_joins()
    try:
        updates = cast(
            Any,
            await rpc_call(
                f"{label}: join private chat",
                lambda: client(messages.ImportChatInviteRequest(invite_hash)),
                retry_server_errors=False,
            ),
        )
    except UserAlreadyParticipantError:
        if isinstance(already, (types.Chat, types.Channel)):
            return already
        raise
    except InviteRequestSentError as error:
        raise RuntimeError(
            "This chat needs admin approval; the join request was sent."
        ) from error
    for chat in getattr(updates, "chats", None) or []:
        if isinstance(chat, (types.Chat, types.Channel)):
            return chat
    if isinstance(already, (types.Chat, types.Channel)):
        return already
    raise RuntimeError("Telegram accepted the invite but returned no chat.")


async def join_target_chat(
    client: TelegramClient, target: Target, label: str
) -> types.Chat | types.Channel:
    """Join (or resolve) one single-chat link and return its entity."""
    if target.kind == "public":
        return await join_public_chat(client, target.value, label)
    if target.kind == "invite":
        return await join_invite_chat(client, target.value, label)
    if target.kind == "internal":
        entity = cast(
            Any,
            await rpc_call(
                f"{label}: resolve chat",
                lambda: client.get_entity(types.PeerChannel(int(target.value))),
            ),
        )
        if not isinstance(entity, (types.Chat, types.Channel)):
            raise ValueError("That t.me/c/... link is not a group or channel.")
        return entity
    raise ValueError(f"'{target.label}' is not a single-chat link.")


async def chat_description(client: TelegramClient, entity: Any) -> str:
    """Best-effort read of a chat's About text (empty string when unavailable)."""
    try:
        if isinstance(entity, types.Channel):
            full = cast(
                Any,
                await rpc_call(
                    "read description",
                    lambda: client(
                        channels.GetFullChannelRequest(
                            cast(Any, utils.get_input_channel(entity))
                        )
                    ),
                ),
            )
        elif isinstance(entity, types.Chat):
            full = cast(
                Any,
                await rpc_call(
                    "read description",
                    lambda: client(messages.GetFullChatRequest(chat_id=entity.id)),
                ),
            )
        else:
            return ""
    except (RPCError, RuntimeError, ValueError, TypeError):
        return ""
    return str(getattr(getattr(full, "full_chat", None), "about", "") or "")


async def chatlist_filter_ids(client: TelegramClient) -> set[int]:
    filters = cast(
        Any,
        await rpc_call(
            "load Telegram folders",
            lambda: client(messages.GetDialogFiltersRequest()),
        ),
    )
    return {
        int(item.id)
        for item in filters.filters
        if isinstance(item, types.DialogFilterChatlist)
    }


async def release_chatlist_slot(
    client: TelegramClient, filter_id: int, label: str
) -> None:
    """Remove a shared-folder view while keeping every channel in it.

    ``leaveChatlist`` with an empty ``peers`` list deletes only the folder;
    all channels/groups stay joined, so this never loses access to chats.
    """
    try:
        await rpc_call(
            f"{label}: release folder slot",
            lambda: client(
                chatlists.LeaveChatlistRequest(
                    chatlist=types.InputChatlistDialogFilter(filter_id), peers=[]
                )
            ),
            retry_server_errors=False,
        )
    except (RPCError, RuntimeError):
        pass


async def join_chatlist_transient(
    client: TelegramClient, slug: str, input_peers: list[Any], label: str
) -> None:
    """Join a shared folder's channels without permanently keeping the folder.

    Steps: import the folder (joins the channels, including private ones),
    then release the folder slot but keep the channels. If the account is at
    the shared-folder limit, free one slot from an existing shared folder
    (its channels are kept) and retry. The tool therefore never accumulates
    folder slots across runs.
    """
    baseline = await chatlist_filter_ids(client)

    def do_join() -> Any:
        return client(chatlists.JoinChatlistInviteRequest(slug=slug, peers=input_peers))

    try:
        await rpc_call(f"{label}: join folder", do_join, retry_server_errors=False)
    except RPCError as error:
        if not is_chatlists_full(error) or not baseline:
            raise
        victim = max(baseline)
        console.print(
            f"[yellow]{label}: folder limit reached; releasing one shared-folder "
            f"view to make room (all its channels stay joined).[/yellow]"
        )
        await release_chatlist_slot(client, victim, label)
        baseline.discard(victim)
        await rpc_call(
            f"{label}: join folder (retry)", do_join, retry_server_errors=False
        )

    # Release our freshly imported folder too, keeping the channels, so the
    # slot is not held after this run.
    after = await chatlist_filter_ids(client)
    dropped = sorted(after - baseline)
    for new_id in dropped:
        await release_chatlist_slot(client, new_id, label)
    if dropped:
        console.print(f"[dim]{label}: folder view removed, chats kept[/dim]")


async def import_shared_folder(client: TelegramClient, slug: str) -> ImportedFolder:
    console.print(
        "\n[bold bright_magenta]Importing shared folder[/bold bright_magenta]"
    )
    checked = cast(
        Any,
        await rpc_call(
            "check shared folder",
            lambda: client(chatlists.CheckChatlistInviteRequest(slug=slug)),
        ),
    )

    if isinstance(checked, chatlist_types.ChatlistInvite):
        title = checked.title.text
        input_peers, entities = await resolve_input_peers(
            client, checked.peers, checked.chats
        )
        if not input_peers:
            raise RuntimeError("The folder contains no accessible channels or groups.")
        try:
            await join_chatlist_transient(client, slug, input_peers, "Main")
        except RPCError as error:
            if not is_chatlists_full(error):
                raise
            console.print(
                "[yellow]Could not free a folder slot; joining public channels "
                "only (private ones may be unreachable this run).[/yellow]"
            )
            await join_channels_individually(client, entities, "Main")
    elif isinstance(checked, chatlist_types.ChatlistInviteAlready):
        title = await imported_filter_title(client, checked.filter_id)
        all_refs = [*checked.already_peers, *checked.missing_peers]
        _, entities = await resolve_input_peers(client, all_refs, checked.chats)
        if checked.missing_peers:
            missing_inputs, _ = await resolve_input_peers(
                client, checked.missing_peers, checked.chats
            )
            if missing_inputs:
                chatlist = types.InputChatlistDialogFilter(checked.filter_id)
                await rpc_call(
                    "join new folder chats",
                    lambda: client(
                        chatlists.JoinChatlistUpdatesRequest(
                            chatlist=chatlist,
                            peers=missing_inputs,
                        )
                    ),
                )
    else:
        raise RuntimeError(f"Unexpected folder response: {type(checked).__name__}")

    accessible = [
        entity
        for entity in entities
        if isinstance(entity, (types.Chat, types.Channel))
        and not isinstance(entity, types.ChannelForbidden)
        and not getattr(entity, "deactivated", False)
    ]
    if not accessible:
        raise RuntimeError(
            "The folder has no accessible groups or channels to back up."
        )

    console.print(
        f"[green]Folder ready:[/green] [bold]{escape(title)}[/bold] "
        f"· {len(accessible)} source chat(s)"
    )
    return ImportedFolder(title=title, chats=accessible)


def to_peer(entity: Any) -> Any:
    if isinstance(entity, types.Channel):
        return types.PeerChannel(entity.id)
    if isinstance(entity, types.Chat):
        return types.PeerChat(entity.id)
    return entity


def parse_invite_hash(link: str) -> str:
    marker = link.strip().rstrip("/").rsplit("/", 1)[-1]
    return marker[1:] if marker.startswith("+") else marker


async def ensure_folder_joined(session: Session, slug: str) -> bool:
    """Best-effort: make a worker a member of every accessible source chat."""
    client = session.client
    try:
        checked = cast(
            Any,
            await rpc_call(
                f"{session.label}: check folder",
                lambda: client(chatlists.CheckChatlistInviteRequest(slug=slug)),
            ),
        )
        if isinstance(checked, chatlist_types.ChatlistInvite):
            input_peers, entities = await resolve_input_peers(
                client, checked.peers, checked.chats
            )
            if input_peers:
                try:
                    await join_chatlist_transient(
                        client, slug, input_peers, session.label
                    )
                except RPCError as error:
                    if not is_chatlists_full(error):
                        raise
                    await join_channels_individually(client, entities, session.label)
        elif isinstance(checked, chatlist_types.ChatlistInviteAlready):
            if checked.missing_peers:
                missing, _ = await resolve_input_peers(
                    client, checked.missing_peers, checked.chats
                )
                if missing:
                    await rpc_call(
                        f"{session.label}: join folder updates",
                        lambda: client(
                            chatlists.JoinChatlistUpdatesRequest(
                                chatlist=types.InputChatlistDialogFilter(
                                    checked.filter_id
                                ),
                                peers=missing,
                            )
                        ),
                    )
        return True
    except (RPCError, RuntimeError) as error:
        console.print(
            f"[yellow]{session.label} could not join the folder: "
            f"{escape(str(error))}[/yellow]"
        )
        return False


async def ensure_chat_joined(session: Session, target: Target) -> bool:
    """Best-effort: make a worker a member of one pasted group/channel link."""
    try:
        await join_target_chat(session.client, target, session.label)
        return True
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        console.print(
            f"[yellow]{session.label} could not join "
            f"{escape(target.label)}: {escape(str(error))}[/yellow]"
        )
        return False


async def promote_workers(
    main_client: TelegramClient, destination: Any, workers: list[Session]
) -> None:
    """Promote every joined worker to admin in the destination group so they
    can post reliably and manage the backup alongside the main account."""
    if not workers:
        return
    try:
        channel = cast(
            Any,
            utils.get_input_channel(await main_client.get_input_entity(destination)),
        )
    except (RPCError, ValueError, TypeError):
        return
    # Fetch participants so the main account caches each worker's access hash.
    try:
        await main_client.get_participants(destination, limit=200)
    except (RPCError, ValueError):
        pass

    rights = types.ChatAdminRights(
        change_info=True,
        post_messages=True,
        edit_messages=True,
        delete_messages=True,
        ban_users=True,
        invite_users=True,
        pin_messages=True,
        manage_call=True,
    )
    for worker in workers:
        try:
            user = cast(
                Any,
                utils.get_input_user(
                    await main_client.get_input_entity(worker.user_id)
                ),
            )
        except (RPCError, ValueError, TypeError):
            console.print(
                f"[yellow]Could not resolve {worker.label} to promote[/yellow]"
            )
            continue
        try:
            await rpc_call(
                f"promote {worker.label}",
                lambda user=user: main_client(
                    channels.EditAdminRequest(
                        channel=channel,
                        user_id=user,
                        admin_rights=rights,
                        rank="worker",
                    )
                ),
                retry_server_errors=False,
            )
            console.print(f"[green]{worker.label} promoted to admin[/green]")
        except (RPCError, RuntimeError) as error:
            console.print(
                f"[yellow]Could not promote {worker.label}: "
                f"{escape(str(error))}[/yellow]"
            )


async def resolve_worker_user(
    owner_client: TelegramClient, worker: Session, source: Any
) -> Any | None:
    """Resolve a worker to an InputUser the owner can act on.

    First tries the owner's cache (populated once the owner and worker share
    a group). Otherwise searches the shared source supergroup by the worker's
    name, which caches the worker without any rate-limited join.
    """
    try:
        return cast(
            Any,
            utils.get_input_user(await owner_client.get_input_entity(worker.user_id)),
        )
    except (ValueError, RPCError, TypeError):
        pass
    if isinstance(source, types.Channel) and worker.name:
        try:
            found = await owner_client.get_participants(
                source, search=worker.name, limit=50
            )
        except (RPCError, ValueError, TypeError):
            found = []
        if any(getattr(user, "id", None) == worker.user_id for user in found):
            try:
                return cast(
                    Any,
                    utils.get_input_user(
                        await owner_client.get_input_entity(worker.user_id)
                    ),
                )
            except (ValueError, RPCError, TypeError):
                return None
    return None


async def worker_channel_peer(
    client: TelegramClient, channel_id: int, invite_link: str | None
) -> Any | None:
    """Resolve a worker's own input peer for a group it now belongs to."""
    try:
        return await client.get_input_entity(types.PeerChannel(channel_id))
    except (RPCError, ValueError, TypeError):
        pass
    if invite_link:
        try:
            checked = cast(
                Any,
                await client(
                    messages.CheckChatInviteRequest(parse_invite_hash(invite_link))
                ),
            )
            chat = getattr(checked, "chat", None)
            if chat is not None:
                return utils.get_input_peer(chat)
        except (RPCError, ValueError, TypeError):
            pass
    return None


async def worker_self_join(
    session: Session, invite_link: str, channel_id: int
) -> Any | None:
    """Last resort: worker joins via invite link. Never waits out a FloodWait."""
    client = session.client
    try:
        await client(messages.ImportChatInviteRequest(parse_invite_hash(invite_link)))
    except UserAlreadyParticipantError:
        pass
    except FloodWaitError as error:
        console.print(
            f"[yellow]{session.label}: invite-link join is rate-limited "
            f"({int(error.seconds)}s); skipping the join — the owner will add "
            f"it to later groups instead.[/yellow]"
        )
        return None
    except (InviteHashExpiredError, InviteHashInvalidError, RPCError, RuntimeError):
        return None
    return await worker_channel_peer(client, channel_id, invite_link)


async def invite_worker_via(
    inviter: Session, target: Session, source: Any, channel_id: int
) -> str:
    """Have one member (owner or an admin worker) add ``target`` to the group.

    Returns: "ok" if added/already in, "privacy" if the target blocks being
    added by anyone (self-join needed), or "busy" if this inviter can't do it
    right now (rate-limited or can't resolve) so another inviter should try.
    """
    client = inviter.client
    try:
        channel = cast(
            Any,
            utils.get_input_channel(
                await client.get_input_entity(types.PeerChannel(channel_id))
            ),
        )
    except (RPCError, ValueError, TypeError):
        return "busy"
    user = await resolve_worker_user(client, target, source)
    if user is None:
        return "busy"
    try:
        await client(channels.InviteToChannelRequest(channel=channel, users=[user]))
        return "ok"
    except UserAlreadyParticipantError:
        return "ok"
    except UserPrivacyRestrictedError:
        return "privacy"
    except (FloodWaitError, RPCError, RuntimeError):
        return "busy"


async def attach_worker_to_group(
    inviters: list[Session],
    worker: Session,
    source: Any,
    channel_id: int,
    invite_link: str | None,
) -> Any | None:
    """Get a worker into the destination group with minimal rate-limit risk.

    Tries the owner first, then any already-joined admin worker (they each
    have invite rights), so if one account is rate-limited on
    InviteToChannel the next one adds the worker. Only when no member can add
    it does the worker fall back to a self-join (which never blocks on a long
    FloodWait).
    """
    for inviter in inviters:
        outcome = await invite_worker_via(inviter, worker, source, channel_id)
        if outcome == "ok":
            peer = await worker_channel_peer(worker.client, channel_id, invite_link)
            if peer is not None:
                console.print(f"[dim]{worker.label} added by {inviter.label}[/dim]")
                return peer
        elif outcome == "privacy":
            # No member can add this account; only a self-join will work.
            break

    if invite_link:
        return await worker_self_join(worker, invite_link, channel_id)
    return None


async def create_private_group(
    client: TelegramClient,
    source_title: str,
) -> tuple[str, types.Channel]:
    title = backup_chat_title(source_title)
    created = cast(
        Any,
        await rpc_call(
            f"create {title}",
            lambda: client(
                channels.CreateChannelRequest(
                    title=title,
                    about=f"Video backup of {source_title}",
                    megagroup=True,
                )
            ),
            retry_server_errors=False,
        ),
    )
    destination = next(
        (chat for chat in created.chats if isinstance(chat, types.Channel)), None
    )
    if destination is None:
        raise RuntimeError("Telegram did not return the newly created private group.")
    return title, destination


async def export_private_group_link(
    client: TelegramClient,
    destination: Any,
) -> str:
    input_peer = await client.get_input_entity(destination)
    exported = cast(
        Any,
        await rpc_call(
            "export private group link",
            lambda: client(
                messages.ExportChatInviteRequest(
                    peer=input_peer,
                    title="HeartVault backup",
                )
            ),
        ),
    )
    link = getattr(exported, "link", None)
    if not isinstance(link, str) or not link:
        raise RuntimeError("Telegram did not return the private group invite link.")
    return link


def print_named_link(name: str, link: str, *, folder: bool = False) -> None:
    name_style = "bold bright_magenta" if folder else "bold"
    console.print(
        Text.assemble(
            (name, name_style),
            " : ",
            (link, "bold bright_cyan underline"),
        )
    )


def transfer_progress() -> Progress:
    return Progress(
        SpinnerColumn(style="bright_magenta"),
        TextColumn("[progress.description]{task.description}"),
        BarColumn(bar_width=24, complete_style="bright_magenta"),
        DownloadColumn(),
        TransferSpeedColumn(),
        TimeRemainingColumn(),
        console=console,
        transient=True,
    )


def connection_count(size: int) -> int:
    override = os.environ.get("HEARTVAULT_CONNECTIONS")
    if override and override.isdigit() and int(override) > 0:
        return min(MAX_TRANSFER_CONNECTIONS * 2, int(override))
    if size <= 0:
        return 1
    # Gentle by default (~1 connection per 25 MiB) to avoid tripping Telegram's
    # per-account throttle, which escalates into very long FloodWaits.
    scaled = math.ceil(size / (25 * 1024 * 1024))
    return max(1, min(MAX_TRANSFER_CONNECTIONS, scaled))


async def open_transfer_senders(
    client: TelegramClient, dc_id: int, count: int
) -> list[Any]:
    """Open several MTProto connections to ``dc_id`` for parallel transfer.

    Auth handling mirrors the well-known FastTelethon approach:
    - When ``dc_id`` is the client's own DC, reuse the existing auth key and
      never call ``ExportAuthorizationRequest`` (Telegram rejects exporting
      authorization for the DC you are already connected to).
    - For a foreign DC, export/import authorization once for the first
      connection, then share that authorized key with the rest.
    Senders are created one at a time because the first foreign export
    temporarily mutates the shared init request.
    """
    internal = cast(Any, client)
    dc = await client._get_dc(dc_id)
    same_dc = dc_id == int(cast(Any, client.session).dc_id)
    auth_key = cast(Any, client.session).auth_key if same_dc else None

    senders: list[Any] = []
    try:
        for _ in range(count):
            sender = MTProtoSender(auth_key, loggers=internal._log)
            await sender.connect(
                internal._connection(
                    dc.ip_address,
                    dc.port,
                    dc.id,
                    loggers=internal._log,
                    proxy=internal._proxy,
                    local_addr=internal._local_addr,
                )
            )
            if auth_key is None:
                # First connection to a foreign DC: authorize it, then reuse
                # the resulting key for every subsequent connection.
                exported = cast(Any, await client(ExportAuthorizationRequest(dc_id)))
                internal._init_request.query = ImportAuthorizationRequest(
                    id=exported.id, bytes=exported.bytes
                )
                await cast(
                    Any,
                    sender.send(InvokeWithLayerRequest(LAYER, internal._init_request)),
                )
                auth_key = sender.auth_key
            senders.append(sender)
    except Exception:
        await close_transfer_senders(senders)
        raise
    return senders


async def close_transfer_senders(senders: list[Any]) -> None:
    for sender in senders:
        try:
            await sender.disconnect()
        except Exception:
            pass


def video_size(message: types.Message) -> int:
    document = getattr(cast(Any, message), "document", None)
    return int(getattr(document, "size", 0) or 0)


def human_size(num_bytes: int) -> str:
    value = float(num_bytes)
    for unit in ("B", "KB", "MB", "GB"):
        if value < 1024 or unit == "GB":
            return f"{value:.1f} {unit}" if unit != "B" else f"{int(value)} B"
        value /= 1024
    return f"{value:.1f} GB"


def document_filename(document: Any, message_id: int) -> str:
    for attribute in getattr(document, "attributes", None) or []:
        name = getattr(attribute, "file_name", None)
        if name:
            return name
    return f"video_{message_id}.mp4"


async def call_part(
    client: TelegramClient, sender: Any, request: Any, label: str
) -> Any:
    """Invoke one file-part request, retrying transient timeouts and drops.

    The MTProto sender auto-reconnects, so re-issuing the same part request
    after a timeout succeeds without restarting the whole file.
    """
    attempt = 0
    while True:
        try:
            return await client._call(sender, request)
        except FloodWaitError as error:
            wait_for = max(1, int(error.seconds)) + 1
            if wait_for > MAX_FLOOD_WAIT:
                raise
            await asyncio.sleep(wait_for)
            continue
        except TRANSIENT_TRANSFER_ERRORS as error:
            last_error: Exception = error
        except ValueError as error:
            # Telethon raises this after its own internal retries give up
            # during a transient DC outage; treat it as retryable.
            if "Request was unsuccessful" not in str(error):
                raise
            last_error = error
        attempt += 1
        if attempt >= PART_RETRIES:
            raise last_error
        delay = min(2**attempt, 15)
        console.log(f"[dim]{escape(label)}: transient error, retry in {delay}s[/dim]")
        await asyncio.sleep(delay)


async def parallel_download(
    client: TelegramClient,
    document: Any,
    dest_path: Path,
    progress: Callable[[int, int], None],
) -> None:
    """Download one file over several connections, each fetching its own slice."""
    dc_id, location = utils.get_input_location(document)
    size = int(document.size)
    total_parts = math.ceil(size / PART_SIZE)
    count = min(connection_count(size), total_parts) or 1
    senders = await open_transfer_senders(client, dc_id, count)
    file_descriptor = os.open(dest_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    os.ftruncate(file_descriptor, size)
    done = 0
    lock = asyncio.Lock()

    async def worker(start: int, sender: Any) -> None:
        nonlocal done
        part = start
        while part < total_parts:
            offset = part * PART_SIZE
            result = await call_part(
                client,
                sender,
                GetFileRequest(location, offset=offset, limit=PART_SIZE),
                f"download part {part}",
            )
            chunk = getattr(result, "bytes", b"")
            if chunk:
                os.pwrite(file_descriptor, chunk, offset)
                async with lock:
                    done += len(chunk)
                    progress(done, size)
            part += count

    try:
        await asyncio.gather(
            *(worker(index, sender) for index, sender in enumerate(senders))
        )
    finally:
        os.close(file_descriptor)
        await close_transfer_senders(senders)


async def parallel_upload(
    client: TelegramClient,
    file_path: Path,
    size: int,
    name: str,
    progress: Callable[[int, int], None],
) -> types.InputFileBig:
    """Upload one file over several connections and return its big-file handle."""
    total_parts = math.ceil(size / PART_SIZE)
    count = min(connection_count(size), total_parts) or 1
    file_id = helpers.generate_random_long()
    senders = await open_transfer_senders(
        client, int(cast(Any, client.session).dc_id), count
    )
    file_descriptor = os.open(file_path, os.O_RDONLY)
    done = 0
    lock = asyncio.Lock()

    async def worker(start: int, sender: Any) -> None:
        nonlocal done
        part = start
        while part < total_parts:
            offset = part * PART_SIZE
            chunk = os.pread(file_descriptor, PART_SIZE, offset)
            await call_part(
                client,
                sender,
                SaveBigFilePartRequest(
                    file_id=file_id,
                    file_part=part,
                    file_total_parts=total_parts,
                    bytes=chunk,
                ),
                f"upload part {part}",
            )
            async with lock:
                done += len(chunk)
                progress(done, size)
            part += count

    try:
        await asyncio.gather(
            *(worker(index, sender) for index, sender in enumerate(senders))
        )
    finally:
        os.close(file_descriptor)
        await close_transfer_senders(senders)
    return types.InputFileBig(id=file_id, parts=total_parts, name=name)


async def copy_video(
    client: TelegramClient,
    source: types.Chat | types.Channel,
    destination: Any,
    message: types.Message,
    temp_dir: Path,
    progress_ui: bool = True,
) -> str:
    caption = video_caption(message.id)

    # Fast path: reuse Telegram's existing file reference so the server copies
    # the video by pointer. No bytes are downloaded or uploaded, so it is
    # near-instant and byte-for-byte identical to the original.
    try:
        await rpc_call(
            f"copy video #{message.id}",
            lambda: client.send_file(
                destination,
                file=cast(Any, message.media),
                caption=caption,
                supports_streaming=True,
            ),
            retry_server_errors=False,
        )
        return "linked"
    except (
        ChatForwardsRestrictedError,
        MediaEmptyError,
        FileReferenceExpiredError,
    ):
        # Protected or stale reference: fall back to a full re-download/upload.
        pass

    document = cast(Any, message).document
    if document is None:
        raise RuntimeError("The protected video message has no document to copy.")

    size = int(getattr(document, "size", 0) or 0)
    source_name = utils.get_display_name(source) or "source"
    file_name = document_filename(document, message.id)
    media_path = temp_dir / f"{message.id}_{file_name}"

    async def transfer(
        on_progress: Callable[[int, int], None],
        set_upload_phase: Callable[[int], None],
    ) -> None:
        nonlocal media_path
        if size > 0:
            await rpc_call(
                f"download video #{message.id}",
                lambda: parallel_download(client, document, media_path, on_progress),
                retry_server_errors=False,
            )
        else:
            downloaded = await rpc_call(
                f"download video #{message.id}",
                lambda: client.download_media(
                    message,
                    file=str(media_path),
                    progress_callback=on_progress,
                ),
            )
            if not downloaded or isinstance(downloaded, bytes):
                raise RuntimeError("Telegram returned no downloaded file path.")
            media_path = Path(downloaded)

        actual_size = media_path.stat().st_size
        set_upload_phase(actual_size)
        total_parts = math.ceil(actual_size / PART_SIZE) if actual_size else 0
        try:
            if 0 < actual_size and total_parts <= MAX_UPLOAD_PARTS:
                input_file = await rpc_call(
                    f"upload video #{message.id}",
                    lambda: parallel_upload(
                        client, media_path, actual_size, file_name, on_progress
                    ),
                    retry_server_errors=False,
                )
                # Streaming/duration/resolution are preserved by reusing the
                # source document's own attributes.
                media = types.InputMediaUploadedDocument(
                    file=input_file,
                    mime_type=document.mime_type or "video/mp4",
                    attributes=list(document.attributes),
                )
                await rpc_call(
                    f"send video #{message.id}",
                    lambda: client.send_file(destination, file=media, caption=caption),
                    retry_server_errors=False,
                )
            else:
                await rpc_call(
                    f"upload video #{message.id}",
                    lambda: client.send_file(
                        destination,
                        file=str(media_path),
                        caption=caption,
                        force_document=False,
                        supports_streaming=True,
                        progress_callback=on_progress,
                    ),
                    retry_server_errors=False,
                )
        finally:
            media_path.unlink(missing_ok=True)

    if progress_ui:
        with transfer_progress() as progress:
            task = progress.add_task(
                f"Download · {escape(source_name)} · #{message.id}",
                total=size or None,
            )

            def on_progress(current: int, total: int) -> None:
                progress.update(task, completed=current, total=total or None)

            def set_upload_phase(total: int) -> None:
                progress.reset(
                    task, description=f"Upload · #{message.id}", total=total or None
                )

            await transfer(on_progress, set_upload_phase)
    else:
        await transfer(lambda current, total: None, lambda total: None)
    return "reuploaded"


async def destination_video_ids(client: TelegramClient, destination: Any) -> set[int]:
    """Recover completed source IDs from captions already present remotely."""
    copied: set[int] = set()
    async for message in client.iter_messages(destination):
        caption = (message.raw_text or "").strip()
        match = re.fullmatch(r"ᴠɪᴅᴇᴏ\s*~\s*💗\s*(\d+)", caption)
        if match:
            copied.add(int(match.group(1)))
    return copied


async def backup_chat(
    pool: list[Session],
    source: types.Chat | types.Channel,
    index: int,
    total: int,
    temp_dir: Path,
    state: StateStore,
) -> BackupResult:
    client = pool[0].client
    source_title = utils.get_display_name(source) or f"Chat {utils.get_peer_id(source)}"
    source_key = str(utils.get_peer_id(source))
    brand = brand_key(source_title)
    target_title = backup_chat_title(source_title)
    console.rule(
        f"[bold bright_magenta]{index}/{total}[/bold bright_magenta] "
        f"[bold]{escape(source_title)}[/bold]"
    )

    # Reuse an existing group for the same brand (e.g. "chochlate qt" reuses
    # the group made for "chochlate haha"); otherwise create a new one.
    record = state.groups.get(brand)
    destination: Any | None = None
    if record:
        try:
            saved_destination = types.InputPeerChannel(
                channel_id=int(record["destination_id"]),
                access_hash=int(record["access_hash"]),
            )
            destination = saved_destination
            target_title = str(record.get("backup_title") or target_title)
            await rpc_call(
                "verify saved backup group",
                lambda: client.get_entity(saved_destination),
            )
            if source_key in record.get("sources", {}):
                console.print("[bright_cyan]Resuming saved private group[/bright_cyan]")
            else:
                console.print(
                    f"[bright_cyan]Matched existing group[/bright_cyan] "
                    f"[bold]{escape(target_title)}[/bold] — backing up into it"
                )
        except (KeyError, TypeError, ValueError, RPCError):
            console.print(
                "[yellow]Saved private group is unavailable; creating a new one.[/yellow]"
            )
            state.groups.pop(brand, None)
            state.save()
            record = None
            destination = None

    if destination is None:
        try:
            target_title, created = await create_private_group(client, source_title)
            if created.access_hash is None:
                raise RuntimeError("The new private group has no access hash.")
            destination = created
            record = {
                "backup_title": target_title,
                "destination_id": created.id,
                "access_hash": created.access_hash,
                "invite_link": None,
                "sources": {},
            }
            state.groups[brand] = record
            state.save()
        except (RPCError, RuntimeError) as error:
            console.print(
                f"[red]Could not create backup group:[/red] {escape(str(error))}"
            )
            return BackupResult(
                source_title=source_title,
                backup_title=target_title,
                destination=None,
                error=str(error),
            )

    if record is None:
        raise RuntimeError("Backup state was not initialized for the destination.")

    sources = record.setdefault("sources", {})
    source_record = sources.setdefault(
        source_key, {"title": source_title, "copied_message_ids": []}
    )
    state.save()

    result = BackupResult(
        source_title=source_title,
        backup_title=target_title,
        destination=destination,
        invite_link=record.get("invite_link"),
    )

    if not result.invite_link:
        try:
            result.invite_link = await export_private_group_link(client, destination)
            record["invite_link"] = result.invite_link
            state.save()
        except (RPCError, RuntimeError) as error:
            console.print(
                f"[yellow]Private group created, but its invite link could not be "
                f"exported: {escape(str(error))}[/yellow]"
            )
    if result.invite_link:
        print_named_link(target_title, result.invite_link)

    copied_ids = {
        int(message_id) for message_id in source_record.get("copied_message_ids", [])
    }
    # Caption-based recovery only makes sense when this group holds a single
    # source; merged groups mix message ids from different channels.
    if len(sources) == 1:
        try:
            remote_ids = await destination_video_ids(client, destination)
            if not remote_ids.issubset(copied_ids):
                copied_ids.update(remote_ids)
                source_record["copied_message_ids"] = sorted(copied_ids)
                state.save()
        except RPCError as error:
            console.print(
                f"[yellow]Could not reconcile remote captions; using the saved "
                f"checkpoint: {escape(str(error))}[/yellow]"
            )

    # Scan the source once (via main) to collect the pending, in-limit videos.
    pending: list[int] = []
    seen: set[int] = set()
    filters = (
        types.InputMessagesFilterVideo(),
        types.InputMessagesFilterRoundVideo(),
    )
    for media_filter in filters:
        try:
            async for message in client.iter_messages(
                source,
                reverse=True,
                filter=media_filter,
            ):
                if not message.video or message.id in copied_ids or message.id in seen:
                    continue
                seen.add(message.id)
                size = video_size(message)
                if size > MAX_VIDEO_BYTES:
                    result.skipped += 1
                    console.print(
                        f"  [yellow]⤼[/yellow] video [bold]#{message.id}[/bold] "
                        f"skipped ({human_size(size)} > 100 MB)"
                    )
                    continue
                pending.append(message.id)
        except RPCError as error:
            result.error = f"History scan failed: {error}"
            console.print(f"[red]{escape(result.error)}[/red]")

    # Build the active worker set for this chat: main plus any worker that can
    # both reach the source and post into this destination group.
    worker_entries: list[tuple[Session, Any, Any]] = []
    channel_id = int(record["destination_id"])
    owner = pool[0]
    # The owner plus every worker already in the group can add the next worker.
    inviters: list[Session] = [owner]
    for worker in pool[1:]:
        dest_peer = await attach_worker_to_group(
            inviters, worker, source, channel_id, result.invite_link
        )
        if dest_peer is None:
            continue
        try:
            source_peer = await worker.client.get_input_entity(to_peer(source))
        except (RPCError, ValueError, TypeError):
            continue
        worker_entries.append((worker, source_peer, dest_peer))
        # Promote right away so this worker can post and also help add the rest.
        await promote_workers(owner.client, destination, [worker])
        inviters.append(worker)

    # Report any worker that could not join this group, so it is clear why a
    # session is not posting here (rather than silently using fewer workers).
    attached_labels = {s.label for (s, _sp, _dp) in worker_entries}
    missing = [w.label for w in pool[1:] if w.label not in attached_labels]
    if missing:
        console.print(
            f"[yellow]Not posting here via: {', '.join(missing)} "
            f"(could not join this group this time)[/yellow]"
        )

    # The owner only creates the group, invites and promotes the workers. To
    # keep the owner account clean, the actual posting is done exclusively by
    # the workers; the owner posts only as a fallback when no worker is usable.
    now = time.monotonic()
    ready_workers = [
        entry for entry in worker_entries if entry[0].cooldown_until <= now
    ]
    cooling = [
        f"{s.label} (~{int(s.cooldown_until - now)}s)"
        for (s, _sp, _dp) in worker_entries
        if s.cooldown_until > now
    ]
    if cooling:
        console.print(
            f"[yellow]Cooling down (throttled): {', '.join(cooling)}[/yellow]"
        )
    if ready_workers:
        copy_pool = ready_workers
    elif worker_entries:
        wait = int(min(s.cooldown_until for (s, _sp, _dp) in worker_entries) - now)
        console.print(
            f"[yellow]All workers are cooling down (~{max(0, wait)}s); skipping "
            f"this chat for now — rerun later to finish it.[/yellow]"
        )
        copy_pool = []
    else:
        if pool[1:]:
            console.print(
                "[yellow]No worker could post here; the owner will post as "
                "a fallback.[/yellow]"
            )
        copy_pool = [(pool[0], source, destination)]

    if pending and copy_pool:
        posters = ", ".join(session.label for (session, _sp, _dp) in copy_pool)
        console.print(f"[dim]{len(pending)} video(s) · posting via {posters}[/dim]")
        await copy_videos_pooled(
            copy_pool,
            source,
            pending,
            temp_dir,
            copied_ids,
            source_record,
            state,
            result,
        )

    console.print(
        f"[bold]Finished:[/bold] {result.copied} new · "
        f"{len(copied_ids)} total · {result.skipped} skipped · "
        f"{result.failed} failed"
    )
    return result


async def copy_videos_pooled(
    active: list[tuple[Session, Any, Any]],
    source: types.Chat | types.Channel,
    pending: list[int],
    temp_dir: Path,
    copied_ids: set[int],
    source_record: dict[str, Any],
    state: StateStore,
    result: BackupResult,
) -> None:
    """Distribute the pending videos across every active session.

    Each session pulls the next video id from a shared queue and copies it
    end to end on its own connections, so N sessions give ~N times the
    throughput. Live progress bars are only shown when a single session is
    working (concurrent bars would collide), otherwise each line is tagged
    with the session that copied it.
    """
    queue: asyncio.Queue[int] = asyncio.Queue()
    for message_id in pending:
        queue.put_nowait(message_id)

    lock = asyncio.Lock()
    progress_ui = len(active) == 1

    async def consume(session: Session, source_peer: Any, dest_peer: Any) -> None:
        while True:
            try:
                message_id = queue.get_nowait()
            except asyncio.QueueEmpty:
                return
            try:
                message = cast(
                    Any,
                    await rpc_call(
                        f"{session.label}: fetch #{message_id}",
                        lambda: session.client.get_messages(
                            source_peer, ids=message_id
                        ),
                    ),
                )
                if message is None or not getattr(message, "video", None):
                    continue
                mode = await copy_video(
                    session.client,
                    source,
                    dest_peer,
                    message,
                    temp_dir,
                    progress_ui=progress_ui,
                )
                async with lock:
                    copied_ids.add(message_id)
                    source_record["copied_message_ids"] = sorted(copied_ids)
                    state.save()
                    result.copied += 1
                tag = "linked" if mode == "linked" else "re-uploaded"
                suffix = "" if progress_ui else f" [dim]· {session.label}[/dim]"
                console.print(
                    f"  [green]✓[/green] video [bold]#{message_id}[/bold] {tag}{suffix}"
                )
            except (FloodWaitError, FloodTooLongError) as error:
                # This account is throttled: pause it and hand the video back
                # to a healthy session instead of burning it as a failure.
                seconds = int(getattr(error, "seconds", MAX_FLOOD_WAIT))
                session.cooldown_until = time.monotonic() + seconds
                queue.put_nowait(message_id)
                console.print(
                    f"  [yellow]⏸ {session.label} throttled ~{seconds}s; pausing "
                    f"it and requeuing video #{message_id}[/yellow]"
                )
                return
            except Exception as error:
                # Never let one video stop the whole run; count it as failed so
                # it is retried on the next resumable run.
                async with lock:
                    result.failed += 1
                console.print(
                    f"  [red]✗[/red] video [bold]#{message_id}[/bold] failed "
                    f"({session.label}): {escape(str(error))}"
                )

    await asyncio.gather(*(consume(session, sp, dp) for (session, sp, dp) in active))


async def free_filter_id(client: TelegramClient) -> int:
    current = cast(
        Any,
        await rpc_call(
            "load Telegram folders",
            lambda: client(messages.GetDialogFiltersRequest()),
        ),
    )
    used = {getattr(item, "id", 0) for item in current.filters}
    for filter_id in range(2, 256):
        if filter_id not in used:
            return filter_id
    raise RuntimeError("No free Telegram folder slot is available.")


async def create_backup_folder(
    client: TelegramClient,
    source_folder_title: str,
    destinations: list[Any],
) -> tuple[str, str]:
    if not destinations:
        raise RuntimeError("No private backup groups were created.")

    folder_title = backup_folder_title(source_folder_title)
    folder_id = await free_filter_id(client)
    input_peers = [await client.get_input_entity(chat) for chat in destinations]
    dialog_filter = types.DialogFilterChatlist(
        id=folder_id,
        title=types.TextWithEntities(text=folder_title, entities=[]),
        pinned_peers=[],
        include_peers=input_peers,
    )

    await rpc_call(
        "create backup folder",
        lambda: client(
            messages.UpdateDialogFilterRequest(id=folder_id, filter=dialog_filter)
        ),
    )
    exported = cast(
        Any,
        await rpc_call(
            "export backup folder link",
            lambda: client(
                chatlists.ExportChatlistInviteRequest(
                    chatlist=types.InputChatlistDialogFilter(filter_id=folder_id),
                    title=f"{source_folder_title} backup"[:32],
                    peers=input_peers,
                )
            ),
            retry_server_errors=False,
        ),
    )
    link = getattr(getattr(exported, "invite", None), "url", None)
    if not isinstance(link, str) or not link:
        raise RuntimeError("Telegram created the folder but returned no share link.")
    return folder_title, link


def result_status(result: BackupResult) -> str:
    if result.destination is None:
        return "group failed"
    if not result.invite_link:
        return "link failed"
    if result.error:
        return "scan failed"
    if result.failed:
        return "media failed"
    return "complete"


def show_summary(results: list[BackupResult], folder_title: str, link: str) -> bool:
    complete = all(result_status(result) == "complete" for result in results)
    table = Table(
        title="Backup report",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("Source")
    table.add_column("Private backup")
    table.add_column("New", justify="right")
    table.add_column("Skipped", justify="right")
    table.add_column("Failed", justify="right")
    table.add_column("Status")
    for result in results:
        table.add_row(
            escape(result.source_title),
            escape(result.backup_title) if result.destination else "Not created",
            str(result.copied),
            str(result.skipped),
            str(result.failed),
            result_status(result),
        )
    console.print("\n", table)

    linked_results = [result for result in results if result.invite_link]
    if linked_results:
        console.print(
            "[bold bright_magenta]Private backup group links[/bold bright_magenta]"
        )
        for result in linked_results:
            print_named_link(result.backup_title, cast(str, result.invite_link))
        console.print()

    label = "BACKUP COMPLETE" if complete else "BACKUP PARTIAL"
    label_style = "bright_magenta" if complete else "yellow"
    console.print(
        Panel(
            Align.center(
                f"[bold {label_style}]{label} {HEART}[/bold {label_style}]\n"
                f"[bold]{escape(folder_title)}[/bold]"
            ),
            border_style=label_style,
            padding=(1, 3),
        )
    )
    print_named_link(folder_title, link, folder=True)
    return complete


def ask_links() -> str:
    """Read a pasted block of links, one per line, ended by an empty line."""
    console.print(
        "\n[bright_cyan]Paste link(s)[/bright_cyan] [dim]groups · channels · "
        "t.me/+invites · t.me/addlist folders — one per line, empty line to "
        "start[/dim]"
    )
    lines: list[str] = []
    while True:
        try:
            line = input()
        except EOFError:
            break
        if not line.strip():
            if lines:
                break
            continue
        lines.append(line.strip())
    return "\n".join(lines)


async def backup_sources(
    active_pool: list[Session],
    sources: Sequence[types.Chat | types.Channel],
    temp_dir: Path,
    state: StateStore,
    results: list[BackupResult],
) -> None:
    """Back up every source chat in order; one chat's failure is isolated."""
    total = len(sources)
    for index, source in enumerate(sources, start=1):
        try:
            result = await backup_chat(
                active_pool, source, index, total, temp_dir, state
            )
        except (OSError, RPCError, RuntimeError, ValueError) as error:
            title = utils.get_display_name(source) or "chat"
            console.print(
                f"[red]Chat '{escape(title)}' stopped: {escape(str(error))}[/red]"
            )
            result = BackupResult(
                source_title=title,
                backup_title=backup_chat_title(title),
                destination=None,
                error=str(error),
            )
        results.append(result)


async def queue_described_folders(
    client: TelegramClient,
    sources: Sequence[types.Chat | types.Channel],
    queue: list[Target],
    position: int,
    seen: set[str],
) -> int:
    """Follow shared-folder links advertised in a chat's description.

    Each folder found is inserted right after the link that mentioned it, so
    it is handled next: join it, back it up, drop the folder view, then carry
    on with the remaining pasted links.
    """
    added = 0
    for source in sources:
        about = await chat_description(client, source)
        for slug in folder_slugs_in_text(about):
            target = Target(
                "folder", slug, f"https://t.me/addlist/{slug}", origin="description"
            )
            if target.key in seen:
                continue
            seen.add(target.key)
            queue.insert(position + added, target)
            added += 1
            name = utils.get_display_name(source) or "chat"
            console.print(
                f"[bright_cyan]Folder link in {escape(name)}'s description:"
                f"[/bright_cyan] {escape(target.label)}"
            )
    return added


async def disconnect_client(client: TelegramClient) -> None:
    disconnect_result = cast(Any, client.disconnect())
    if inspect.isawaitable(disconnect_result):
        await disconnect_result


def _silence_shutdown_noise() -> None:
    """Hide benign asyncio warnings from transfer connections closing.

    The parallel-transfer senders and their background loops are torn down as
    the run winds down; Python then complains about GC'd pending tasks and
    ignored GeneratorExit. These are harmless, so we filter just those.
    """

    def loop_handler(loop: asyncio.AbstractEventLoop, context: dict[str, Any]) -> None:
        if "Task was destroyed but it is pending" in context.get("message", ""):
            return
        loop.default_exception_handler(context)

    with contextlib.suppress(RuntimeError):
        asyncio.get_running_loop().set_exception_handler(loop_handler)

    previous_hook = sys.unraisablehook

    def unraisable_hook(unraisable: Any) -> None:
        if isinstance(unraisable.exc_value, GeneratorExit):
            return
        previous_hook(unraisable)

    sys.unraisablehook = unraisable_hook


async def run() -> bool:
    banner()
    _silence_shutdown_noise()
    pool: list[Session] = []
    try:
        client, main_me, api_id, api_hash = await authenticate()
        pool.append(
            Session(
                client=client,
                label="main",
                user_id=int(main_me.id),
                name=utils.get_display_name(main_me) or "",
            )
        )

        worker_text = Prompt.ask(
            f"\n[bright_cyan]How many worker sessions to add "
            f"(0-{MAX_WORKERS})[/bright_cyan]",
            default="0",
        ).strip()
        worker_count = (
            min(MAX_WORKERS, int(worker_text)) if worker_text.isdigit() else 0
        )
        if worker_count:
            existing_ids = {s.user_id for s in pool}
            pool.extend(
                await authenticate_workers(api_id, api_hash, worker_count, existing_ids)
            )
            console.print(
                f"\n[green]{len(pool) - 1} distinct worker account(s) ready[/green]"
            )

        targets, rejected = parse_target_list(ask_links())
        for bad in rejected:
            console.print(f"[yellow]Not a Telegram chat link:[/yellow] {escape(bad)}")
        if not targets:
            raise ValueError("No usable Telegram chat or folder link was provided.")
        folders = sum(1 for target in targets if target.is_folder)
        console.print(
            f"[green]{len(targets)} link(s) queued[/green] "
            f"[dim]· {len(targets) - folders} chat · {folders} folder[/dim]"
        )

        state = StateStore()
        results: list[BackupResult] = []
        first_title: str | None = None
        seen_keys = {target.key for target in targets}
        with tempfile.TemporaryDirectory(prefix="heartvault-") as temp:
            temp_dir = Path(temp)
            position = 0
            # One link at a time: join it, back it up, then move to the next.
            # ``targets`` can grow while looping when a chat's description
            # points at a shared folder; that folder is handled next.
            while position < len(targets):
                target = targets[position]
                position += 1
                console.rule(
                    f"[bold bright_magenta]Link {position}/{len(targets)}"
                    f"[/bold bright_magenta] [bold]{escape(target.label)}[/bold]"
                )

                sources: list[types.Chat | types.Channel]
                active_pool: list[Session] = [pool[0]]
                if target.is_folder:
                    try:
                        imported = await import_shared_folder(client, target.value)
                    except (RPCError, RuntimeError, ValueError) as error:
                        console.print(
                            f"[red]Folder skipped:[/red] {escape(str(error))}"
                        )
                        continue
                    sources = list(imported.chats)
                    title = imported.title
                    # Workers must join the folder's chats to download them.
                    for worker in pool[1:]:
                        if await ensure_folder_joined(worker, target.value):
                            active_pool.append(worker)
                else:
                    try:
                        entity = await join_target_chat(client, target, "Main")
                    except (RPCError, RuntimeError, ValueError, TypeError) as error:
                        console.print(
                            f"[red]Skipped {escape(target.label)}:[/red] "
                            f"{escape(str(error))}"
                        )
                        continue
                    sources = [entity]
                    title = utils.get_display_name(entity) or target.label
                    console.print(f"[green]Joined:[/green] [bold]{escape(title)}[/bold]")
                    for worker in pool[1:]:
                        if await ensure_chat_joined(worker, target):
                            active_pool.append(worker)

                if first_title is None:
                    first_title = title
                if len(active_pool) > 1:
                    console.print(
                        f"[green]{len(active_pool)} sessions ready[/green] "
                        f"([bold]{', '.join(s.label for s in active_pool)}[/bold])"
                    )

                await backup_sources(active_pool, sources, temp_dir, state, results)

                if target.origin == "paste":
                    # Descriptions are only followed one level deep, so a
                    # followed folder cannot chain into further folders.
                    await queue_described_folders(
                        client, sources, targets, position, seen_keys
                    )
                console.print(f"[green]Done:[/green] {escape(target.label)}")

        if not results:
            raise RuntimeError("None of the pasted links could be opened.")

        # De-duplicate destinations: several sources may share one merged group.
        seen_channels: set[int] = set()
        destinations: list[Any] = []
        for result in results:
            channel = result.destination
            if channel is None:
                continue
            channel_id = int(getattr(channel, "channel_id", getattr(channel, "id", 0)))
            if channel_id in seen_channels:
                continue
            seen_channels.add(channel_id)
            destinations.append(channel)

        folder_title, link = await create_backup_folder(
            client,
            first_title or "backup",
            destinations,
        )
        return show_summary(results, folder_title, link)
    finally:
        for session in pool:
            await disconnect_client(session.client)


def main() -> None:
    try:
        complete = asyncio.run(run())
        if not complete:
            raise SystemExit(2)
    except KeyboardInterrupt:
        console.print(
            "\n[yellow]Cancelled. Progress was saved; rerun to resume.[/yellow]"
        )
    except (OSError, ValueError, RuntimeError, RPCError) as error:
        console.print(
            Panel(
                f"[bold red]Backup stopped[/bold red]\n{escape(str(error))}",
                border_style="red",
            )
        )
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
