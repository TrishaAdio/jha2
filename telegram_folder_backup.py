"""Interactive Telegram shared-folder video backup utility."""

from __future__ import annotations

import asyncio
import getpass
import inspect
import json
import math
import os
import re
import tempfile
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
MAX_FLOOD_WAIT = 15 * 60
# Only videos at or below this size are backed up; larger ones are skipped.
MAX_VIDEO_BYTES = 100 * 1024 * 1024
# 512 KiB parts evenly divide Telegram's 1 MiB block and satisfy the upload
# 512 KiB part limit, so the same size works for parallel download and upload.
PART_SIZE = 512 * 1024
MAX_UPLOAD_PARTS = 4000
# Extra connections opened per transfer. Each connection gets its own slice of
# the file, so throughput scales roughly linearly with this until bandwidth or
# Telegram throttling is the limit.
MAX_TRANSFER_CONNECTIONS = 8
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
                "[dim]Telegram folder video backup · original quality[/dim]"
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


def extract_folder_slug(raw_link: str) -> str:
    value = raw_link.strip()
    if not value:
        raise ValueError("The folder link cannot be empty.")

    if value.startswith("tg://"):
        parsed = urlparse(value)
        if parsed.netloc != "addlist":
            raise ValueError("This is not a Telegram shared-folder link.")
        slug = parse_qs(parsed.query).get("slug", [""])[0]
    else:
        if "://" not in value:
            value = f"https://{value}"
        parsed = urlparse(value)
        host = parsed.netloc.lower().removeprefix("www.")
        if host not in {"t.me", "telegram.me"}:
            raise ValueError("Use a t.me/addlist/... shared-folder link.")
        path_parts = [part for part in parsed.path.split("/") if part]
        if len(path_parts) != 2 or path_parts[0].lower() != "addlist":
            raise ValueError("Use a t.me/addlist/... shared-folder link.")
        slug = path_parts[1]

    if not re.fullmatch(r"[A-Za-z0-9_-]+", slug):
        raise ValueError("The shared-folder link has an invalid slug.")
    return slug


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
                raise RuntimeError(
                    f"Telegram requested a {wait_for}s wait during {label}; "
                    "progress is saved, so rerun later to resume."
                ) from error
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


async def authenticate_workers(api_id: int, api_hash: str, count: int) -> list[Session]:
    """Log in extra accounts that share the workload. They reuse the main
    application's API credentials; each just needs its own phone/OTP once,
    after which the session persists to disk."""
    workers: list[Session] = []
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
        await rpc_call(
            "join shared folder",
            lambda: client(
                chatlists.JoinChatlistInviteRequest(slug=slug, peers=input_peers)
            ),
        )
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
            input_peers, _ = await resolve_input_peers(
                client, checked.peers, checked.chats
            )
            if input_peers:
                await rpc_call(
                    f"{session.label}: join folder",
                    lambda: client(
                        chatlists.JoinChatlistInviteRequest(
                            slug=slug, peers=input_peers
                        )
                    ),
                )
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


async def attach_worker_to_group(
    owner_client: TelegramClient,
    worker: Session,
    source: Any,
    destination: Any,
    channel_id: int,
    invite_link: str | None,
) -> Any | None:
    """Get a worker into the destination group with minimal rate-limit risk.

    Preferred path: the owner (group creator) adds the worker as a member,
    which is not subject to the heavy invite-link join throttling. Only if the
    owner cannot resolve/add the worker does it fall back to a self-join, and
    that fallback never blocks on a long FloodWait.
    """
    channel: Any | None = None
    try:
        channel = cast(
            Any,
            utils.get_input_channel(await owner_client.get_input_entity(destination)),
        )
    except (RPCError, ValueError, TypeError):
        channel = None

    if channel is not None:
        user = await resolve_worker_user(owner_client, worker, source)
        if user is not None:
            added = False
            try:
                await rpc_call(
                    f"owner adds {worker.label}",
                    lambda: owner_client(
                        channels.InviteToChannelRequest(channel=channel, users=[user])
                    ),
                    retry_server_errors=False,
                )
                added = True
            except UserAlreadyParticipantError:
                added = True
            except (UserPrivacyRestrictedError, RPCError, RuntimeError) as error:
                console.print(
                    f"[yellow]Owner could not add {worker.label} "
                    f"({escape(str(error))}); trying self-join.[/yellow]"
                )
            if added:
                peer = await worker_channel_peer(worker.client, channel_id, invite_link)
                if peer is not None:
                    console.print(f"[dim]{worker.label} added by owner[/dim]")
                    return peer

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
    # Roughly one connection per 16 MiB, bounded to a safe range.
    scaled = math.ceil(size / (16 * 1024 * 1024))
    return max(2, min(MAX_TRANSFER_CONNECTIONS, scaled))


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
    owner_client = pool[0].client
    for worker in pool[1:]:
        dest_peer = await attach_worker_to_group(
            owner_client, worker, source, destination, channel_id, result.invite_link
        )
        if dest_peer is None:
            continue
        try:
            source_peer = await worker.client.get_input_entity(to_peer(source))
        except (RPCError, ValueError, TypeError):
            continue
        worker_entries.append((worker, source_peer, dest_peer))

    if worker_entries:
        await promote_workers(
            pool[0].client, destination, [s for (s, _sp, _dp) in worker_entries]
        )

    # The owner only creates the group, invites and promotes the workers. To
    # keep the owner account clean, the actual posting is done exclusively by
    # the workers; the owner posts only as a fallback when no worker is usable.
    if worker_entries:
        copy_pool = worker_entries
    else:
        if pool[1:]:
            console.print(
                "[yellow]No worker could post here; the owner will post as "
                "a fallback.[/yellow]"
            )
        copy_pool = [(pool[0], source, destination)]

    if pending:
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


async def disconnect_client(client: TelegramClient) -> None:
    disconnect_result = cast(Any, client.disconnect())
    if inspect.isawaitable(disconnect_result):
        await disconnect_result


async def run() -> bool:
    banner()
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
            "\n[bright_cyan]How many worker sessions to add (0-3)[/bright_cyan]",
            default="0",
        ).strip()
        worker_count = min(3, int(worker_text)) if worker_text.isdigit() else 0
        if worker_count:
            pool.extend(await authenticate_workers(api_id, api_hash, worker_count))

        raw_links = Prompt.ask(
            "\n[bright_cyan]Shared folder link(s) — separate several with a "
            "space or comma[/bright_cyan]"
        )
        slugs: list[str] = []
        for piece in re.split(r"[\s,]+", raw_links.strip()):
            if not piece:
                continue
            slug = extract_folder_slug(piece)
            if slug not in slugs:
                slugs.append(slug)
        if not slugs:
            raise ValueError("No shared folder link was provided.")

        state = StateStore()
        results: list[BackupResult] = []
        first_folder_title: str | None = None
        with tempfile.TemporaryDirectory(prefix="heartvault-") as temp:
            temp_dir = Path(temp)
            # Process each folder in turn: finish one, then move to the next.
            for folder_index, slug in enumerate(slugs, start=1):
                console.rule(
                    f"[bold bright_magenta]Folder {folder_index}/{len(slugs)}"
                    f"[/bold bright_magenta]"
                )
                imported = await import_shared_folder(client, slug)
                if first_folder_title is None:
                    first_folder_title = imported.title

                # Workers must join this folder's chats to download from them.
                active_pool: list[Session] = [pool[0]]
                for worker in pool[1:]:
                    if await ensure_folder_joined(worker, slug):
                        active_pool.append(worker)
                if len(active_pool) > 1:
                    console.print(
                        f"[green]{len(active_pool)} sessions ready[/green] "
                        f"([bold]{', '.join(s.label for s in active_pool)}[/bold])"
                    )

                for index, source in enumerate(imported.chats, start=1):
                    try:
                        result = await backup_chat(
                            active_pool,
                            source,
                            index,
                            len(imported.chats),
                            temp_dir,
                            state,
                        )
                    except (OSError, RPCError, RuntimeError, ValueError) as error:
                        # One chat's failure must not abort the whole backup.
                        title = utils.get_display_name(source) or "chat"
                        console.print(
                            f"[red]Chat '{escape(title)}' stopped: "
                            f"{escape(str(error))}[/red]"
                        )
                        result = BackupResult(
                            source_title=title,
                            backup_title=backup_chat_title(title),
                            destination=None,
                            error=str(error),
                        )
                    results.append(result)
                console.print(f"[green]Folder {folder_index} done[/green]")

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
            first_folder_title or "backup",
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
