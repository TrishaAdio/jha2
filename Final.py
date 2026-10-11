"""Final — anonymous, thumbnail-safe Telegram video backup userbot.

What this adds over its two siblings
------------------------------------
``telegram_folder_backup.py`` re-uploads bytes so it can beat "restrict saving
content"; ``qtrio.py`` forwards pointers for raw speed. Both leave four gaps
that this script closes:

anonymous workers
    Every worker is promoted with ``ChatAdminRights(anonymous=True)``, so
    Telegram signs their videos as the group itself. The account that uploaded
    a video is never shown, so a worker's identity and user id stay private.
locked-down members
    The moment a destination group exists, ``change_info`` and ``pin_messages``
    are taken away from normal members, so nobody but the owner can change the
    group photo (pfp), name or description. When a group's work is finished,
    every "send" right is revoked chat-wide, which freezes it as a read-only
    archive. Admins are exempt from default banned rights, so reruns still work.
visible thumbnails
    A re-uploaded document whose ``thumb`` is never set is exactly the blank
    grey preview Telegram shows, and the sibling scripts never set it. Here the
    source's own JPEG preview is carried over, a frame is generated with ffmpeg
    when the source itself has none, and every send is verified to have landed
    with a thumbnail (see ``copy_video``).
honest ETA
    Pointer copies are near-instant while re-uploads move every byte, so a
    plain "videos per second" estimate swings wildly. Progress is measured in
    *cost units* instead (one per video plus one per 8 MiB), which self-
    calibrates to whichever path the run is actually taking and yields both a
    time remaining and a wall-clock finish time.

Typography is Unicode MATHEMATICAL SANS-SERIF ITALIC (𝘢-𝘻, 𝘈-𝘡) rather than the
small caps the older scripts use. Message ids inside captions stay ASCII so the
resume scan cannot be confused by styling.

Run it, log in, pick up to ten groups from the list, and leave it alone.
"""

from __future__ import annotations

import asyncio
import getpass
import contextlib
import json
import logging
import math
import os
import re
import shutil
import tempfile
import time
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from types import TracebackType
from typing import Any, Callable, Iterable, Sequence, cast

from rich.align import Align
from rich.console import Group as RenderGroup
from rich.live import Live
from rich.markup import escape
from rich.panel import Panel
from rich.progress import (
    BarColumn,
    DownloadColumn,
    Progress,
    ProgressColumn,
    SpinnerColumn,
    Task,
    TaskID,
    TextColumn,
    TimeElapsedColumn,
    TransferSpeedColumn,
)
from rich.prompt import Prompt
from rich.table import Table
from rich.text import Text
from telethon import TelegramClient, helpers, types, utils
from telethon.errors import (
    AuthKeyUnregisteredError,
    ChannelInvalidError,
    ChannelPrivateError,
    ChatAdminRequiredError,
    ChatForwardsRestrictedError,
    ChatNotModifiedError,
    FileReferenceExpiredError,
    FloodWaitError,
    ChatSendMediaForbiddenError,
    ChatSendVideosForbiddenError,
    ChatWriteForbiddenError,
    MediaEmptyError,
    PeerFloodError,
    PeerIdInvalidError,
    RPCError,
    SessionRevokedError,
    UserAlreadyParticipantError,
    UserBannedInChannelError,
    UserChannelsTooMuchError,
    UserDeactivatedBanError,
    UserDeactivatedError,
    UserKickedError,
    UserNotMutualContactError,
    UserPrivacyRestrictedError,
)
from telethon.tl.functions import channels, chatlists, contacts, messages
from telethon.tl.functions.upload import GetFileRequest, SaveBigFilePartRequest

from telegram_folder_backup import (
    HEART,
    MAX_UPLOAD_PARTS,
    MAX_VIDEO_BYTES,
    PART_SIZE,
    TITLE_SUFFIX,
    FloodTooLongError,
    Session,
    _silence_shutdown_noise,
    ask_links,
    attach_worker_to_group,
    brand_key,
    call_part,
    canonical_source_name,
    close_transfer_senders,
    console,
    disconnect_client,
    document_filename,
    export_private_group_link,
    free_filter_id,
    human_size,
    import_shared_folder,
    join_target_chat,
    login_client,
    open_transfer_senders,
    pace_joins,
    parse_invite_hash,
    parse_target_list,
    print_named_link,
    resolve_worker_user,
    rpc_call,
    to_peer,
    video_size,
)

SESSION_FILE = "final"
STATE_FILE = ".final_state.json"
# The terminal menu refuses to start on more than this many groups per run.
MAX_GROUPS = 10
# Extra accounts that upload alongside the owner, each one anonymous. Upload
# throughput is metered per account, so the number of accounts is what sets the
# ceiling for a protected source whose bytes must be moved.
MAX_WORKERS = 30
# Telegram's own ceilings. Titles and ranks are measured in UTF-16 units
# because every italic-sans letter is a surrogate pair and so costs two.
TITLE_LIMIT = 128
FOLDER_TITLE_LIMIT = 12
# Telegram rejects a document thumbnail larger than this, so an oversized
# source preview is passed over in favour of a smaller one.
THUMB_MAX_BYTES = 200 * 1024
# Generated thumbnails are capped at this width; Telegram's own video previews
# are 320px, and a larger one only wastes an upload.
THUMB_WIDTH = 320
# Connections carrying one file, per direction. Telegram meters each *account*,
# not each socket, so this helps only up to a point: past it the same bandwidth
# is split more ways and Telegram starts throttling, which shows up as speeds
# that sag the longer a run goes. Four is a sane plateau; FINAL_CONNECTIONS can
# change it, but more worker accounts is what actually scales a run.
DEFAULT_CONNECTIONS = 4
MAX_CONNECTIONS = 16
# Upload sockets per account when the budget allows it.
MAX_UPLOAD_LANES = 6
# Telegram Premium removes the download speed limit, so the reading account can
# take far more download lanes than an ordinary one. Uploads stay modest per
# account because that allowance is still metered — the way to upload faster is
# more uploader accounts, not more sockets on one.
DEFAULT_READER_CONNECTIONS = 8
DEFAULT_PREMIUM_READER_CONNECTIONS = 16
# Total sockets this host opens to Telegram across every account. Past roughly
# this many, Telegram starts resetting connections instead of serving them, and
# each reset costs a retried part, so a bigger number transfers less. Divided
# between the reader and the uploaders at roster time.
DEFAULT_CONNECTION_BUDGET = 32
# In-flight requests per video, per direction. The pool is what actually bounds
# concurrency; this only decides how many tasks queue for it.
LANES_PER_VIDEO = 4
# Requests allowed in flight on one socket. Two lets the next request be on the
# wire while the previous reply is still coming back, which hides the round trip
# without needing another connection.
REQUEST_DEPTH = 2
# Videos one account copies at the same time. These share the account's
# connections rather than adding any, so raising it makes each video slower
# without making the run faster. One keeps the per-video ETA honest.
DEFAULT_PARALLEL_VIDEOS = 1
MAX_PARALLEL_VIDEOS = 4
# Telegram's ceiling for a single downloaded file part. Uploads are capped at
# PART_SIZE (512 KiB), so one download feeds exactly two uploads.
DOWNLOAD_PART = 1024 * 1024
# Message ids per forwardMessages call, which is Telegram's own cap. One call
# moves this many videos and no bytes at all, so a source that allows
# forwarding finishes in the time a handful of re-uploads would take.
FORWARD_BATCH = 100
FORWARD_INTERVAL = 1.0
# A worker that keeps failing is ejected after this many consecutive errors, so
# a broken account cannot drain the queue and fail every video in it.
MAX_CONSECUTIVE_FAILURES = 3
# With the "high" option, videos up to this size are copied too. 512 KiB parts
# and Telegram's 4000-part ceiling put the hard limit at 2 GB.
HIGH_VIDEO_BYTES = 2000 * 1024 * 1024
# ETA accounting: one cost unit per video plus one per this many bytes. The
# ratio only has to be in the right ballpark — the rate is measured live.
COST_BYTES = 8 * 1024 * 1024
# An estimate from a single sample is noise, so the ETA stays hidden until the
# run has some history behind it.
ETA_WARMUP_SECONDS = 4.0
# Videos are scanned server-side with these filters, so no history is walked.
MEDIA_FILTERS = (
    types.InputMessagesFilterVideo(),
    types.InputMessagesFilterRoundVideo(),
)

# ---------------------------------------------------------------------------
# Typography — MATHEMATICAL SANS-SERIF ITALIC
# ---------------------------------------------------------------------------
# U+1D608 'A', U+1D622 'a'. Unicode has no sans-serif *italic* digits, so the
# upright sans-serif digits at U+1D7E2 stand in; they sit together visually.
_ITALIC_UPPER = 0x1D608
_ITALIC_LOWER = 0x1D622
_SANS_DIGIT = 0x1D7E2


def italic_sans(value: str) -> str:
    """Restyle text as italic sans, after stripping any existing styling.

    ``canonical_source_name`` NFKD-folds the input first, so a name that is
    already decorated (bold, small caps, a previous run's italics) comes back
    as plain ASCII and is restyled once rather than layered.
    """
    styled: list[str] = []
    for character in canonical_source_name(value):
        code = ord(character)
        if 0x41 <= code <= 0x5A:
            styled.append(chr(_ITALIC_UPPER + code - 0x41))
        elif 0x61 <= code <= 0x7A:
            styled.append(chr(_ITALIC_LOWER + code - 0x61))
        elif 0x30 <= code <= 0x39:
            styled.append(chr(_SANS_DIGIT + code - 0x30))
        else:
            styled.append(character)
    return "".join(styled)


def _utf16_len(text: str) -> int:
    """Length as Telegram counts it: UTF-16 code units, not Python chars."""
    return len(text.encode("utf-16-le")) // 2


def _fit_utf16(text: str, limit: int) -> str:
    """Trim to ``limit`` UTF-16 units without splitting a surrogate pair."""
    if _utf16_len(text) <= limit:
        return text
    kept: list[str] = []
    used = 0
    for character in text:
        width = _utf16_len(character)
        if used + width > limit:
            break
        kept.append(character)
        used += width
    return "".join(kept).rstrip()


def group_title(source_title: str) -> str:
    """Destination group name: the source in italic sans, plus the brand mark."""
    styled = italic_sans(source_title) or italic_sans("untitled")
    room = TITLE_LIMIT - _utf16_len(TITLE_SUFFIX)
    return f"{_fit_utf16(styled, room)}{TITLE_SUFFIX}"


def folder_title(source_title: str) -> str:
    """Telegram folder names are capped at 12 UTF-16 units, so ~4 letters."""
    styled = italic_sans(source_title) or italic_sans("backup")
    room = FOLDER_TITLE_LIMIT - _utf16_len(f" {HEART}")
    fitted = _fit_utf16(styled, max(room, 0))
    return f"{fitted} {HEART}" if fitted else HEART


VIDEO_LABEL = italic_sans("video")


def video_caption(message_id: int) -> str:
    """``𝘷𝘪𝘥𝘦𝘰 ~ 💗 1234`` — the id stays ASCII so resume parsing is exact."""
    return f"{VIDEO_LABEL} ~ {HEART} {message_id}"


# Captions are NFKC-folded before matching, which turns italic-sans (and
# sans-serif digits) back into ASCII. The second pattern recognises groups made
# by telegram_folder_backup.py, whose phonetic small caps do *not* fold, so an
# existing backup group can still be resumed by this script.
CAPTION_PATTERNS = (
    re.compile(r"video\s*~\s*💗\s*(\d+)"),
    re.compile(r"ᴠɪᴅᴇᴏ\s*~\s*💗\s*(\d+)"),
)


def caption_message_id(caption: str) -> int | None:
    folded = unicodedata.normalize("NFKC", (caption or "").strip()).lower()
    for pattern in CAPTION_PATTERNS:
        match = pattern.fullmatch(folded)
        if match:
            return int(match.group(1))
    return None


def format_duration(seconds: float) -> str:
    whole = max(0, int(seconds))
    hours, rest = divmod(whole, 3600)
    minutes, secs = divmod(rest, 60)
    if hours:
        return f"{hours}h {minutes:02d}m"
    if minutes:
        return f"{minutes}m {secs:02d}s"
    return f"{secs}s"


# ---------------------------------------------------------------------------
# Accounts
# ---------------------------------------------------------------------------


@dataclass(slots=True)
class Worker(Session):
    """A logged-in account plus the per-run tally shown in the final report.

    Extends the shared :class:`Session` so every helper imported from
    ``telegram_folder_backup`` (invites, joins, cooldowns) keeps working.
    """

    copied: int = 0
    failed: int = 0
    anonymous: bool = False
    last_error: str = ""
    username: str = ""
    phone: str = ""
    premium: bool = False
    download_lanes: int = 0
    upload_lanes: int = 0
    transport: Any = None


def banner() -> None:
    console.print(
        Panel(
            Align.center(
                f"[bold bright_magenta]F I N A L[/bold bright_magenta]\n"
                f"[dim]anonymous video backup · thumbnails kept · "
                f"max {MAX_GROUPS} groups per run[/dim]"
            ),
            border_style="bright_magenta",
            padding=(1, 4),
        )
    )


async def authenticate() -> tuple[list[Worker], int, str]:
    """Log in the owner, then as many anonymous workers as requested."""
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

    console.print(
        "\n[bold bright_magenta]Owner account[/bold bright_magenta] "
        "[dim]· creates the groups and promotes the workers[/dim]"
    )
    owner_client, owner_me = await login_client(
        SESSION_FILE, api_id, api_hash, "Owner"
    )
    pool: list[Worker] = [
        Worker(
            client=owner_client,
            label="owner",
            user_id=int(owner_me.id),
            name=utils.get_display_name(owner_me) or "",
            username=getattr(owner_me, "username", None) or "",
            phone=getattr(owner_me, "phone", None) or "",
            premium=bool(getattr(owner_me, "premium", False)),
        )
    ]

    count_text = Prompt.ask(
        f"\n[bright_cyan]How many worker accounts (0-{MAX_WORKERS})[/bright_cyan]",
        default="0",
    ).strip()
    count = min(MAX_WORKERS, int(count_text)) if count_text.isdigit() else 0

    seen = {pool[0].user_id}
    for number in range(1, count + 1):
        console.print(
            f"\n[bold bright_magenta]Worker {number}[/bold bright_magenta] "
            f"[dim]· uploads anonymously[/dim]"
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
                f"[yellow]Worker {number} is an account already in this run; "
                f"skipping the duplicate.[/yellow]"
            )
            await disconnect_client(client)
            continue
        seen.add(int(me.id))
        pool.append(
            Worker(
                client=client,
                label=f"w{number}",
                user_id=int(me.id),
                name=utils.get_display_name(me) or "",
                username=getattr(me, "username", None) or "",
                phone=getattr(me, "phone", None) or "",
                premium=bool(getattr(me, "premium", False)),
            )
        )

    await introduce_accounts(pool)
    show_accounts(pool)
    return pool, api_id, api_hash


async def import_contacts(
    client: TelegramClient, targets: Sequence[Worker]
) -> set[int]:
    """Save accounts as contacts so ``client`` can address them by user id.

    Telegram only lets an account act on a user it has already met, because the
    access hash needed to name a user is different for every account. Two
    accounts that never shared a chat therefore cannot refer to each other, so
    the owner could not add a worker as a member. Saving the number as a
    contact introduces them. Returns the user ids Telegram matched.
    """
    entries = [
        types.InputPhoneContact(
            client_id=target.user_id,
            phone="+" + target.phone.lstrip("+"),
            first_name=f"Final {target.label}",
            last_name="",
        )
        for target in targets
        if target.phone
    ]
    if not entries:
        return set()
    try:
        imported = cast(
            Any,
            await rpc_call(
                "save accounts as contacts",
                lambda: client(contacts.ImportContactsRequest(entries)),
                retry_server_errors=False,
            ),
        )
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        console.print(
            f"[yellow]Could not save accounts as contacts: "
            f"{escape(str(error))}[/yellow]"
        )
        return set()
    return {int(user.id) for user in getattr(imported, "users", None) or []}


async def introduce_accounts(pool: Sequence[Worker]) -> None:
    """Make the owner and every worker known to each other, once, at login.

    The owner saves each worker (needed so it can add them as members), and each
    worker saves the owner (so they are mutual contacts, which some privacy
    settings require before someone may be added to a group). These are the
    user's own accounts; the contact entries are named ``Final <label>``.
    """
    if len(pool) < 2:
        return
    owner, workers = pool[0], list(pool[1:])
    missing = [w.label for w in workers if not w.phone]
    if missing:
        console.print(
            f"[yellow]No phone number known for {', '.join(missing)}; the owner "
            f"cannot add those as members unless they share a chat.[/yellow]"
        )
    matched = await import_contacts(owner.client, workers)
    for worker in workers:
        if worker.phone and worker.user_id not in matched:
            console.print(
                f"[yellow]Telegram did not match {worker.label}'s number, so the "
                f"owner may not be able to add it as a member.[/yellow]"
            )
    for worker in workers:
        await import_contacts(worker.client, [owner])
    console.print(
        f"[dim]{len(matched)}/{len(workers)} worker(s) saved as contacts of the "
        f"owner[/dim]"
    )


def show_accounts(pool: Sequence[Worker]) -> None:
    """Print the signed-in accounts with their user ids.

    The ids are shown here, locally, precisely because they will not appear
    anywhere in Telegram once the workers are promoted anonymously.
    """
    table = Table(
        title=f"Signed-in accounts ({len(pool)})",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("Label")
    table.add_column("Name")
    table.add_column("User id", justify="right")
    table.add_column("Premium")
    table.add_column("Role")
    for session in pool:
        table.add_row(
            session.label,
            escape(session.name or "—"),
            str(session.user_id),
            "yes" if session.premium else "—",
            "owner" if session.label == "owner" else "worker",
        )
    console.print(table)


# ---------------------------------------------------------------------------
# State
# ---------------------------------------------------------------------------


class FinalState:
    """Brand-keyed checkpoints, so a rerun resumes instead of duplicating.

    Keyed by ``brand_key`` exactly like the sibling scripts, so sibling sources
    ("chochlate qt", "chochlate 18+") share one destination group, and copied
    ids are tracked per source inside it.
    """

    def __init__(self) -> None:
        self.path = Path(__file__).resolve().parent / STATE_FILE
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            self.data: dict[str, Any] = raw if isinstance(raw, dict) else {}
        except FileNotFoundError:
            self.data = {}
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"Could not read backup state: {error}") from error
        self.groups: dict[str, dict[str, Any]] = self.data.setdefault("groups", {})
        # Cached video inventory per source, so a rerun does not rescan the
        # whole history just to learn what it already knew.
        self.scans: dict[str, dict[str, Any]] = self.data.setdefault("scans", {})
        self._lock = asyncio.Lock()

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

    def source_record(self, brand: str, source_key: str, title: str) -> dict[str, Any]:
        group = self.groups.setdefault(brand, {})
        sources = group.setdefault("sources", {})
        return sources.setdefault(source_key, {"title": title, "copied": []})

    def copied_ids(self, brand: str, source_key: str) -> set[int]:
        group = self.groups.get(brand) or {}
        record = (group.get("sources") or {}).get(source_key) or {}
        return {int(value) for value in record.get("copied", [])}

    def channel_ids(self) -> set[int]:
        """Channels this tool made, so they never show up as sources."""
        found: set[int] = set()
        for group in self.groups.values():
            try:
                found.add(int(group["channel_id"]))
            except (KeyError, TypeError, ValueError):
                continue
        return found

    async def remember_group(self, brand: str, values: dict[str, Any]) -> None:
        async with self._lock:
            group = self.groups.setdefault(brand, {})
            group.update(values)
            group.setdefault("sources", {})
            self.save()

    async def mark_copied(
        self, brand: str, source_key: str, title: str, message_id: int
    ) -> None:
        async with self._lock:
            record = self.source_record(brand, source_key, title)
            copied = {int(value) for value in record.get("copied", [])}
            copied.add(int(message_id))
            record["copied"] = sorted(copied)
            record["title"] = title
            self.save()

    async def save_scan(
        self,
        source_key: str,
        title: str,
        max_id: int,
        normal: dict[int, int],
        big: dict[int, int],
        oversize: dict[int, int],
    ) -> None:
        async with self._lock:
            self.scans[source_key] = {
                "title": title,
                "max_id": int(max_id),
                "normal": {str(mid): int(size) for mid, size in normal.items()},
                "big": {str(mid): int(size) for mid, size in big.items()},
                "oversize": {
                    str(mid): int(size) for mid, size in oversize.items()
                },
            }
            self.save()

    async def forget_group(self, brand: str) -> None:
        async with self._lock:
            self.groups.pop(brand, None)
            self.save()


# ---------------------------------------------------------------------------
# ETA
# ---------------------------------------------------------------------------


def work_cost(size: int) -> float:
    """Rough effort for one video: a fixed per-message cost plus its bytes.

    A pointer copy moves no bytes and costs ~1; a 400 MB re-upload costs ~51.
    Because the rate is measured from real completions, a run that is mostly
    pointer copies and a run that is mostly re-uploads both converge instead of
    one of them reporting a wildly wrong ETA.
    """
    return 1.0 + max(0, size) / COST_BYTES


class Eta:
    """Cost-weighted progress, time remaining, and a wall-clock finish time."""

    def __init__(self) -> None:
        self.total_cost = 0.0
        self.done_cost = 0.0
        self.total_videos = 0
        self.done_videos = 0
        self.started = time.monotonic()

    def plan(self, sizes: Iterable[int]) -> None:
        for size in sizes:
            self.total_cost += work_cost(size)
            self.total_videos += 1

    def reset_clock(self) -> None:
        """Start timing when the first byte moves, not during login."""
        self.started = time.monotonic()

    def complete(self, size: int) -> None:
        self.done_cost += work_cost(size)
        self.done_videos += 1

    def drop(self, size: int) -> None:
        """Take work that will not happen (failed/skipped) out of the estimate."""
        self.total_cost = max(self.done_cost, self.total_cost - work_cost(size))
        self.total_videos = max(self.done_videos, self.total_videos - 1)

    def drop_many(self, sizes: Iterable[int]) -> None:
        for size in sizes:
            self.drop(size)

    @property
    def elapsed(self) -> float:
        return time.monotonic() - self.started

    def snapshot(self) -> tuple[float | None, datetime | None]:
        elapsed = self.elapsed
        if self.done_cost <= 0 or elapsed < ETA_WARMUP_SECONDS:
            return None, None
        rate = self.done_cost / elapsed
        if rate <= 0:
            return None, None
        remaining = max(0.0, self.total_cost - self.done_cost) / rate
        return remaining, datetime.now() + timedelta(seconds=remaining)


class EtaColumn(ProgressColumn):
    """Renders ``eta 12m 30s · done ~18:42`` next to the overall bar."""

    def __init__(self, eta: Eta) -> None:
        super().__init__()
        self.eta = eta

    def render(self, task: Task) -> Text:
        remaining, finish = self.eta.snapshot()
        if remaining is None or finish is None:
            return Text("eta estimating…", style="dim")
        clock = finish.strftime("%H:%M")
        if finish.date() != datetime.now().date():
            clock = finish.strftime("%d %b %H:%M")
        return Text(
            f"eta {format_duration(remaining)} · done ~{clock}", style="bright_cyan"
        )


class Dashboard:
    """One live region: an overall bar with the ETA, plus a bar per worker."""

    def __init__(self, eta: Eta, label: str = "backing up") -> None:
        self.eta = eta
        self.overall = Progress(
            SpinnerColumn(style="bright_magenta"),
            TextColumn("[bold bright_magenta]{task.description}"),
            BarColumn(bar_width=28, complete_style="bright_magenta"),
            TextColumn("[bold]{task.completed}/{task.total}[/bold] videos"),
            TimeElapsedColumn(),
            EtaColumn(eta),
            console=console,
        )
        self.transfer = Progress(
            TextColumn("  [dim]{task.description}"),
            BarColumn(bar_width=18, complete_style="bright_cyan"),
            DownloadColumn(),
            TransferSpeedColumn(),
            console=console,
        )
        self.live = Live(
            RenderGroup(self.overall, self.transfer),
            console=console,
            refresh_per_second=8,
        )
        self.task = self.overall.add_task(label, total=eta.total_videos or 1)

    def __enter__(self) -> Dashboard:
        self.live.__enter__()
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        self.live.__exit__(exc_type, exc, traceback)

    def advance(self) -> None:
        self.overall.update(self.task, completed=self.eta.done_videos)

    def retotal(self) -> None:
        self.overall.update(
            self.task,
            total=max(1, self.eta.total_videos),
            completed=self.eta.done_videos,
        )

    def lane(self, label: str) -> TaskID:
        return self.transfer.add_task(f"{label} idle", total=None, start=False)


# ---------------------------------------------------------------------------
# Choosing sources
# ---------------------------------------------------------------------------


@dataclass(slots=True)
class Candidate:
    entity: types.Chat | types.Channel
    title: str
    kind: str
    known: bool


def is_own_output(title: str, channel_id: int, made: set[int]) -> bool:
    """True for a group this project produced, so a run never eats its own tail."""
    if channel_id in made:
        return True
    return title.rstrip().endswith(TITLE_SUFFIX.strip())


async def fetch_candidates(
    client: TelegramClient, state: FinalState
) -> list[Candidate]:
    made = state.channel_ids()
    found: list[Candidate] = []
    seen: set[int] = set()
    console.print("[dim]Reading your chat list…[/dim]")
    async for dialog in client.iter_dialogs():
        entity = dialog.entity
        if not isinstance(entity, (types.Chat, types.Channel)):
            continue
        if getattr(entity, "deactivated", False) or isinstance(
            entity, types.ChannelForbidden
        ):
            continue
        peer_id = utils.get_peer_id(entity)
        if peer_id in seen:
            continue
        title = utils.get_display_name(entity) or f"Chat {peer_id}"
        if is_own_output(title, int(getattr(entity, "id", 0)), made):
            continue
        seen.add(peer_id)
        kind = (
            "channel"
            if isinstance(entity, types.Channel) and not entity.megagroup
            else "group"
        )
        found.append(
            Candidate(
                entity=entity,
                title=title,
                kind=kind,
                known=brand_key(title) in state.groups,
            )
        )
    return found


def show_candidates(candidates: Sequence[Candidate]) -> None:
    table = Table(
        title=f"Your groups and channels ({len(candidates)})",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("#", justify="right")
    table.add_column("Title")
    table.add_column("Kind")
    table.add_column("Backed up before")
    for number, candidate in enumerate(candidates, start=1):
        table.add_row(
            str(number),
            escape(candidate.title),
            candidate.kind,
            "yes" if candidate.known else "—",
        )
    console.print(table)


def parse_selection(raw: str, count: int, limit: int) -> list[int]:
    """Turn ``1,4,7-12`` into zero-based indexes, order kept, deduplicated.

    ``all`` is deliberately *not* accepted as a shortcut past the limit: with
    more than ``limit`` chats on offer it raises, so a 200-group account cannot
    accidentally start a 200-group run.
    """
    cleaned = raw.strip().lower()
    if cleaned in {"all", "*"}:
        if count > limit:
            raise ValueError(
                f"'all' would be {count} groups; this run allows at most {limit}. "
                f"Pick them explicitly, for example 1-{limit}."
            )
        return list(range(count))
    if not cleaned:
        raise ValueError("Nothing was selected.")

    chosen: list[int] = []
    for piece in re.split(r"[\s,]+", cleaned):
        if not piece:
            continue
        match = re.fullmatch(r"(\d+)(?:-(\d+))?", piece)
        if not match:
            raise ValueError(f"'{piece}' is not a number or a range like 4-9.")
        start = int(match.group(1))
        end = int(match.group(2) or start)
        if start < 1 or end > count or end < start:
            raise ValueError(f"'{piece}' is outside 1-{count}.")
        chosen.extend(range(start - 1, end))

    ordered: list[int] = []
    seen: set[int] = set()
    for index in chosen:
        if index not in seen:
            seen.add(index)
            ordered.append(index)
    if not ordered:
        raise ValueError("Nothing was selected.")
    if len(ordered) > limit:
        raise ValueError(
            f"{len(ordered)} groups selected; this run allows at most {limit}."
        )
    return ordered


async def choose_sources(
    client: TelegramClient, state: FinalState
) -> list[types.Chat | types.Channel]:
    """Pick up to ``MAX_GROUPS`` chats from the owner's own list, or by link."""
    console.print("\n[bold bright_magenta]Sources[/bold bright_magenta]")
    try:
        candidates = await fetch_candidates(client, state)
    except (RPCError, RuntimeError) as error:
        console.print(
            f"[yellow]Could not read your chat list ({escape(str(error))}); "
            f"paste links instead.[/yellow]"
        )
        return await sources_from_links(client)
    if not candidates:
        console.print("[yellow]No group or channel found in this account.[/yellow]")
        return await sources_from_links(client)

    show_candidates(candidates)
    while True:
        raw = Prompt.ask(
            f"[bright_cyan]Which groups[/bright_cyan] [dim]· up to {MAX_GROUPS} · "
            f"e.g. 1,4,7-9 · 'links' to paste links instead[/dim]",
            default="1",
        ).strip()
        if raw.lower() in {"links", "link", "paste"}:
            return await sources_from_links(client)
        try:
            picked = parse_selection(raw, len(candidates), MAX_GROUPS)
        except ValueError as error:
            console.print(f"[yellow]{escape(str(error))}[/yellow]")
            continue
        chosen = [candidates[index] for index in picked]
        console.print(
            f"[green]{len(chosen)} group(s) selected:[/green] "
            + ", ".join(f"[bold]{escape(item.title)}[/bold]" for item in chosen)
        )
        return [item.entity for item in chosen]


async def sources_from_links(
    client: TelegramClient,
) -> list[types.Chat | types.Channel]:
    """Fallback path: paste links, join them, and cap the result at the limit."""
    targets, rejected = parse_target_list(ask_links())
    for bad in rejected:
        console.print(f"[yellow]Not a Telegram chat link:[/yellow] {escape(bad)}")
    if not targets:
        raise ValueError("No usable Telegram chat or folder link was provided.")

    sources: list[types.Chat | types.Channel] = []
    seen: set[int] = set()
    for position, target in enumerate(targets, start=1):
        console.rule(
            f"[bold bright_magenta]Link {position}/{len(targets)}"
            f"[/bold bright_magenta] [bold]{escape(target.label)}[/bold]"
        )
        try:
            if target.is_folder:
                imported = await import_shared_folder(client, target.value)
                found: list[types.Chat | types.Channel] = list(imported.chats)
            else:
                entity = await join_target_chat(client, target, "Owner")
                found = [entity]
                console.print(
                    f"[green]Joined:[/green] "
                    f"[bold]{escape(utils.get_display_name(entity) or '')}[/bold]"
                )
        except (RPCError, RuntimeError, ValueError, TypeError) as error:
            console.print(
                f"[red]Skipped {escape(target.label)}:[/red] {escape(str(error))}"
            )
            continue
        for chat in found:
            peer_id = utils.get_peer_id(chat)
            if peer_id in seen:
                continue
            seen.add(peer_id)
            sources.append(chat)
            if len(sources) >= MAX_GROUPS:
                console.print(
                    f"[yellow]Reached the {MAX_GROUPS}-group limit; the rest of "
                    f"the links are left for the next run.[/yellow]"
                )
                return sources
    if not sources:
        raise RuntimeError("None of the pasted links could be opened.")
    return sources


# ---------------------------------------------------------------------------
# Planning
# ---------------------------------------------------------------------------


@dataclass(slots=True)
class Plan:
    """One source chat and the videos still to copy out of it."""

    source: types.Chat | types.Channel
    title: str
    key: str
    brand: str
    pending: list[tuple[int, int]] = field(default_factory=list)
    # Over the normal size limit, held back for the optional second pass.
    big: list[tuple[int, int]] = field(default_factory=list)
    # Past even the "high" limit, so re-uploading them is not possible. They
    # are still kept, because forwarding has no size limit and can take them.
    oversize: list[tuple[int, int]] = field(default_factory=list)
    already: int = 0
    cached: bool = False
    error: str | None = None

    @property
    def huge(self) -> int:
        return len(self.oversize)

    @property
    def everything(self) -> list[tuple[int, int]]:
        """Every outstanding video, whatever its size.

        Only meaningful for forwarding: it moves no bytes, so a 2 GB video is
        no more expensive than a small one and nothing needs holding back.
        """
        return sorted({*self.pending, *self.big, *self.oversize})

    @property
    def pending_bytes(self) -> int:
        return sum(size for _id, size in self.pending)

    @property
    def big_bytes(self) -> int:
        return sum(size for _id, size in self.big)


async def build_plan(
    client: TelegramClient,
    source: types.Chat | types.Channel,
    state: FinalState,
) -> Plan:
    """Work out what is left to copy, scanning only what is new.

    The first run walks the source's whole video history, which for thousands
    of videos is slow. That result is cached, so later runs ask Telegram only
    for messages newer than the highest id already seen and the scan finishes
    almost immediately. The cached ids are kept separately from the copied ones,
    so a video that is known but not yet copied is still picked up.
    """
    title = utils.get_display_name(source) or f"Chat {utils.get_peer_id(source)}"
    key = str(utils.get_peer_id(source))
    brand = brand_key(title)
    plan = Plan(source=source, title=title, key=key, brand=brand)
    copied = state.copied_ids(brand, key)
    plan.already = len(copied)

    record = state.scans.get(key) or {}
    normal: dict[int, int] = {
        int(mid): int(size) for mid, size in (record.get("normal") or {}).items()
    }
    big: dict[int, int] = {
        int(mid): int(size) for mid, size in (record.get("big") or {}).items()
    }
    oversize: dict[int, int] = {
        int(mid): int(size) for mid, size in (record.get("oversize") or {}).items()
    }
    last_id = int(record.get("max_id") or 0)
    plan.cached = bool(record)

    highest = last_id
    complete = True
    for media_filter in MEDIA_FILTERS:
        try:
            async for message in client.iter_messages(
                source, reverse=True, filter=media_filter, min_id=last_id
            ):
                highest = max(highest, int(message.id))
                if not getattr(message, "video", None):
                    continue
                if (
                    message.id in normal
                    or message.id in big
                    or message.id in oversize
                ):
                    continue
                size = video_size(message)
                if size > HIGH_VIDEO_BYTES:
                    oversize[message.id] = size
                elif size > MAX_VIDEO_BYTES:
                    big[message.id] = size
                else:
                    normal[message.id] = size
        except (RPCError, RuntimeError, ValueError) as error:
            plan.error = f"Scan failed: {error}"
            complete = False
            console.print(f"[red]{escape(plan.title)}: {escape(plan.error)}[/red]")
            break

    # Only advance the watermark when the pass actually finished, otherwise a
    # half-read history would be treated as fully known on the next run.
    await state.save_scan(
        key,
        title,
        highest if complete else last_id,
        normal,
        big,
        oversize,
    )

    plan.pending = sorted(
        (mid, size) for mid, size in normal.items() if mid not in copied
    )
    plan.big = sorted((mid, size) for mid, size in big.items() if mid not in copied)
    plan.oversize = sorted(
        (mid, size) for mid, size in oversize.items() if mid not in copied
    )
    return plan


def show_plan(plans: Sequence[Plan]) -> None:
    table = Table(
        title="Work queued",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("Source")
    table.add_column("Backup group")
    table.add_column("New", justify="right")
    table.add_column("Size", justify="right")
    table.add_column("Done before", justify="right")
    table.add_column("Oversized", justify="right")
    table.add_column("Scan")
    for plan in plans:
        oversized = f"{len(plan.big)}" if plan.big else "—"
        if plan.huge:
            oversized = f"{oversized} (+{plan.huge} too big)"
        table.add_row(
            escape(plan.title),
            escape(group_title(plan.title)),
            str(len(plan.pending)),
            human_size(plan.pending_bytes),
            str(plan.already),
            oversized,
            "cached" if plan.cached else "full",
        )
    console.print(table)


# ---------------------------------------------------------------------------
# Destination groups: creation, member lockdown, anonymous promotion
# ---------------------------------------------------------------------------
# Telethon's ChatBannedRights is a list of things members may NOT do, so every
# flag set to True *removes* that ability. Admins are exempt from the chat
# default, which is why the workers keep posting after a group is frozen.


def member_rights(*, allow_sending: bool) -> types.ChatBannedRights:
    """Default rights for normal members.

    ``change_info`` is always revoked, which is what stops a member renaming
    the group or replacing its photo; ``pin_messages`` goes with it. Once a
    group's work is finished, every "send" flag is revoked too, leaving a
    read-only archive. ``invite_users`` is deliberately left alone so the
    invite link keeps working.
    """
    restricted = not allow_sending
    return types.ChatBannedRights(
        until_date=None,
        change_info=True,
        pin_messages=True,
        send_messages=restricted,
        send_media=restricted,
        send_plain=restricted,
        send_photos=restricted,
        send_videos=restricted,
        send_roundvideos=restricted,
        send_audios=restricted,
        send_voices=restricted,
        send_docs=restricted,
        send_stickers=restricted,
        send_gifs=restricted,
        send_games=restricted,
        send_inline=restricted,
        send_polls=restricted,
        embed_links=restricted,
    )


async def apply_member_rights(
    client: TelegramClient, destination: Any, *, allow_sending: bool, label: str
) -> bool:
    try:
        peer = await client.get_input_entity(destination)
        await rpc_call(
            label,
            lambda: client(
                messages.EditChatDefaultBannedRightsRequest(
                    peer=peer, banned_rights=member_rights(allow_sending=allow_sending)
                )
            ),
            retry_server_errors=False,
        )
        return True
    except ChatNotModifiedError:
        # Telegram says this when the rights are already what was asked for,
        # which is the normal case for a reused group. That is success.
        return True
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        console.print(f"[yellow]{label} failed: {escape(str(error))}[/yellow]")
        return False


# Workers need to post, tidy up and pull the next worker in — nothing more.
# change_info is withheld on purpose: only the owner may rename the group or
# change its photo. anonymous=True is the whole point: Telegram then signs
# their videos as the group, so the uploading account is never revealed.
WORKER_RIGHTS = types.ChatAdminRights(
    change_info=False,
    post_messages=False,
    edit_messages=False,
    delete_messages=True,
    ban_users=False,
    invite_users=True,
    pin_messages=True,
    add_admins=False,
    anonymous=True,
    manage_call=False,
)

OWNER_RIGHTS = types.ChatAdminRights(
    change_info=True,
    post_messages=False,
    edit_messages=False,
    delete_messages=True,
    ban_users=True,
    invite_users=True,
    pin_messages=True,
    add_admins=True,
    anonymous=True,
    manage_call=True,
)


async def promote_anonymous(
    owner_client: TelegramClient, destination: Any, worker: Worker
) -> bool:
    """Make one worker an anonymous admin of the destination group.

    An empty rank is used rather than a label like "worker": for an anonymous
    admin Telegram shows the rank beside the group name, and a blank one leaks
    the least.
    """
    try:
        channel = cast(
            Any,
            utils.get_input_channel(await owner_client.get_input_entity(destination)),
        )
    except (RPCError, ValueError, TypeError) as error:
        worker.last_error = f"promote: {error}"
        return False
    try:
        user = cast(
            Any,
            utils.get_input_user(await owner_client.get_input_entity(worker.user_id)),
        )
    except (RPCError, ValueError, TypeError) as error:
        worker.last_error = f"promote: {error}"
        console.print(f"[yellow]Could not resolve {worker.label} to promote[/yellow]")
        return False
    try:
        await rpc_call(
            f"promote {worker.label}",
            lambda: owner_client(
                channels.EditAdminRequest(
                    channel=channel,
                    user_id=user,
                    admin_rights=WORKER_RIGHTS,
                    rank="",
                )
            ),
            retry_server_errors=False,
        )
        worker.anonymous = True
        return True
    except (RPCError, RuntimeError) as error:
        worker.last_error = f"promote: {error}"
        console.print(
            f"[yellow]Could not promote {worker.label}: {escape(str(error))}[/yellow]"
        )
        return False


_owner_anonymous_warned = False


async def make_owner_anonymous(owner: Worker, destination: Any) -> None:
    """Best-effort: hide the owner too, for the runs where it posts directly.

    Telegram does not always let a group's creator rewrite its own admin row,
    so this is attempted and then dropped. It only matters when no worker can
    serve a group and the owner uploads as the fallback; the warning is printed
    once per run rather than once per group.
    """
    global _owner_anonymous_warned
    try:
        channel = cast(
            Any,
            utils.get_input_channel(await owner.client.get_input_entity(destination)),
        )
        await rpc_call(
            "hide owner",
            lambda: owner.client(
                channels.EditAdminRequest(
                    channel=channel,
                    user_id=types.InputUserSelf(),
                    admin_rights=OWNER_RIGHTS,
                    rank="",
                )
            ),
            retry_server_errors=False,
        )
        owner.anonymous = True
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        if not _owner_anonymous_warned:
            _owner_anonymous_warned = True
            console.print(
                f"[yellow]The owner account could not be made anonymous "
                f"({escape(str(error))}). Workers are still anonymous; the owner "
                f"is only visible if it has to post a video itself.[/yellow]"
            )


async def create_group(client: TelegramClient, source_title: str) -> types.Channel:
    title = group_title(source_title)
    created = cast(
        Any,
        await rpc_call(
            f"create {title}",
            lambda: client(
                channels.CreateChannelRequest(
                    title=title,
                    about=f"Video backup of {canonical_source_name(source_title)}",
                    megagroup=True,
                )
            ),
            retry_server_errors=False,
        ),
    )
    channel = next(
        (chat for chat in created.chats if isinstance(chat, types.Channel)), None
    )
    if channel is None:
        raise RuntimeError("Telegram did not return the newly created group.")
    if channel.access_hash is None:
        raise RuntimeError("The new group came back without an access hash.")
    return channel


async def destination_copied_ids(
    client: TelegramClient, destination: Any
) -> set[int]:
    """Recover finished ids from the captions already in a reused group."""
    found: set[int] = set()
    async for message in client.iter_messages(destination):
        message_id = caption_message_id(message.raw_text or "")
        if message_id is not None:
            found.add(message_id)
    return found


# ---------------------------------------------------------------------------
# Getting workers into the source chats
# ---------------------------------------------------------------------------


async def source_entry_link(
    owner_client: TelegramClient, source: types.Chat | types.Channel
) -> str | None:
    """A link a worker can use to reach this source: @username, else an invite."""
    username = getattr(source, "username", None)
    if username:
        return f"https://t.me/{username}"
    try:
        peer = await owner_client.get_input_entity(source)
        exported = cast(
            Any,
            await rpc_call(
                "export source link",
                lambda: owner_client(
                    messages.ExportChatInviteRequest(peer=peer, title="Final backup")
                ),
                retry_server_errors=False,
            ),
        )
    except (RPCError, RuntimeError, ValueError, TypeError):
        return None
    link = getattr(exported, "link", None)
    return link if isinstance(link, str) and link else None


def _short(error: BaseException) -> str:
    """One-line reason for the console, without Telethon's request dump."""
    text = str(error).strip().splitlines()[0] if str(error).strip() else ""
    return f"{type(error).__name__}: {text}"[:110]


async def can_read_source(
    client: TelegramClient, peer: Any, probe_ids: Sequence[int]
) -> bool:
    """True if this account can actually fetch history from the source.

    Having the chat in the session cache or being listed as a member is not
    enough: a private group can hide older history from newly added members, and
    a worker that cannot see a video would fetch ``None`` and the run would
    mistake it for a deleted message. Several ids are tried because any single
    one may genuinely have been deleted since the scan.
    """
    for message_id in probe_ids[:3]:
        try:
            if await client.get_messages(peer, ids=message_id) is not None:
                return True
        except (RPCError, ValueError, TypeError):
            return False
    return False


async def resolve_worker_user_for_owner(
    owner: Worker, worker: Worker, source: types.Chat | types.Channel
) -> Any | None:
    """InputUser the owner can act on, via cache, source search, then @username."""
    user = await resolve_worker_user(owner.client, worker, source)
    if user is not None:
        return user
    if worker.username:
        try:
            return cast(
                Any,
                utils.get_input_user(
                    await owner.client.get_input_entity(worker.username)
                ),
            )
        except (RPCError, ValueError, TypeError):
            pass
    # Last resort: save the worker's number as a contact, which introduces it.
    if worker.phone and worker.user_id in await import_contacts(
        owner.client, [worker]
    ):
        try:
            return cast(
                Any,
                utils.get_input_user(
                    await owner.client.get_input_entity(worker.user_id)
                ),
            )
        except (RPCError, ValueError, TypeError):
            return None
    return None


async def owner_adds_worker(
    owner: Worker, worker: Worker, source: types.Chat | types.Channel
) -> str | None:
    """Add a worker to the source with the owner's "add member" right.

    Returns ``None`` on success, otherwise the reason it did not work. Telegram
    reports a user who blocks being added in ``missing_invitees`` instead of
    raising, so that field is checked; trusting the absence of an exception
    would report success for an add that silently did nothing.
    """
    user = await resolve_worker_user_for_owner(owner, worker, source)
    if user is None:
        return "owner cannot find this worker (no shared chat, @username or phone)"
    try:
        if isinstance(source, types.Channel):
            channel = cast(Any, utils.get_input_channel(source))
            invited = cast(
                Any,
                await rpc_call(
                    f"owner adds {worker.label}",
                    lambda: owner.client(
                        channels.InviteToChannelRequest(
                            channel=channel, users=[user]
                        )
                    ),
                    retry_server_errors=False,
                ),
            )
            if getattr(invited, "missing_invitees", None):
                return "worker's privacy settings block being added"
        else:
            await rpc_call(
                f"owner adds {worker.label}",
                lambda: owner.client(
                    messages.AddChatUserRequest(
                        chat_id=source.id, user_id=user, fwd_limit=100
                    )
                ),
                retry_server_errors=False,
            )
    except UserAlreadyParticipantError:
        return None
    except UserPrivacyRestrictedError:
        return "worker's privacy settings block being added"
    except UserNotMutualContactError:
        return "worker must be a mutual contact of the owner to be added"
    except ChatAdminRequiredError:
        return "owner is not allowed to add members to this source"
    except UserBannedInChannelError:
        return "worker is banned from this source"
    except UserKickedError:
        return "worker was removed from this source and cannot be re-added"
    except UserChannelsTooMuchError:
        return "worker is already in too many groups and channels"
    except PeerFloodError:
        return "owner is limited by Telegram from adding members right now"
    except (FloodWaitError, FloodTooLongError) as error:
        seconds = int(getattr(error, "seconds", 0))
        return f"owner's add-member is rate-limited ({seconds}s)"
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        return _short(error)
    return None


async def worker_peer_after_add(
    worker: Worker, source: types.Chat | types.Channel
) -> Any | None:
    """Find the worker's own handle on a source it was just added to.

    A freshly added account has no access hash for the chat in its session, so
    it is resolved by @username when there is one, otherwise by reading the
    newest dialogs, where the "you were added" service message puts the chat.
    """
    try:
        return await worker.client.get_input_entity(to_peer(source))
    except (RPCError, ValueError, TypeError):
        pass
    username = getattr(source, "username", None)
    if username:
        try:
            return await worker.client.get_input_entity(username)
        except (RPCError, ValueError, TypeError):
            pass
    wanted = utils.get_peer_id(source)
    try:
        async for dialog in worker.client.iter_dialogs(limit=100):
            if utils.get_peer_id(dialog.entity) == wanted:
                return await worker.client.get_input_entity(dialog.entity)
    except (RPCError, ValueError, TypeError):
        pass
    return None


async def worker_source_peer(
    owner: Worker,
    worker: Worker,
    source: types.Chat | types.Channel,
    entry_link: str | None,
    probe_ids: Sequence[int],
) -> Any | None:
    """Get a worker reading the source, trying the cheapest route first.

    1. It may already have access (verified by actually reading a video).
    2. It joins itself through the link.
    3. If that fails, the owner adds it with the "add member" option.

    Every failure is printed with its reason, so a worker that sits a source out
    is never a silent surprise. Access hashes are per-account, so the owner's
    handle is useless to a worker and each one resolves the source itself.
    """
    name = escape(utils.get_display_name(source) or "source")

    try:
        existing = await worker.client.get_input_entity(to_peer(source))
    except (RPCError, ValueError, TypeError):
        existing = None
    if existing is not None and await can_read_source(
        worker.client, existing, probe_ids
    ):
        return existing

    join_reason = "no link available to join with"
    if entry_link:
        await pace_joins()
        try:
            if "/+" in entry_link or "/joinchat/" in entry_link:
                await worker.client(
                    messages.ImportChatInviteRequest(parse_invite_hash(entry_link))
                )
            else:
                username = entry_link.rstrip("/").rsplit("/", 1)[-1]
                entity = await worker.client.get_entity(username)
                if isinstance(entity, types.Channel):
                    await worker.client(
                        channels.JoinChannelRequest(
                            cast(Any, utils.get_input_channel(entity))
                        )
                    )
            join_reason = ""
        except UserAlreadyParticipantError:
            join_reason = ""
        except FloodWaitError as error:
            join_reason = f"join rate-limited ({int(error.seconds)}s)"
        except (RPCError, RuntimeError, ValueError, TypeError) as error:
            join_reason = _short(error)

        if not join_reason:
            peer = await worker_peer_after_add(worker, source)
            if peer is not None and await can_read_source(
                worker.client, peer, probe_ids
            ):
                return peer
            join_reason = "joined but cannot read the history"

    console.print(
        f"[yellow]{worker.label} could not join '{name}' itself "
        f"({escape(join_reason)}); {owner.label} will add it as a member.[/yellow]"
    )
    reason = await owner_adds_worker(owner, worker, source)
    if reason is None:
        peer = await worker_peer_after_add(worker, source)
        if peer is not None and await can_read_source(
            worker.client, peer, probe_ids
        ):
            console.print(
                f"[green]{owner.label} added {worker.label} to '{name}'[/green]"
            )
            return peer
        reason = (
            "added, but it cannot read the history "
            "(is history hidden from new members?)"
        )

    worker.last_error = f"source: {reason}"[:120]
    console.print(
        f"[yellow]{worker.label} sits out '{name}': {escape(reason)}[/yellow]"
    )
    return None


# ---------------------------------------------------------------------------
# Transfer layer
# ---------------------------------------------------------------------------
# Throughput on Telegram is set by how many connections carry a file, not by
# how fast the link is: one connection tops out near ~1 MB/s however much
# bandwidth is spare. The sibling scripts open at most 4 (one per 25 MiB), so a
# 4 Gbps host still crawls at ~4 MB/s. Here the count is set by FINAL_CONNECTIONS
# and the connections are opened once per account and reused for every video,
# so no video pays for an MTProto handshake.


def connection_budget() -> int:
    """Total sockets to Telegram. Override with FINAL_TOTAL_CONNECTIONS."""
    raw = os.environ.get("FINAL_TOTAL_CONNECTIONS", "")
    if raw.isdigit() and int(raw) > 0:
        return max(4, int(raw))
    return DEFAULT_CONNECTION_BUDGET


def allocate_lanes(
    downloaders: Sequence[Worker], uploaders: Sequence[Worker]
) -> None:
    """Split the socket budget across the accounts that will actually use it.

    Opening sockets per account without regard to how many accounts there are
    is what produced the connection resets: eight accounts at the old defaults
    asked for 44 at once. Uploads are metered per account, so a couple of lanes
    each is already near that account's ceiling; the rest goes to whichever
    accounts are downloading, shared out between them.
    """
    budget = connection_budget()
    upload_count = max(1, len(uploaders))
    # Uploads are metered per account, so they need the larger share; a Premium
    # downloader is not metered and delivers more per socket.
    share = 2 if any(session.premium for session in downloaders) else 1
    upload_budget = budget * share // (share + 1)
    per_upload = max(2, min(MAX_UPLOAD_LANES, upload_budget // upload_count))
    for session in uploaders:
        session.upload_lanes = per_upload
    left = max(4, budget - per_upload * upload_count)
    download_count = max(1, len(downloaders))
    per_download = max(2, left // download_count)
    for session in downloaders:
        session.download_lanes = min(reader_connections(session), per_download)


def reader_connections(session: Worker) -> int:
    """Download lanes for an account. Premium has no speed cap, so it gets more.

    Override with FINAL_DOWNLOAD_CONNECTIONS.
    """
    raw = os.environ.get("FINAL_DOWNLOAD_CONNECTIONS", "")
    if raw.isdigit() and int(raw) > 0:
        return max(1, min(MAX_CONNECTIONS, int(raw)))
    if session.premium:
        return DEFAULT_PREMIUM_READER_CONNECTIONS
    return DEFAULT_READER_CONNECTIONS


class ConnectionNoise(logging.Filter):
    """Collapse Telethon's connection churn into a count.

    With many transfer sockets open, Telegram drops some and Telethon
    reconnects; a reply already in flight then arrives against the old session
    and is discarded as a security error. ``call_part`` retries the part, so
    none of it is a failure the user can act on, but one log line per event
    buried the actual progress. They are counted and reported once instead.
    """

    PATTERNS = (
        "wrong session ID",
        "Security error while unpacking",
        "Server closed the connection",
        "Connection reset by peer",
        "Broken pipe",
        "Connection to Telegram failed",
    )

    def __init__(self) -> None:
        super().__init__()
        self.count = 0

    def filter(self, record: logging.LogRecord) -> bool:
        try:
            message = record.getMessage()
        except Exception:  # noqa: BLE001 - a bad log record must not stop a run
            return True
        if any(pattern in message for pattern in self.PATTERNS):
            self.count += 1
            return False
        return True


CONNECTION_NOISE = ConnectionNoise()


def quiet_connection_noise() -> None:
    logging.getLogger("telethon").addFilter(CONNECTION_NOISE)


def transfer_connections() -> int:
    """Connections per file. Override with FINAL_CONNECTIONS."""
    raw = os.environ.get("FINAL_CONNECTIONS", "")
    if raw.isdigit() and int(raw) > 0:
        return max(1, min(MAX_CONNECTIONS, int(raw)))
    return DEFAULT_CONNECTIONS


def _sender_pool(senders: Sequence[Any]) -> asyncio.Queue[Any]:
    """Checkout queue holding each socket ``REQUEST_DEPTH`` times."""
    pool: asyncio.Queue[Any] = asyncio.Queue()
    for _ in range(REQUEST_DEPTH):
        for sender in senders:
            pool.put_nowait(sender)
    return pool


class Transport:
    """One account's reusable MTProto connections.

    Senders are opened on first use and kept for the whole run: a batch of
    thousands of videos would otherwise spend most of its time on handshakes.
    Download senders are keyed by the source's data centre, and uploads always
    go to the account's own one.
    """

    def __init__(
        self, client: TelegramClient, download_count: int, upload_count: int
    ) -> None:
        self.client = client
        self.download_count = download_count
        self.upload_count = upload_count
        self._download: dict[int, list[Any]] = {}
        self._upload: list[Any] | None = None
        self._guard = asyncio.Lock()
        # Sockets are checked out of a queue rather than picked by a counter, so
        # two requests in flight always hold two different sockets. A shared
        # counter with a modulo could hand both to the same one and leave the
        # rest idle, which silently halved upload concurrency.
        self._download_pool: dict[int, asyncio.Queue[Any]] = {}
        self._upload_pool: asyncio.Queue[Any] | None = None

    async def download_senders(self, dc_id: int) -> list[Any]:
        async with self._guard:
            senders = self._download.get(dc_id)
            if senders is None:
                senders = await open_transfer_senders(
                    self.client, dc_id, self.download_count
                )
                self._download[dc_id] = senders
                self._download_pool[dc_id] = _sender_pool(senders)
            return senders

    async def upload_senders(self) -> list[Any]:
        async with self._guard:
            if self._upload is None:
                own_dc = int(cast(Any, self.client.session).dc_id)
                self._upload = await open_transfer_senders(
                    self.client, own_dc, self.upload_count
                )
                self._upload_pool = _sender_pool(self._upload)
            return self._upload

    async def fetch(self, dc_id: int, request: Any, label: str) -> Any:
        """Run one download request on a socket checked out of the pool."""
        await self.download_senders(dc_id)
        pool = self._download_pool[dc_id]
        sender = await pool.get()
        try:
            return await call_part(self.client, sender, request, label)
        finally:
            pool.put_nowait(sender)

    async def push(self, request: Any, label: str) -> Any:
        """Run one upload request on a socket checked out of the pool."""
        await self.upload_senders()
        pool = self._upload_pool
        assert pool is not None
        sender = await pool.get()
        try:
            return await call_part(self.client, sender, request, label)
        finally:
            pool.put_nowait(sender)

    async def close(self) -> None:
        for senders in self._download.values():
            await close_transfer_senders(senders)
        self._download.clear()
        self._download_pool.clear()
        if self._upload is not None:
            await close_transfer_senders(self._upload)
            self._upload = None
        self._upload_pool = None


async def worker_transport(session: Worker) -> Transport:
    """This account's connection pool, opened on first use."""
    if session.transport is None:
        session.transport = Transport(
            session.client,
            session.download_lanes or reader_connections(session),
            session.upload_lanes or transfer_connections(),
        )
    return cast(Transport, session.transport)


async def close_transports(pool: Sequence[Worker]) -> None:
    """Shut the pooled connections down before the clients disconnect."""
    for session in pool:
        if session.transport is not None:
            with contextlib.suppress(Exception):
                await session.transport.close()
            session.transport = None


async def relay_copy(
    reader: Worker,
    uploader: Worker,
    document: Any,
    name: str,
    size: int,
    progress: Callable[[int], None],
) -> types.InputFileBig:
    """Download on one account and upload on another, via this host's memory.

    ``upload.saveBigFilePart`` carries nothing but raw bytes: no peer, no file
    reference, nothing tied to where the data came from. So the account doing
    the uploading needs no access whatsoever to the source chat, and the
    account reading the source never has to post. That is what lets a Premium
    account, whose download speed is unmetered, feed several ordinary accounts
    that each upload under their own allowance.

    The ``file_id`` belongs to the uploader's session, so every part of one
    video has to come from that same uploader; different videos go to different
    uploaders instead.

    Fetching and pushing are independent and meet at a bounded queue, so both
    run at once and a fast reader cannot buffer a whole file ahead of a slower
    uploader.
    """
    dc_id, location = utils.get_input_location(document)
    total_up = math.ceil(size / PART_SIZE)
    total_down = math.ceil(size / DOWNLOAD_PART)
    if total_up > MAX_UPLOAD_PARTS:
        raise RuntimeError(
            f"{human_size(size)} needs {total_up} parts, over Telegram's "
            f"{MAX_UPLOAD_PARTS} limit."
        )
    file_id = helpers.generate_random_long()
    read_transport = await worker_transport(reader)
    send_transport = await worker_transport(uploader)
    fetchers = min(LANES_PER_VIDEO, total_down) or 1
    pushers = min(LANES_PER_VIDEO, total_up) or 1
    per_download = DOWNLOAD_PART // PART_SIZE
    queue: asyncio.Queue[tuple[int, bytes] | None] = asyncio.Queue(
        maxsize=max(4, pushers * 2)
    )
    moved = 0
    guard = asyncio.Lock()

    async def fetch(start: int) -> None:
        index = start
        while index < total_down:
            offset = index * DOWNLOAD_PART
            fetched = await read_transport.fetch(
                dc_id,
                GetFileRequest(location, offset=offset, limit=DOWNLOAD_PART),
                f"{reader.label} down {index}",
            )
            data = getattr(fetched, "bytes", b"")
            if not data:
                raise RuntimeError(
                    f"Telegram returned no data at {offset} of {name}."
                )
            base = index * per_download
            for cursor in range(0, len(data), PART_SIZE):
                await queue.put(
                    (base + cursor // PART_SIZE, data[cursor : cursor + PART_SIZE])
                )
            index += fetchers

    async def push() -> None:
        nonlocal moved
        while True:
            item = await queue.get()
            if item is None:
                return
            part, data = item
            await send_transport.push(
                SaveBigFilePartRequest(
                    file_id=file_id,
                    file_part=part,
                    file_total_parts=total_up,
                    bytes=data,
                ),
                f"{uploader.label} up {part}",
            )
            async with guard:
                moved += len(data)
                progress(moved)

    fetch_tasks = [asyncio.create_task(fetch(index)) for index in range(fetchers)]
    push_tasks = [asyncio.create_task(push()) for _ in range(pushers)]
    try:
        await asyncio.gather(*fetch_tasks)
        # Every byte is queued, so release the pushers once they have drained it.
        for _ in push_tasks:
            await queue.put(None)
        await asyncio.gather(*push_tasks)
    except BaseException:
        for task in (*fetch_tasks, *push_tasks):
            task.cancel()
        await asyncio.gather(*fetch_tasks, *push_tasks, return_exceptions=True)
        raise
    return types.InputFileBig(id=file_id, parts=total_up, name=name)


async def pooled_download(
    transport: Transport,
    document: Any,
    dest_path: Path,
    size: int,
    progress: Callable[[int], None],
) -> None:
    """Download to disk over the pooled connections.

    Only needed when a thumbnail has to be generated from the video itself,
    since ffmpeg needs a real file to read a frame out of.
    """
    dc_id, location = utils.get_input_location(document)
    # 1 MiB is Telegram's ceiling for one part, so this is half the round trips
    # of a 512 KiB read.
    total_parts = math.ceil(size / DOWNLOAD_PART)
    lanes = min(LANES_PER_VIDEO, total_parts) or 1
    handle = os.open(dest_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    os.ftruncate(handle, size)
    done = 0
    guard = asyncio.Lock()

    async def pipeline(start: int) -> None:
        nonlocal done
        part = start
        while part < total_parts:
            offset = part * DOWNLOAD_PART
            fetched = await transport.fetch(
                dc_id,
                GetFileRequest(location, offset=offset, limit=DOWNLOAD_PART),
                f"download part {part}",
            )
            chunk = getattr(fetched, "bytes", b"")
            if chunk:
                os.pwrite(handle, chunk, offset)
                async with guard:
                    done += len(chunk)
                    progress(done)
            part += lanes

    try:
        await asyncio.gather(*(pipeline(index) for index in range(lanes)))
    finally:
        os.close(handle)


async def pooled_upload(
    transport: Transport,
    file_path: Path,
    size: int,
    name: str,
    progress: Callable[[int], None],
) -> types.InputFileBig:
    """Upload a local file over the pooled connections."""
    total_parts = math.ceil(size / PART_SIZE)
    if total_parts > MAX_UPLOAD_PARTS:
        raise RuntimeError(
            f"{human_size(size)} needs {total_parts} parts, over Telegram's "
            f"{MAX_UPLOAD_PARTS} limit."
        )
    file_id = helpers.generate_random_long()
    lanes = min(LANES_PER_VIDEO, total_parts) or 1
    handle = os.open(file_path, os.O_RDONLY)
    done = 0
    guard = asyncio.Lock()

    async def pipeline(start: int) -> None:
        nonlocal done
        part = start
        while part < total_parts:
            offset = part * PART_SIZE
            chunk = os.pread(handle, PART_SIZE, offset)
            if not chunk:
                break
            await transport.push(
                SaveBigFilePartRequest(
                    file_id=file_id,
                    file_part=part,
                    file_total_parts=total_parts,
                    bytes=chunk,
                ),
                f"upload part {part}",
            )
            async with guard:
                done += len(chunk)
                progress(done)
            part += lanes

    try:
        await asyncio.gather(*(pipeline(index) for index in range(lanes)))
    finally:
        os.close(handle)
    return types.InputFileBig(id=file_id, parts=total_parts, name=name)


# ---------------------------------------------------------------------------
# Thumbnails
# ---------------------------------------------------------------------------
# A document re-uploaded with no `thumb` is the blank grey preview, so the
# source's own JPEG is carried across; when the source has none either, a frame
# is cut with ffmpeg if it is installed.


def _thumb_rank(thumb: Any) -> tuple[int, int]:
    """Prefer a real downloadable JPEG, then a cached one, then the stripped one."""
    if isinstance(thumb, types.PhotoSize):
        return 3, int(thumb.size or 0)
    if isinstance(thumb, types.PhotoSizeProgressive):
        return 3, max(thumb.sizes or [0])
    if isinstance(thumb, types.PhotoCachedSize):
        return 2, len(thumb.bytes or b"")
    if isinstance(thumb, types.PhotoStrippedSize):
        return 1, len(thumb.bytes or b"")
    return 0, 0


def pick_thumb(document: Any) -> Any | None:
    """Best usable preview on a source document, or ``None``.

    ``VideoSize`` is skipped even though it is the largest entry: it is an
    animated MP4 cover, not a JPEG, and Telegram rejects it as a ``thumb``.
    ``PhotoPathSize`` is an SVG outline, and anything over Telegram's 200 KB
    thumbnail ceiling is passed over for a smaller size.
    """
    candidates: list[tuple[int, int, Any]] = []
    for thumb in getattr(document, "thumbs", None) or []:
        if isinstance(
            thumb, (types.VideoSize, types.PhotoPathSize, types.PhotoSizeEmpty)
        ):
            continue
        if not getattr(thumb, "type", None):
            continue
        tier, size = _thumb_rank(thumb)
        if tier == 0 or size > THUMB_MAX_BYTES:
            continue
        candidates.append((tier, size, thumb))
    if not candidates:
        return None
    return max(candidates, key=lambda item: (item[0], item[1]))[2]


async def source_thumb_bytes(
    client: TelegramClient, message: types.Message, document: Any
) -> bytes | None:
    """Download the source's own preview JPEG.

    The chosen size is requested by its ``type`` string: Telethon matches that
    against its own sorted list, which handles ``PhotoSizeProgressive`` (an
    instance of which it would otherwise refuse).
    """
    chosen = pick_thumb(document)
    if chosen is None:
        return None
    try:
        data = await client.download_media(message, file=bytes, thumb=chosen.type)
    except (RPCError, RuntimeError, ValueError, TypeError, OSError):
        return None
    return data if isinstance(data, bytes) and data else None


def ffmpeg_available() -> bool:
    return shutil.which("ffmpeg") is not None


async def generate_thumb_bytes(media_path: Path, duration: float) -> bytes | None:
    """Cut a single frame as a JPEG with ffmpeg, if ffmpeg is installed.

    Seeks ~10% in so the frame is not the black fade most videos open on. Fully
    optional: ffmpeg is not a dependency of this project, and a run without it
    simply keeps whatever preview the source had.
    """
    if not ffmpeg_available():
        return None
    seek = 1.0
    if duration > 0:
        seek = max(0.0, min(duration * 0.1, max(duration - 0.5, 0.0)))
    output = media_path.with_suffix(".thumb.jpg")
    try:
        process = await asyncio.create_subprocess_exec(
            "ffmpeg",
            "-nostdin",
            "-loglevel",
            "error",
            "-ss",
            f"{seek:.3f}",
            "-i",
            str(media_path),
            "-frames:v",
            "1",
            "-vf",
            f"scale={THUMB_WIDTH}:-2",
            "-q:v",
            "4",
            "-f",
            "mjpeg",
            "-y",
            str(output),
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.DEVNULL,
        )
        await process.wait()
        if process.returncode != 0 or not output.exists():
            return None
        data = output.read_bytes()
        return data if data and len(data) <= THUMB_MAX_BYTES else None
    except (OSError, ValueError):
        return None
    finally:
        output.unlink(missing_ok=True)


def video_attributes(
    document: Any, thumb: Any | None
) -> tuple[list[Any], float, bool]:
    """Rebuild the document's attributes with streaming and sane dimensions.

    Telegram needs a width and height to lay the preview out; when the source
    attribute has none, the thumbnail's own dimensions are borrowed so at least
    the aspect ratio is right. Returns the attributes, the duration (for the
    ffmpeg seek) and whether the video is silent.
    """
    rest: list[Any] = []
    found: types.DocumentAttributeVideo | None = None
    for attribute in getattr(document, "attributes", None) or []:
        if isinstance(attribute, types.DocumentAttributeVideo):
            found = attribute
        else:
            rest.append(attribute)

    duration = float(getattr(found, "duration", 0) or 0)
    width = int(getattr(found, "w", 0) or 0)
    height = int(getattr(found, "h", 0) or 0)
    if (width <= 0 or height <= 0) and thumb is not None:
        width = int(getattr(thumb, "w", 0) or 0) or width
        height = int(getattr(thumb, "h", 0) or 0) or height
    if width <= 0 or height <= 0:
        width, height = THUMB_WIDTH, THUMB_WIDTH
    nosound = bool(getattr(found, "nosound", False))

    rest.append(
        types.DocumentAttributeVideo(
            duration=duration,
            w=width,
            h=height,
            round_message=bool(getattr(found, "round_message", False)),
            supports_streaming=True,
            nosound=nosound,
        )
    )
    return rest, duration, nosound


def sent_has_thumb(sent: Any) -> bool:
    """Did the message that just landed actually get a preview?"""
    document = getattr(sent, "document", None)
    if document is None:
        return False
    for thumb in getattr(document, "thumbs", None) or []:
        if not isinstance(thumb, (types.PhotoSizeEmpty, types.PhotoPathSize)):
            return True
    return False


# ---------------------------------------------------------------------------
# Copying one video
# ---------------------------------------------------------------------------


@dataclass(slots=True)
class CopyOutcome:
    mode: str
    thumbnail: bool


@dataclass(slots=True)
class Relay:
    """One reading account paired with one posting account.

    The reader pulls bytes out of the source; the uploader pushes them into the
    destination under its own session. When both are the same account the
    cheap pointer copy is possible; when they differ it is not, because a media
    pointer is only valid for the account that fetched it.
    """

    reader: Worker
    uploader: Worker
    source_peer: Any
    dest_peer: Any
    lane: TaskID

    @property
    def same_account(self) -> bool:
        return self.reader.user_id == self.uploader.user_id

    @property
    def tag(self) -> str:
        if self.same_account:
            return self.uploader.label
        return f"{self.reader.label}→{self.uploader.label}"


async def copy_video(
    relay: Relay,
    message: types.Message,
    temp_dir: Path,
    dashboard: Dashboard,
    *,
    pointer: PointerState,
) -> CopyOutcome:
    """Copy one video into the destination, keeping its preview visible.

    * **pointer copy** — only when the reader and uploader are the same
      account, since a media pointer cannot be handed to another account. Free
      and instant, and skipped entirely for a source that restricts saving.
    * **relay** — the reader streams the bytes and the uploader pushes them up
      under its own session, so the uploader needs no access to the source.

    The ``thumb`` the sibling scripts never set is set on the relay path, which
    is what keeps previews from coming out blank.
    """
    uploader = relay.uploader
    lane = relay.lane
    caption = video_caption(message.id)
    document = cast(Any, message).document
    source_thumb = pick_thumb(document) if document is not None else None
    can_generate = ffmpeg_available() and document is not None

    if relay.same_account and pointer.allowed and (
        source_thumb is not None or not can_generate
    ):
        dashboard.transfer.update(
            lane, description=f"{relay.tag} link #{message.id}"
        )
        try:
            sent = await rpc_call(
                f"{relay.tag}: copy #{message.id}",
                lambda: uploader.client.send_file(
                    relay.dest_peer,
                    file=cast(Any, message.media),
                    caption=caption,
                    supports_streaming=True,
                ),
                retry_server_errors=False,
            )
            return CopyOutcome("linked", sent_has_thumb(sent))
        except ChatForwardsRestrictedError:
            # The whole source is protected, so stop trying for the rest of it.
            pointer.allowed = False
        except (MediaEmptyError, FileReferenceExpiredError):
            # Just this reference is stale: fall through and move the bytes.
            pass

    if document is None:
        raise RuntimeError("This video message has no document to copy.")

    size = int(getattr(document, "size", 0) or 0)
    if size <= 0:
        raise RuntimeError("Telegram reported no size for this video.")
    file_name = document_filename(document, message.id)
    attributes, duration, nosound = video_attributes(document, source_thumb)

    def on_progress(done: int) -> None:
        dashboard.transfer.update(lane, completed=done, total=size)

    # The source's own preview is cheap and always preferred; only a video with
    # none needs the local file so ffmpeg can cut a frame out of it.
    thumb_data = await source_thumb_bytes(
        relay.reader.client, message, document
    )
    media_path: Path | None = None
    try:
        if thumb_data is None and can_generate:
            media_path = temp_dir / f"{uploader.label}_{message.id}_{file_name}"
            dashboard.transfer.reset(
                lane,
                description=f"{relay.tag} ↓ #{message.id}",
                total=size,
                start=True,
            )
            await pooled_download(
                await worker_transport(relay.reader),
                document,
                media_path,
                size,
                on_progress,
            )
            thumb_data = await generate_thumb_bytes(media_path, duration)
            dashboard.transfer.reset(
                lane,
                description=f"{relay.tag} ↑ #{message.id}",
                total=size,
                start=True,
            )
            input_file: Any = await pooled_upload(
                await worker_transport(uploader),
                media_path,
                size,
                file_name,
                on_progress,
            )
        else:
            dashboard.transfer.reset(
                lane,
                description=f"{relay.tag} ⇄ #{message.id}",
                total=size,
                start=True,
            )
            input_file = await relay_copy(
                relay.reader, uploader, document, file_name, size, on_progress
            )

        # The preview is uploaded by the account that will post, so the handle
        # it returns belongs to that account's session.
        thumb_file = None
        if thumb_data:
            try:
                thumb_file = await uploader.client.upload_file(
                    thumb_data, file_name=f"{message.id}_thumb.jpg"
                )
            except (RPCError, RuntimeError, ValueError, TypeError):
                thumb_file = None

        media = types.InputMediaUploadedDocument(
            file=input_file,
            thumb=thumb_file,
            mime_type=document.mime_type or "video/mp4",
            attributes=attributes,
            nosound_video=nosound or None,
        )
        sent = await rpc_call(
            f"{relay.tag}: send #{message.id}",
            lambda: uploader.client.send_file(
                relay.dest_peer, file=media, caption=caption
            ),
            retry_server_errors=False,
        )
        return CopyOutcome("re-uploaded", sent_has_thumb(sent))
    finally:
        if media_path is not None:
            media_path.unlink(missing_ok=True)
        dashboard.transfer.reset(
            lane,
            description=f"{relay.tag} idle",
            total=None,
            start=False,
        )


# ---------------------------------------------------------------------------
# Running one destination group
# ---------------------------------------------------------------------------


@dataclass(slots=True)
class GroupResult:
    brand: str
    title: str
    sources: list[str]
    destination: Any | None = None
    invite_link: str | None = None
    copied: int = 0
    failed: int = 0
    skipped: int = 0
    already: int = 0
    deferred: int = 0
    no_thumb: int = 0
    locked: bool = False
    members_restricted: bool = False
    posters: list[str] = field(default_factory=list)
    error: str | None = None


# Errors that mean this account can never post here, however many times it
# tries: a peer it cannot address, a permission it does not have, or a dead
# session. The video is given back to the queue and the account is ejected,
# because retrying it would just burn the whole queue (which is what a single
# broken worker did before: it failed instantly, so it won the race for every
# video and marked thousands of them failed).
FATAL_WORKER_ERRORS = (
    PeerIdInvalidError,
    ChannelInvalidError,
    ChannelPrivateError,
    ChatWriteForbiddenError,
    ChatAdminRequiredError,
    UserBannedInChannelError,
    ChatSendMediaForbiddenError,
    ChatSendVideosForbiddenError,
    AuthKeyUnregisteredError,
    UserDeactivatedError,
    UserDeactivatedBanError,
    SessionRevokedError,
)


@dataclass(slots=True)
class PointerState:
    """Whether a pointer copy is still worth attempting for this source.

    A chat with "restrict saving content" refuses every pointer copy, so after
    the first refusal the attempt is dropped for the rest of the source. Over
    thousands of videos that is thousands of pointless round trips saved.
    """

    allowed: bool = True
    announced: bool = False


async def copy_plan(
    relays: list[Relay],
    plan: Plan,
    temp_dir: Path,
    state: FinalState,
    eta: Eta,
    dashboard: Dashboard,
    result: GroupResult,
    pointer: PointerState,
) -> None:
    """Drain one source's pending videos through every reader/uploader pair.

    Each pair takes the next id off a shared queue and carries that video end
    to end. A pair that is throttled, broken or unable to post is taken out and
    its video handed back, so the queue always drains through whatever is still
    healthy instead of being consumed by a session that fails instantly.
    """
    queue: asyncio.Queue[tuple[int, int]] = asyncio.Queue()
    for item in plan.pending:
        queue.put_nowait(item)
    guard = asyncio.Lock()
    ejected: set[str] = set()
    streak: dict[str, int] = {}

    async def eject(relay: Relay, message_id: int, size: int, why: str) -> None:
        """Retire a pair and give its current video back to the queue."""
        ejected.add(relay.tag)
        relay.uploader.last_error = why[:120]
        queue.put_nowait((message_id, size))
        remaining = sorted(
            {other.tag for other in relays if other.tag not in ejected}
        )
        console.print(
            f"  [red]⊘[/red] {relay.tag} taken out of this source "
            f"({escape(why)}); #{message_id} requeued"
        )
        if remaining:
            console.print(f"  [dim]still posting via {', '.join(remaining)}[/dim]")
        else:
            console.print(
                "  [yellow]no account left for this source; the rest is left "
                "for a rerun[/yellow]"
            )

    async def consume(relay: Relay) -> None:
        uploader = relay.uploader
        while True:
            if relay.tag in ejected:
                return
            try:
                message_id, size = queue.get_nowait()
            except asyncio.QueueEmpty:
                return
            try:
                # Only the reader can see the source, so it fetches the message.
                message = cast(
                    Any,
                    await rpc_call(
                        f"{relay.reader.label}: fetch #{message_id}",
                        lambda: relay.reader.client.get_messages(
                            relay.source_peer, ids=message_id
                        ),
                    ),
                )
                if message is None or not getattr(message, "video", None):
                    # Deleted since the scan: bank it so later runs skip it.
                    async with guard:
                        result.skipped += 1
                        eta.drop(size)
                        dashboard.retotal()
                    await state.mark_copied(
                        plan.brand, plan.key, plan.title, message_id
                    )
                    continue

                was_allowed = pointer.allowed
                outcome = await copy_video(
                    relay, message, temp_dir, dashboard, pointer=pointer
                )
                if was_allowed and not pointer.allowed and not pointer.announced:
                    pointer.announced = True
                    console.print(
                        f"[dim]{escape(plan.title)} restricts saving, so every "
                        f"video is re-uploaded; not trying to link again.[/dim]"
                    )
                await state.mark_copied(plan.brand, plan.key, plan.title, message_id)
                async with guard:
                    result.copied += 1
                    uploader.copied += 1
                    streak[relay.tag] = 0
                    if not outcome.thumbnail:
                        result.no_thumb += 1
                    eta.complete(size)
                    dashboard.advance()
                note = "" if outcome.thumbnail else " [yellow](no preview)[/yellow]"
                console.print(
                    f"  [green]✓[/green] #{message_id} {outcome.mode} "
                    f"[dim]· {relay.tag}[/dim]{note}"
                )
            except (FloodWaitError, FloodTooLongError) as error:
                seconds = int(getattr(error, "seconds", 60))
                uploader.cooldown_until = time.monotonic() + seconds
                uploader.last_error = f"throttled {seconds}s"
                queue.put_nowait((message_id, size))
                console.print(
                    f"  [yellow]⏸ {relay.tag} throttled ~{seconds}s; "
                    f"requeued #{message_id}[/yellow]"
                )
                return
            except FATAL_WORKER_ERRORS as error:
                async with guard:
                    await eject(relay, message_id, size, _short(error))
                return
            except Exception as error:  # noqa: BLE001 - one video must not stop the run
                async with guard:
                    hits = streak.get(relay.tag, 0) + 1
                    streak[relay.tag] = hits
                    if hits >= MAX_CONSECUTIVE_FAILURES:
                        # Not this video's fault; the pair is unwell.
                        await eject(
                            relay,
                            message_id,
                            size,
                            f"{hits} failures in a row, last: {_short(error)}",
                        )
                        return
                    result.failed += 1
                    uploader.failed += 1
                    uploader.last_error = str(error)
                    eta.drop(size)
                    dashboard.retotal()
                console.print(
                    f"  [red]✗[/red] #{message_id} failed ({relay.tag}): "
                    f"{escape(str(error))}"
                )

    await asyncio.gather(*(consume(relay) for relay in relays))


async def resolve_destination(
    owner: Worker, plans: Sequence[Plan], brand: str, state: FinalState
) -> tuple[Any, str, str | None]:
    """Reuse this brand's saved group when it still exists, else make one."""
    client = owner.client
    record = state.groups.get(brand)
    if record:
        try:
            saved = types.InputPeerChannel(
                channel_id=int(record["channel_id"]),
                access_hash=int(record["access_hash"]),
            )
            await rpc_call("verify saved group", lambda: client.get_entity(saved))
            title = str(record.get("title") or group_title(plans[0].title))
            saved_link = record.get("invite_link")
            console.print(
                f"[bright_cyan]Reusing[/bright_cyan] [bold]{escape(title)}[/bold]"
            )
            return saved, title, saved_link if isinstance(saved_link, str) else None
        except (KeyError, TypeError, ValueError, RPCError, RuntimeError):
            console.print(
                "[yellow]The saved group is gone; creating a new one.[/yellow]"
            )
            await state.forget_group(brand)

    channel = await create_group(client, plans[0].title)
    title = group_title(plans[0].title)
    link: str | None = None
    try:
        link = await export_private_group_link(client, channel)
    except (RPCError, RuntimeError) as error:
        console.print(
            f"[yellow]Group created but its invite link failed: "
            f"{escape(str(error))}[/yellow]"
        )
    await state.remember_group(
        brand,
        {
            "title": title,
            "channel_id": int(channel.id),
            "access_hash": int(channel.access_hash or 0),
            "invite_link": link,
            "locked": False,
        },
    )
    console.print(f"[green]Created[/green] [bold]{escape(title)}[/bold]")
    return channel, title, link


def parallel_videos() -> int:
    """Videos one account copies at once. Override with FINAL_PARALLEL_VIDEOS."""
    raw = os.environ.get("FINAL_PARALLEL_VIDEOS", "")
    if raw.isdigit() and int(raw) > 0:
        return max(1, min(MAX_PARALLEL_VIDEOS, int(raw)))
    return DEFAULT_PARALLEL_VIDEOS


async def verified_dest_peer(
    worker: Worker, channel_id: int, fallback: Any
) -> Any | None:
    """Get a destination handle this worker can really send media to.

    A worker freshly added to a group often has no access hash for it, and
    Telethon then falls back to a stub peer that resolves but is rejected by
    ``SendMedia`` with "invalid Peer" — thousands of times in a row, which is
    what happened. Asking Telegram for the channel yields this account's own
    access hash, and a participant lookup proves the handle works before any
    video is handed to it.
    """
    client = worker.client
    peer = fallback
    try:
        got = cast(
            Any,
            await rpc_call(
                f"{worker.label}: resolve destination",
                lambda: client(
                    channels.GetChannelsRequest(
                        [types.InputChannel(channel_id, access_hash=0)]
                    )
                ),
                retry_server_errors=False,
            ),
        )
        channel = next(
            (chat for chat in got.chats if isinstance(chat, types.Channel)), None
        )
        if channel is not None and channel.access_hash is not None:
            peer = types.InputPeerChannel(
                channel_id=channel.id, access_hash=channel.access_hash
            )
    except (RPCError, RuntimeError, ValueError, TypeError):
        pass
    if peer is None:
        return None
    try:
        await rpc_call(
            f"{worker.label}: confirm membership",
            lambda: client(
                channels.GetParticipantRequest(
                    channel=cast(Any, utils.get_input_channel(peer)),
                    participant=types.InputPeerSelf(),
                )
            ),
            retry_server_errors=False,
        )
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        worker.last_error = f"destination: {_short(error)}"
        return None
    return peer


async def reader_dest_peer(
    owner: Worker,
    reader: Worker,
    destination: Any,
    channel_id: int,
    invite_link: str | None,
    inviters: list[Worker],
) -> Any | None:
    """A destination handle for the reader, so it can try forwarding.

    Forwarding needs one account that is in both chats. The reader is the one
    that can see the source, so it is the only candidate; this gets it into the
    destination as an anonymous admin like any uploader.
    """
    if reader.user_id == owner.user_id:
        return destination
    attached = await attach_worker_to_group(
        cast(Any, inviters), reader, destination, channel_id, invite_link
    )
    if attached is None:
        return None
    if not await promote_anonymous(owner.client, destination, reader):
        return None
    return await verified_dest_peer(reader, channel_id, attached)


async def forward_all(
    reader: Worker,
    dest_peer: Any,
    source_peer: Any,
    plan: Plan,
    state: FinalState,
    eta: Eta,
    dashboard: Dashboard,
    result: GroupResult,
) -> bool:
    """Move a whole source by forwarding, if Telegram will allow it.

    A forward moves no bytes: the server repoints the existing file, so a
    hundred videos cost one request and a 100 MB video costs the same as a
    1 MB one. ``drop_author`` removes the "forwarded from" header, and an
    anonymous admin's forwards are signed as the group, so the result looks the
    same as an upload.

    Returns ``False`` without side effects when the source restricts saving, so
    the caller can fall back to moving the bytes. This is checked rather than
    assumed because the difference is minutes against hours.

    One trade-off: a forward keeps the original caption, so these messages carry
    no ``video ~ 💗 id`` marker and the caption scan cannot recover them. The
    state file is what makes a rerun resume, and it is written per batch.
    """
    # Forwarding is size-blind, so the videos held back from the byte path go
    # in the same pass rather than waiting for the "high" question.
    pending = plan.everything
    if not pending:
        return True
    sizes = dict(pending)
    ids = [message_id for message_id, _size in pending]
    # The oversized videos are not in the run's estimate, because until the
    # probe succeeds we do not know they can be moved. They are added once the
    # first batch proves forwarding works, never before.
    queued = {message_id for message_id, _size in plan.pending}
    extra = [item for item in pending if item[0] not in queued]
    counted = False
    task = dashboard.lane(f"{reader.label} forward")
    dashboard.transfer.reset(
        task, description=f"{reader.label} forwarding", total=len(ids), start=True
    )
    done = 0
    try:
        for start in range(0, len(ids), FORWARD_BATCH):
            batch = ids[start : start + FORWARD_BATCH]

            async def send(current: list[int] = batch) -> Any:
                return await reader.client.forward_messages(
                    dest_peer,
                    current,
                    from_peer=source_peer,
                    drop_author=True,
                    silent=True,
                )

            try:
                sent = cast(
                    Any,
                    await rpc_call(
                        f"{reader.label}: forward {len(batch)}",
                        send,
                        retry_server_errors=False,
                    ),
                )
            except ChatForwardsRestrictedError:
                if done == 0:
                    # Protected source: nothing happened, so the caller can
                    # fall back to re-uploading without any double-send.
                    return False
                raise
            if not counted:
                counted = True
                if extra:
                    eta.plan(size for _id, size in extra)
                    dashboard.retotal()
            landed = (
                sum(1 for message in sent if message is not None)
                if isinstance(sent, (list, tuple))
                else (1 if sent is not None else 0)
            )
            for message_id in batch:
                await state.mark_copied(
                    plan.brand, plan.key, plan.title, message_id
                )
            result.copied += landed
            result.skipped += len(batch) - landed
            reader.copied += landed
            for message_id in batch:
                eta.complete(sizes.get(message_id, 0))
            done += len(batch)
            dashboard.transfer.update(task, completed=done)
            dashboard.advance()
            console.print(
                f"  [green]✓[/green] {landed}/{len(batch)} forwarded "
                f"[dim]· {reader.label}[/dim]"
            )
            await asyncio.sleep(FORWARD_INTERVAL)
        return True
    finally:
        dashboard.transfer.remove_task(task)


async def pick_reader(
    owner: Worker,
    pool: Sequence[Worker],
    source: types.Chat | types.Channel,
    entry_link: str | None,
    probe_ids: Sequence[int],
) -> tuple[Worker | None, Any]:
    """Choose the one account that will read this source, Premium first.

    Only this account needs to see the source, and Telegram does not meter a
    Premium account's download speed, so a Premium session is the best reader
    even when other accounts could also reach the chat.
    """
    ordered = [s for s in pool if s.premium] + [s for s in pool if not s.premium]
    for candidate in ordered:
        if candidate.user_id == owner.user_id:
            try:
                peer = await owner.client.get_input_entity(to_peer(source))
            except (RPCError, ValueError, TypeError):
                continue
            if await can_read_source(owner.client, peer, probe_ids):
                return candidate, peer
            continue
        peer = await worker_source_peer(
            owner, candidate, source, entry_link, probe_ids
        )
        if peer is not None:
            return candidate, peer
    return None, None


async def run_group(
    pool: list[Worker],
    brand: str,
    plans: list[Plan],
    temp_dir: Path,
    state: FinalState,
    eta: Eta,
    dashboard: Dashboard,
) -> GroupResult:
    """Provision one destination group and fill it.

    Freezing is not done here: that waits until every group is finished and the
    choice about oversized videos has been made, so a group is only closed once
    there is genuinely nothing more to put in it.
    """
    owner = pool[0]
    result = GroupResult(
        brand=brand,
        title=group_title(plans[0].title),
        sources=[plan.title for plan in plans],
        already=sum(plan.already for plan in plans),
        deferred=sum(len(plan.big) for plan in plans),
    )
    console.rule(f"[bold bright_magenta]{escape(result.title)}[/bold bright_magenta]")

    try:
        destination, title, link = await resolve_destination(owner, plans, brand, state)
    except (RPCError, RuntimeError, ValueError) as error:
        result.error = str(error)
        console.print(
            f"[red]No group for '{escape(brand)}':[/red] {escape(str(error))}"
        )
        # None of this group's videos will move, so drop them from the ETA.
        for plan in plans:
            eta.drop_many(size for _id, size in plan.pending)
        dashboard.retotal()
        return result
    result.destination = destination
    result.title = title
    result.invite_link = link
    if link:
        print_named_link(title, link)

    # Take the group's name and photo away from normal members straight away
    # and permanently. Sending stays open until the whole run is done.
    result.members_restricted = await apply_member_rights(
        owner.client, destination, allow_sending=True, label="restrict members"
    )
    await make_owner_anonymous(owner, destination)

    # A reused group may already hold videos this state file does not know
    # about, so its captions are reconciled before anything is sent.
    if state.groups.get(brand, {}).get("channel_id") and len(plans) == 1:
        try:
            remote = await destination_copied_ids(owner.client, destination)
            if remote:
                plan = plans[0]
                stale = [item for item in plan.pending if item[0] in remote]
                if stale:
                    plan.pending = [
                        item for item in plan.pending if item[0] not in remote
                    ]
                    eta.drop_many(size for _id, size in stale)
                    dashboard.retotal()
                    result.already += len(stale)
                    console.print(
                        f"[dim]{len(stale)} video(s) already in the group; "
                        f"skipping[/dim]"
                    )
        except (RPCError, RuntimeError) as error:
            console.print(
                f"[yellow]Could not reconcile existing captions "
                f"({escape(str(error))}); using the saved checkpoint.[/yellow]"
            )

    channel_id = int(getattr(destination, "channel_id", getattr(destination, "id", 0)))
    primary = plans[0].source
    slots = parallel_videos()

    for plan in plans:
        if not plan.pending:
            console.print(f"[dim]{escape(plan.title)} · nothing new[/dim]")
            continue

        probe_ids = [message_id for message_id, _size in plan.pending]
        entry_link = (
            await source_entry_link(owner.client, plan.source)
            if len(pool) > 1
            else None
        )
        reader, reader_source = await pick_reader(
            owner, pool, plan.source, entry_link, probe_ids
        )
        if reader is None or reader_source is None:
            plan.error = "No signed-in account can read this source."
            console.print(f"[red]{escape(plan.title)}: {plan.error}[/red]")
            eta.drop_many(size for _id, size in plan.pending)
            dashboard.retotal()
            continue

        # Uploaders need no access to the source at all: they are handed raw
        # bytes. They only have to be anonymous admins of the destination. With
        # other accounts available the reader is left to do nothing but read.
        candidates = [s for s in pool if s.user_id != reader.user_id] or [reader]
        uploaders: list[tuple[Worker, Any]] = []
        inviters: list[Worker] = [owner]
        for worker in candidates:
            if worker.user_id == owner.user_id:
                # The owner created the group, so its handle is already good.
                uploaders.append((worker, destination))
                continue
            attached = await attach_worker_to_group(
                cast(Any, inviters), worker, primary, channel_id, result.invite_link
            )
            if attached is None:
                worker.last_error = "could not be added to the backup group"
                console.print(
                    f"[yellow]{worker.label} could not be added to "
                    f"{escape(result.title)}; it sits this group out.[/yellow]"
                )
                continue
            # Anonymity is not optional: an unpromoted account would be
            # credited by name and user id on every video it sent.
            if not await promote_anonymous(owner.client, destination, worker):
                console.print(
                    f"[yellow]{worker.label} is not anonymous here, so it will "
                    f"not post (its id would be visible).[/yellow]"
                )
                continue
            inviters.append(worker)
            # Prove the handle works now, rather than discovering per video
            # that every send is rejected.
            dest_peer = await verified_dest_peer(worker, channel_id, attached)
            if dest_peer is None:
                console.print(
                    f"[yellow]{worker.label} cannot address "
                    f"{escape(result.title)} ({escape(worker.last_error)}); it "
                    f"sits this group out.[/yellow]"
                )
                continue
            uploaders.append((worker, dest_peer))

        if not uploaders:
            console.print(
                f"[yellow]No worker could post into {escape(result.title)}; "
                f"{reader.label} will upload as well as read.[/yellow]"
            )
            if not reader.anonymous:
                console.print(
                    f"[yellow]Note: {reader.label} is not anonymous here, so "
                    f"its videos will be credited to it.[/yellow]"
                )
            uploaders = [(reader, destination)]

        now = time.monotonic()
        ready = [item for item in uploaders if item[0].cooldown_until <= now]
        if not ready:
            console.print(
                "[yellow]Every uploader is cooling down; leaving this source "
                "for a rerun.[/yellow]"
            )
            eta.drop_many(size for _id, size in plan.pending)
            dashboard.retotal()
            continue

        # Routing every download through one account caps all the uploaders at
        # that one account's download allowance. Telegram does not meter a
        # Premium account, so funnelling through one is a clear win; without
        # Premium it is a bottleneck, and any account that can reach the source
        # is better off fetching its own videos in parallel. Doing so also
        # re-enables the free pointer copy for that account.
        own_source: dict[int, Any] = {reader.user_id: reader_source}
        if not reader.premium:
            for worker, _dest in ready:
                if worker.user_id in own_source:
                    continue
                peer = await worker_source_peer(
                    owner, worker, plan.source, entry_link, probe_ids
                )
                if peer is not None:
                    own_source[worker.user_id] = peer

        uploading = [worker for worker, _dest in ready]
        downloading = [
            worker for worker in uploading if worker.user_id in own_source
        ]
        relayed = [
            worker for worker in uploading if worker.user_id not in own_source
        ]
        if relayed and reader.user_id not in {w.user_id for w in downloading}:
            downloading.append(reader)
        allocate_lanes(downloading, uploading)

        relays: list[Relay] = []
        for worker, dest_peer in ready:
            source_peer = own_source.get(worker.user_id)
            relay_reader = worker if source_peer is not None else reader
            for slot in range(slots):
                label = worker.label if slots == 1 else f"{worker.label}.{slot + 1}"
                relays.append(
                    Relay(
                        reader=relay_reader,
                        uploader=worker,
                        source_peer=source_peer
                        if source_peer is not None
                        else reader_source,
                        dest_peer=dest_peer,
                        lane=dashboard.lane(
                            label
                            if relay_reader.user_id == worker.user_id
                            else f"{reader.label}→{label}"
                        ),
                    )
                )
        result.posters = sorted(
            {*result.posters, *(relay.uploader.label for relay in relays)}
        )
        own = [w.label for w in uploading if w.user_id in own_source]
        console.print(
            f"[dim]{escape(plan.title)} · {len(plan.pending)} video(s) · "
            f"uploading via {', '.join(sorted(w.label for w in uploading))}[/dim]"
        )
        if reader.premium:
            console.print(
                f"[dim]fetching via {reader.label} (premium, unmetered) for "
                f"all {len(uploading)} uploader(s)[/dim]"
            )
        else:
            detail = f"{len(own)} account(s) fetch their own"
            if relayed:
                detail += (
                    f" · {len(relayed)} relayed via {reader.label} "
                    f"(no source access)"
                )
            console.print(f"[dim]{detail}[/dim]")
            if len(own) < 2:
                console.print(
                    f"[yellow]Only {reader.label} can read this source and it "
                    f"is not Premium, so its download cap limits every "
                    f"uploader. Premium on {reader.label}, or getting the "
                    f"workers into the source, is what lifts this.[/yellow]"
                )
        console.print(
            f"[dim]{sum(w.download_lanes for w in downloading)} download + "
            f"{sum(w.upload_lanes for w in uploading)} upload socket(s) of "
            f"{connection_budget()} budget[/dim]"
        )
        # Forwarding costs nothing, so it is worth one request to find out
        # whether this source permits it before moving a single byte.
        if not bool(getattr(plan.source, "noforwards", False)):
            forward_peer = await reader_dest_peer(
                owner, reader, destination, channel_id, result.invite_link,
                inviters,
            )
            if forward_peer is not None:
                console.print(
                    f"[dim]checking whether {escape(plan.title)} allows "
                    f"forwarding…[/dim]"
                )
                if await forward_all(
                    reader,
                    forward_peer,
                    reader_source,
                    plan,
                    state,
                    eta,
                    dashboard,
                    result,
                ):
                    held = len(plan.big) + len(plan.oversize)
                    console.print(
                        f"[green]{escape(plan.title)} allows forwarding — "
                        f"copied with no bytes moved.[/green]"
                    )
                    if held:
                        console.print(
                            f"[green]{held} oversized video(s) went too, since "
                            f"forwarding ignores size.[/green]"
                        )
                    # Nothing is outstanding for this source any more.
                    plan.pending = []
                    plan.big = []
                    plan.oversize = []
                    result.deferred = 0
                    for relay in relays:
                        dashboard.transfer.remove_task(relay.lane)
                    continue
                console.print(
                    f"[dim]{escape(plan.title)} restricts saving, so its bytes "
                    f"have to be moved.[/dim]"
                )

        pointer = PointerState(
            allowed=not bool(getattr(plan.source, "noforwards", False))
        )
        try:
            await copy_plan(
                relays, plan, temp_dir, state, eta, dashboard, result, pointer
            )
        finally:
            for relay in relays:
                dashboard.transfer.remove_task(relay.lane)

    return result


# ---------------------------------------------------------------------------
# Folder and report
# ---------------------------------------------------------------------------


async def create_folder(
    client: TelegramClient, first_title: str, destinations: Sequence[Any]
) -> tuple[str, str] | None:
    """Collect every destination into one shared Telegram folder."""
    if not destinations:
        return None
    try:
        title = folder_title(first_title)
        filter_id = await free_filter_id(client)
        peers = [await client.get_input_entity(item) for item in destinations]
        dialog_filter = types.DialogFilterChatlist(
            id=filter_id,
            title=types.TextWithEntities(text=title, entities=[]),
            pinned_peers=[],
            include_peers=peers,
        )
        await rpc_call(
            "create backup folder",
            lambda: client(
                messages.UpdateDialogFilterRequest(id=filter_id, filter=dialog_filter)
            ),
        )
        exported = cast(
            Any,
            await rpc_call(
                "export folder link",
                lambda: client(
                    chatlists.ExportChatlistInviteRequest(
                        chatlist=types.InputChatlistDialogFilter(filter_id=filter_id),
                        title=title,
                        peers=peers,
                    )
                ),
                retry_server_errors=False,
            ),
        )
        link = getattr(getattr(exported, "invite", None), "url", None)
        if not isinstance(link, str) or not link:
            return None
        return title, link
    except (RPCError, RuntimeError, ValueError, TypeError) as error:
        console.print(
            f"[yellow]Groups are ready but the folder could not be created: "
            f"{escape(str(error))}[/yellow]"
        )
        return None


def merge_result(into: GroupResult, extra: GroupResult) -> None:
    """Fold a second pass over the same group into its first result."""
    into.copied += extra.copied
    into.failed += extra.failed
    into.skipped += extra.skipped
    into.no_thumb += extra.no_thumb
    into.deferred = extra.deferred
    into.posters = sorted({*into.posters, *extra.posters})
    if extra.destination is not None:
        into.destination = extra.destination
        into.invite_link = extra.invite_link or into.invite_link
        into.title = extra.title
    into.error = extra.error or into.error


async def run_pass(
    pool: list[Worker],
    by_brand: dict[str, list[Plan]],
    state: FinalState,
    eta: Eta,
    temp_dir: Path,
    merged: dict[str, GroupResult],
    label: str,
) -> None:
    """Fill every destination group once, under one live dashboard."""
    with Dashboard(eta, label) as dashboard:
        for brand, plans in by_brand.items():
            result = await run_group(
                pool, brand, plans, temp_dir, state, eta, dashboard
            )
            if brand in merged:
                merge_result(merged[brand], result)
            else:
                merged[brand] = result


def ask_oversized(count: int, total_bytes: int) -> bool:
    """Offer the held-back oversized videos once everything else is done."""
    console.print(
        Panel(
            f"[bold]{count}[/bold] video(s) are over "
            f"{human_size(MAX_VIDEO_BYTES)} and were held back "
            f"[dim]({human_size(total_bytes)} in total)[/dim]\n"
            f"[dim]'done' finishes and locks the groups · 'high' copies these "
            f"first, then locks[/dim]",
            border_style="bright_magenta",
            padding=(1, 3),
        )
    )
    while True:
        answer = (
            Prompt.ask(
                "[bright_cyan]done or high[/bright_cyan]", default="done"
            )
            .strip()
            .lower()
        )
        if answer in {"d", "done", "n", "no"}:
            return False
        if answer in {"h", "high", "y", "yes"}:
            return True
        console.print("[yellow]Type 'done' or 'high'.[/yellow]")


async def freeze_groups(
    owner: Worker, results: Sequence[GroupResult], state: FinalState
) -> int:
    """Turn message sending off for normal members, now the work is finished.

    Members already lost the group name and photo when the group was made; this
    is the final step that closes it for sending. Admins are exempt from a
    chat's default rights, so a later rerun can still add to a frozen group. A
    group with failures is left open so the rerun has somewhere to put them.
    """
    frozen = 0
    for result in results:
        if result.destination is None:
            continue
        if result.failed:
            console.print(
                f"[yellow]{result.failed} video(s) failed, so "
                f"{escape(result.title)} stays open for a rerun.[/yellow]"
            )
            continue
        if await apply_member_rights(
            owner.client,
            result.destination,
            allow_sending=False,
            label=f"freeze {result.title}",
        ):
            result.locked = True
            await state.remember_group(result.brand, {"locked": True})
            frozen += 1
            console.print(
                f"[bright_magenta]🔒 {escape(result.title)} is now read-only "
                f"for members[/bright_magenta]"
            )
    return frozen


def group_status(result: GroupResult) -> str:
    if result.destination is None:
        return "group failed"
    if result.error:
        return "stopped"
    if result.failed:
        return "partial"
    if result.locked:
        return "complete · locked"
    return "complete"


def show_report(
    results: Sequence[GroupResult],
    pool: Sequence[Worker],
    elapsed: float,
    folder: tuple[str, str] | None,
) -> bool:
    table = Table(
        title="Backup report",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("Backup group")
    table.add_column("Sources")
    table.add_column("New", justify="right")
    table.add_column("Before", justify="right")
    table.add_column("Gone", justify="right")
    table.add_column("Oversized", justify="right")
    table.add_column("Failed", justify="right")
    table.add_column("No preview", justify="right")
    table.add_column("Status")
    for result in results:
        table.add_row(
            escape(result.title) if result.destination else "Not created",
            escape(", ".join(result.sources)),
            str(result.copied),
            str(result.already),
            str(result.skipped),
            str(result.deferred) if result.deferred else "—",
            str(result.failed),
            str(result.no_thumb) if result.no_thumb else "—",
            group_status(result),
        )
    console.print("\n", table)

    workers = Table(
        title="Accounts",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    workers.add_column("Label")
    workers.add_column("Name")
    workers.add_column("User id", justify="right")
    workers.add_column("Anonymous")
    workers.add_column("Copied", justify="right")
    workers.add_column("Failed", justify="right")
    workers.add_column("Last issue")
    for session in pool:
        workers.add_row(
            session.label,
            escape(session.name or "—"),
            str(session.user_id),
            "yes" if session.anonymous else "no",
            str(session.copied),
            str(session.failed),
            escape(session.last_error[:48]) if session.last_error else "—",
        )
    console.print(workers)

    copied = sum(result.copied for result in results)
    failed = sum(result.failed for result in results)
    blank = sum(result.no_thumb for result in results)
    deferred = sum(result.deferred for result in results)
    locked = sum(1 for result in results if result.locked)
    complete = bool(results) and all(
        group_status(result).startswith("complete") for result in results
    )

    links = [
        result for result in results if result.invite_link and result.destination
    ]
    if links:
        console.print("[bold bright_magenta]Backup group links[/bold bright_magenta]")
        for result in links:
            print_named_link(result.title, cast(str, result.invite_link))
        console.print()

    label = "BACKUP COMPLETE" if complete else "BACKUP PARTIAL"
    style = "bright_magenta" if complete else "yellow"
    console.print(
        Panel(
            Align.center(
                f"[bold {style}]{label} {HEART}[/bold {style}]\n"
                f"[bold]{copied}[/bold] video(s) copied · "
                f"[bold]{locked}[/bold]/{len(results)} group(s) locked · "
                f"{failed} failed\n"
                f"[dim]took {format_duration(elapsed)} · "
                f"finished {datetime.now().strftime('%H:%M:%S')}[/dim]"
            ),
            border_style=style,
            padding=(1, 3),
        )
    )
    if CONNECTION_NOISE.count:
        console.print(
            f"[dim]{CONNECTION_NOISE.count} dropped connection(s) absorbed and "
            f"retried. A large number means the socket budget is too high for "
            f"this host; lower FINAL_TOTAL_CONNECTIONS.[/dim]"
        )
    if deferred:
        console.print(
            f"[yellow]{deferred} oversized video(s) were left; rerun and choose "
            f"'high' to copy them.[/yellow]"
        )
    if blank:
        hint = (
            "install ffmpeg and rerun to generate previews for them"
            if not ffmpeg_available()
            else "their sources carry no preview either"
        )
        console.print(
            f"[yellow]{blank} video(s) landed without a preview — {hint}.[/yellow]"
        )
    if folder:
        print_named_link(folder[0], folder[1], folder=True)
    return complete


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


async def run() -> bool:
    banner()
    _silence_shutdown_noise()
    quiet_connection_noise()
    started = time.monotonic()
    pool: list[Worker] = []
    try:
        pool, _api_id, _api_hash = await authenticate()
        owner = pool[0]
        state = FinalState()

        sources = await choose_sources(owner.client, state)
        if not sources:
            raise RuntimeError("No source group was selected.")
        sources = sources[:MAX_GROUPS]

        console.print("\n[dim]Working out what is left to copy…[/dim]")
        plans = [await build_plan(owner.client, source, state) for source in sources]
        show_plan(plans)
        console.print(
            f"[dim]{transfer_connections()} connections per video · "
            f"{parallel_videos()} video(s) at a time per account "
            f"(FINAL_CONNECTIONS / FINAL_PARALLEL_VIDEOS to change)[/dim]"
        )
        if not ffmpeg_available():
            console.print(
                "[dim]ffmpeg not found — source previews are reused, but one "
                "cannot be generated for a video that has none.[/dim]"
            )

        # Sibling sources share a destination, so work is grouped by brand.
        by_brand: dict[str, list[Plan]] = {}
        for plan in plans:
            by_brand.setdefault(plan.brand, []).append(plan)

        merged: dict[str, GroupResult] = {}
        with tempfile.TemporaryDirectory(prefix="final-") as temp:
            temp_dir = Path(temp)

            eta = Eta()
            for plan in plans:
                eta.plan(size for _id, size in plan.pending)
            eta.reset_clock()
            await run_pass(
                pool, by_brand, state, eta, temp_dir, merged, "backing up"
            )

            # Everything within the normal limit is done; offer the rest.
            big_count = sum(len(plan.big) for plan in plans)
            big_bytes = sum(plan.big_bytes for plan in plans)
            if big_count and ask_oversized(big_count, big_bytes):
                for plan in plans:
                    plan.pending = plan.big
                    plan.big = []
                high_eta = Eta()
                for plan in plans:
                    high_eta.plan(size for _id, size in plan.pending)
                high_eta.reset_clock()
                await run_pass(
                    pool,
                    by_brand,
                    state,
                    high_eta,
                    temp_dir,
                    merged,
                    "oversized videos",
                )

        results = [merged[brand] for brand in by_brand if brand in merged]
        for result in results:
            result.deferred = sum(
                len(plan.big) for plan in by_brand[result.brand]
            )

        await freeze_groups(owner, results, state)

        seen: set[int] = set()
        destinations: list[Any] = []
        for result in results:
            if result.destination is None:
                continue
            channel_id = int(
                getattr(
                    result.destination,
                    "channel_id",
                    getattr(result.destination, "id", 0),
                )
            )
            if channel_id in seen:
                continue
            seen.add(channel_id)
            destinations.append(result.destination)

        folder = await create_folder(owner.client, plans[0].title, destinations)
        return show_report(results, pool, time.monotonic() - started, folder)
    finally:
        await close_transports(pool)
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
