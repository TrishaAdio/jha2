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
import json
import math
import re
import shutil
import tempfile
import time
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
from types import TracebackType
from typing import Any, Iterable, Sequence, cast

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
from telethon import TelegramClient, types, utils
from telethon.errors import (
    ChatAdminRequiredError,
    ChatForwardsRestrictedError,
    FileReferenceExpiredError,
    FloodWaitError,
    MediaEmptyError,
    PeerFloodError,
    RPCError,
    UserAlreadyParticipantError,
    UserBannedInChannelError,
    UserChannelsTooMuchError,
    UserKickedError,
    UserNotMutualContactError,
    UserPrivacyRestrictedError,
)
from telethon.tl.functions import channels, chatlists, messages

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
    canonical_source_name,
    console,
    disconnect_client,
    document_filename,
    export_private_group_link,
    free_filter_id,
    human_size,
    import_shared_folder,
    join_target_chat,
    login_client,
    pace_joins,
    parallel_download,
    parallel_upload,
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
# Extra accounts that upload alongside the owner, each one anonymous.
MAX_WORKERS = 10
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
            )
        )

    show_accounts(pool)
    return pool, api_id, api_hash


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
    table.add_column("Role")
    for session in pool:
        table.add_row(
            session.label,
            escape(session.name or "—"),
            str(session.user_id),
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

    def __init__(self, eta: Eta) -> None:
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
        self.task = self.overall.add_task("backing up", total=eta.total_videos or 1)

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
    already: int = 0
    skipped: int = 0
    error: str | None = None

    @property
    def pending_bytes(self) -> int:
        return sum(size for _id, size in self.pending)


async def build_plan(
    client: TelegramClient,
    source: types.Chat | types.Channel,
    state: FinalState,
) -> Plan:
    """Server-side scan for the videos this source has not sent over yet."""
    title = utils.get_display_name(source) or f"Chat {utils.get_peer_id(source)}"
    key = str(utils.get_peer_id(source))
    brand = brand_key(title)
    plan = Plan(source=source, title=title, key=key, brand=brand)
    copied = state.copied_ids(brand, key)
    plan.already = len(copied)

    found: dict[int, int] = {}
    for media_filter in MEDIA_FILTERS:
        try:
            async for message in client.iter_messages(
                source, reverse=True, filter=media_filter
            ):
                if message.id in copied or message.id in found:
                    continue
                if not getattr(message, "video", None):
                    continue
                size = video_size(message)
                if size > MAX_VIDEO_BYTES:
                    plan.skipped += 1
                    continue
                found[message.id] = size
        except (RPCError, RuntimeError, ValueError) as error:
            plan.error = f"Scan failed: {error}"
            console.print(f"[red]{escape(plan.title)}: {escape(plan.error)}[/red]")
            break

    plan.pending = sorted(found.items())
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
    table.add_column("Too big", justify="right")
    for plan in plans:
        table.add_row(
            escape(plan.title),
            escape(group_title(plan.title)),
            str(len(plan.pending)),
            human_size(plan.pending_bytes),
            str(plan.already),
            str(plan.skipped),
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
        return "owner cannot resolve this worker (no shared chat or @username)"
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


async def copy_video(
    session: Worker,
    destination: Any,
    message: types.Message,
    temp_dir: Path,
    dashboard: Dashboard,
    lane: TaskID,
) -> CopyOutcome:
    """Copy one video, keeping its preview visible.

    Two routes:

    * **pointer copy** — ``send_file(file=message.media)`` has the server clone
      the existing document, so no bytes move and the preview comes along
      untouched. This is the normal case and it is near-instant.
    * **re-upload** — used when the chat forbids saving content, when the file
      reference has gone stale, *and* when the source itself has no preview and
      ffmpeg is around to make one (a pointer copy of a thumbnail-less video
      would be just as blank at the destination). The ``thumb`` that the
      sibling scripts never set is set here.
    """
    client = session.client
    caption = video_caption(message.id)
    document = cast(Any, message).document
    source_thumb = pick_thumb(document) if document is not None else None
    # A pointer copy is only worth taking if the result will have a preview,
    # or if we have no way of making one anyway.
    can_generate = ffmpeg_available() and document is not None
    prefer_pointer = source_thumb is not None or not can_generate

    if prefer_pointer:
        dashboard.transfer.update(
            lane, description=f"{session.label} link #{message.id}"
        )
        try:
            sent = await rpc_call(
                f"{session.label}: copy #{message.id}",
                lambda: client.send_file(
                    destination,
                    file=cast(Any, message.media),
                    caption=caption,
                    supports_streaming=True,
                ),
                retry_server_errors=False,
            )
            return CopyOutcome("linked", sent_has_thumb(sent))
        except (
            ChatForwardsRestrictedError,
            MediaEmptyError,
            FileReferenceExpiredError,
        ):
            # Protected chat or stale reference: fall through and move bytes.
            pass

    if document is None:
        raise RuntimeError("This video message has no document to copy.")

    size = int(getattr(document, "size", 0) or 0)
    file_name = document_filename(document, message.id)
    media_path = temp_dir / f"{session.label}_{message.id}_{file_name}"
    attributes, duration, nosound = video_attributes(document, source_thumb)

    def on_progress(current: int, total: int) -> None:
        dashboard.transfer.update(lane, completed=current, total=total or None)

    try:
        dashboard.transfer.reset(
            lane,
            description=f"{session.label} ↓ #{message.id}",
            total=size or None,
            start=True,
        )
        await rpc_call(
            f"{session.label}: download #{message.id}",
            lambda: parallel_download(client, document, media_path, on_progress),
            retry_server_errors=False,
        )

        # Prefer the source's own preview; make one only when there is none.
        thumb_data = await source_thumb_bytes(client, message, document)
        if thumb_data is None:
            thumb_data = await generate_thumb_bytes(media_path, duration)
        thumb_file = None
        if thumb_data:
            try:
                thumb_file = await client.upload_file(
                    thumb_data, file_name=f"{message.id}_thumb.jpg"
                )
            except (RPCError, RuntimeError, ValueError, TypeError):
                thumb_file = None

        actual_size = media_path.stat().st_size
        total_parts = math.ceil(actual_size / PART_SIZE) if actual_size else 0
        dashboard.transfer.reset(
            lane,
            description=f"{session.label} ↑ #{message.id}",
            total=actual_size or None,
            start=True,
        )

        if 0 < actual_size and total_parts <= MAX_UPLOAD_PARTS:
            input_file = await rpc_call(
                f"{session.label}: upload #{message.id}",
                lambda: parallel_upload(
                    client, media_path, actual_size, file_name, on_progress
                ),
                retry_server_errors=False,
            )
            media = types.InputMediaUploadedDocument(
                file=input_file,
                thumb=thumb_file,
                mime_type=document.mime_type or "video/mp4",
                attributes=attributes,
                nosound_video=nosound or None,
            )
            sent = await rpc_call(
                f"{session.label}: send #{message.id}",
                lambda: client.send_file(destination, file=media, caption=caption),
                retry_server_errors=False,
            )
        else:
            # Oversized or empty: hand the path to Telethon, which reads the
            # metadata with hachoir. The thumbnail still has to be passed in.
            sent = await rpc_call(
                f"{session.label}: send #{message.id}",
                lambda: client.send_file(
                    destination,
                    file=str(media_path),
                    caption=caption,
                    # Already an InputFile, so Telethon reuses it as-is
                    # instead of uploading the preview a second time.
                    thumb=thumb_file,
                    force_document=False,
                    supports_streaming=True,
                    progress_callback=on_progress,
                ),
                retry_server_errors=False,
            )
        return CopyOutcome("re-uploaded", sent_has_thumb(sent))
    finally:
        media_path.unlink(missing_ok=True)
        dashboard.transfer.update(
            lane, description=f"{session.label} idle", completed=0, total=None
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
    no_thumb: int = 0
    locked: bool = False
    members_restricted: bool = False
    posters: list[str] = field(default_factory=list)
    error: str | None = None


async def copy_plan(
    lanes: list[tuple[Worker, Any, Any, TaskID]],
    plan: Plan,
    temp_dir: Path,
    state: FinalState,
    eta: Eta,
    dashboard: Dashboard,
    result: GroupResult,
) -> None:
    """Spread one source's pending videos across every account that can post.

    Each account pulls the next id off a shared queue and copies it end to end
    on its own connections, so N accounts give roughly N times the throughput.
    A throttled account is parked and its video handed back to the queue rather
    than burned as a failure.
    """
    queue: asyncio.Queue[tuple[int, int]] = asyncio.Queue()
    for item in plan.pending:
        queue.put_nowait(item)
    guard = asyncio.Lock()

    async def consume(
        session: Worker, source_peer: Any, dest_peer: Any, lane: TaskID
    ) -> None:
        while True:
            try:
                message_id, size = queue.get_nowait()
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
                    # Deleted since the scan: bank it so later runs skip it.
                    async with guard:
                        result.skipped += 1
                        eta.drop(size)
                        dashboard.retotal()
                    await state.mark_copied(
                        plan.brand, plan.key, plan.title, message_id
                    )
                    continue

                outcome = await copy_video(
                    session, dest_peer, message, temp_dir, dashboard, lane
                )
                await state.mark_copied(plan.brand, plan.key, plan.title, message_id)
                async with guard:
                    result.copied += 1
                    session.copied += 1
                    if not outcome.thumbnail:
                        result.no_thumb += 1
                    eta.complete(size)
                    dashboard.advance()
                note = "" if outcome.thumbnail else " [yellow](no preview)[/yellow]"
                console.print(
                    f"  [green]✓[/green] #{message_id} {outcome.mode} "
                    f"[dim]· {session.label}[/dim]{note}"
                )
            except (FloodWaitError, FloodTooLongError) as error:
                seconds = int(getattr(error, "seconds", 60))
                session.cooldown_until = time.monotonic() + seconds
                session.last_error = f"throttled {seconds}s"
                queue.put_nowait((message_id, size))
                console.print(
                    f"  [yellow]⏸ {session.label} throttled ~{seconds}s; "
                    f"requeued #{message_id}[/yellow]"
                )
                return
            except Exception as error:  # noqa: BLE001 - one video must not stop the run
                async with guard:
                    result.failed += 1
                    session.failed += 1
                    session.last_error = str(error)
                    eta.drop(size)
                    dashboard.retotal()
                console.print(
                    f"  [red]✗[/red] #{message_id} failed ({session.label}): "
                    f"{escape(str(error))}"
                )

    await asyncio.gather(
        *(consume(session, sp, dp, lane) for session, sp, dp, lane in lanes)
    )


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


async def run_group(
    pool: list[Worker],
    brand: str,
    plans: list[Plan],
    temp_dir: Path,
    state: FinalState,
    eta: Eta,
    dashboard: Dashboard,
) -> GroupResult:
    """Provision one destination group, fill it, then freeze it."""
    owner = pool[0]
    result = GroupResult(
        brand=brand,
        title=group_title(plans[0].title),
        sources=[plan.title for plan in plans],
        already=sum(plan.already for plan in plans),
        skipped=sum(plan.skipped for plan in plans),
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

    # Take the group's name and photo away from normal members immediately and
    # permanently. Sending is left at Telegram's default for now and switched
    # off once this group's work is done, further down.
    has_work = any(plan.pending for plan in plans)
    result.members_restricted = await apply_member_rights(
        owner.client,
        destination,
        allow_sending=has_work,
        label="restrict members",
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

    # Build the posting roster: every worker that can both read the source and
    # post into this group, each one promoted anonymously.
    for plan in plans:
        entry_link = None
        roster: list[tuple[Worker, Any, Any]] = []
        inviters: list[Worker] = [owner]

        if not plan.pending:
            console.print(f"[dim]{escape(plan.title)} · nothing new[/dim]")
            continue

        if len(pool) > 1:
            entry_link = await source_entry_link(owner.client, plan.source)
        for worker in pool[1:]:
            # A worker has to reach both ends: read the source and post here.
            source_peer = await worker_source_peer(
                owner,
                worker,
                plan.source,
                entry_link,
                [message_id for message_id, _size in plan.pending],
            )
            if source_peer is None:
                continue
            dest_peer = await attach_worker_to_group(
                cast(Any, inviters), worker, primary, channel_id, result.invite_link
            )
            if dest_peer is None:
                worker.last_error = "could not be added to the backup group"
                console.print(
                    f"[yellow]{worker.label} could not be added to "
                    f"{escape(result.title)} (owner invite and self-join both "
                    f"failed); it sits this group out.[/yellow]"
                )
                continue
            # Anonymity is not optional: a worker that could not be promoted
            # would be credited by name and user id on every video it sent, so
            # it is kept out of the roster rather than allowed to post openly.
            if not await promote_anonymous(owner.client, destination, worker):
                console.print(
                    f"[yellow]{worker.label} is not anonymous here, so it will "
                    f"not post (its id would be visible).[/yellow]"
                )
                continue
            inviters.append(worker)
            roster.append((worker, source_peer, dest_peer))

        now = time.monotonic()
        ready = [item for item in roster if item[0].cooldown_until <= now]
        if not ready:
            if roster:
                console.print(
                    "[yellow]Every worker is cooling down; the owner will post "
                    "this source.[/yellow]"
                )
            elif len(pool) > 1:
                console.print(
                    "[yellow]No worker could reach this source and group; the "
                    "owner will post it.[/yellow]"
                )
            try:
                owner_source = await owner.client.get_input_entity(to_peer(plan.source))
            except (RPCError, ValueError, TypeError) as error:
                plan.error = f"Owner cannot read the source: {error}"
                console.print(f"[red]{escape(plan.error)}[/red]")
                eta.drop_many(size for _id, size in plan.pending)
                dashboard.retotal()
                continue
            if not owner.anonymous:
                console.print(
                    "[yellow]Note: the owner is not anonymous in this group, so "
                    "the videos it posts here will be credited to it.[/yellow]"
                )
            ready = [(owner, owner_source, destination)]

        # Give each poster its own progress row in the live dashboard.
        assigned = [
            (session, source_peer, dest_peer, dashboard.lane(session.label))
            for session, source_peer, dest_peer in ready
        ]
        result.posters = sorted(
            {*result.posters, *(session.label for session, _s, _d, _l in assigned)}
        )
        console.print(
            f"[dim]{escape(plan.title)} · {len(plan.pending)} video(s) · "
            f"posting via {', '.join(s.label for s, _s, _d, _l in assigned)}[/dim]"
        )
        try:
            await copy_plan(
                assigned, plan, temp_dir, state, eta, dashboard, result
            )
        finally:
            for _session, _sp, _dp, lane in assigned:
                dashboard.transfer.remove_task(lane)

    # The work for this group is finished, so turn sending off for members.
    if result.destination is not None and not result.failed:
        result.locked = await apply_member_rights(
            owner.client, destination, allow_sending=False, label="freeze group"
        )
        if result.locked:
            await state.remember_group(brand, {"locked": True})
            console.print(
                f"[bright_magenta]🔒 {escape(result.title)} is now read-only "
                f"for members[/bright_magenta]"
            )
    elif result.failed:
        console.print(
            f"[yellow]{result.failed} video(s) failed, so "
            f"{escape(result.title)} is left open for a rerun.[/yellow]"
        )
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


async def finish_idle_groups(
    owner: Worker, brands: Iterable[str], state: FinalState
) -> int:
    """Freeze any already-finished group that a previous run left open.

    Reached when there is nothing new to copy. A run that was interrupted
    between its last video and the freeze step would otherwise leave a group
    writable forever, since the next run has no work and would skip it. No new
    group is ever created here.
    """
    frozen = 0
    for brand in brands:
        record = state.groups.get(brand)
        if not record or record.get("locked"):
            continue
        try:
            peer = types.InputPeerChannel(
                channel_id=int(record["channel_id"]),
                access_hash=int(record["access_hash"]),
            )
        except (KeyError, TypeError, ValueError):
            continue
        title = str(record.get("title") or brand)
        if await apply_member_rights(
            owner.client, peer, allow_sending=False, label=f"freeze {title}"
        ):
            await state.remember_group(brand, {"locked": True})
            frozen += 1
            console.print(
                f"[bright_magenta]🔒 {escape(title)} is now read-only for "
                f"members[/bright_magenta]"
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
    eta: Eta,
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
    table.add_column("Skipped", justify="right")
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
                f"[dim]took {format_duration(eta.elapsed)} · "
                f"finished {datetime.now().strftime('%H:%M:%S')}[/dim]"
            ),
            border_style=style,
            padding=(1, 3),
        )
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
    pool: list[Worker] = []
    try:
        pool, _api_id, _api_hash = await authenticate()
        owner = pool[0]
        state = FinalState()

        sources = await choose_sources(owner.client, state)
        if not sources:
            raise RuntimeError("No source group was selected.")
        if len(sources) > MAX_GROUPS:
            sources = sources[:MAX_GROUPS]

        console.print("\n[dim]Scanning the selected groups for videos…[/dim]")
        plans = [await build_plan(owner.client, source, state) for source in sources]
        show_plan(plans)

        eta = Eta()
        for plan in plans:
            eta.plan(size for _id, size in plan.pending)
        if not eta.total_videos:
            console.print(
                f"\n[green]Everything is already backed up {HEART}[/green] "
                f"[dim]nothing new to copy[/dim]"
            )
            await finish_idle_groups(
                owner, {plan.brand for plan in plans}, state
            )
            return True
        if not ffmpeg_available():
            console.print(
                "[dim]ffmpeg not found — source previews are reused, but one "
                "cannot be generated for a video that has none.[/dim]"
            )

        # Sibling sources share a destination, so work is grouped by brand and
        # a group is only frozen once every one of its sources is finished.
        by_brand: dict[str, list[Plan]] = {}
        for plan in plans:
            by_brand.setdefault(plan.brand, []).append(plan)

        results: list[GroupResult] = []
        eta.reset_clock()
        with tempfile.TemporaryDirectory(prefix="final-") as temp:
            temp_dir = Path(temp)
            with Dashboard(eta) as dashboard:
                for brand, brand_plans in by_brand.items():
                    results.append(
                        await run_group(
                            pool, brand, brand_plans, temp_dir, state, eta, dashboard
                        )
                    )

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
        return show_report(results, pool, eta, folder)
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
