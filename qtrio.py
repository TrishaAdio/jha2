"""Multi-account Telegram video mirror that moves media by plain forwarding.

Roles
-----
reader
    One account that is a member of the source groups. It is the only account
    that can see the source history, so it performs every forward.
maker
    One or more accounts that create the destination supergroups, pull the
    reader in, promote it, and hand the group over. Creating a supergroup is
    the most rate-limited call in this whole flow, so the makers take turns and
    a throttled maker is skipped rather than allowed to block the run.

Why this is fast
----------------
Nothing is downloaded and nothing is uploaded. Videos move through
``messages.forwardMessages`` with ``drop_author=True``, which drops the
"Forwarded from" header while the media stays a server-side pointer, so a
2 GB video costs the same as a 2 MB one. Up to ``FORWARD_BATCH`` videos travel
per call, several sources are mirrored concurrently, and the group for the next
source is created while the current one is still forwarding. Throughput is
bound by request pacing rather than by bandwidth.

This is the counterpart to ``telegram_folder_backup.py``: that script
re-uploads bytes so it can beat "restrict saving content", while this one
assumes forwarding is allowed and trades that fallback for raw speed.
"""

from __future__ import annotations

import asyncio
import getpass
import json
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator, Sequence, cast

from rich.align import Align
from rich.markup import escape
from rich.panel import Panel
from rich.prompt import Prompt
from rich.table import Table
from telethon import types, utils
from telethon.errors import (
    ChatForwardsRestrictedError,
    FloodWaitError,
    RPCError,
    UserAlreadyParticipantError,
    UserPrivacyRestrictedError,
)
from telethon.tl.functions import channels, messages

from telegram_folder_backup import (
    HEART,
    MAX_FLOOD_WAIT,
    TITLE_SUFFIX,
    FloodTooLongError,
    Session,
    Target,
    _silence_shutdown_noise,
    ask_links,
    backup_chat_title,
    brand_key,
    console,
    create_backup_folder,
    create_private_group,
    disconnect_client,
    export_private_group_link,
    import_shared_folder,
    join_target_chat,
    login_client,
    pace_joins,
    parse_invite_hash,
    parse_target_list,
    print_named_link,
    promote_workers,
    rpc_call,
    to_peer,
    worker_channel_peer,
)

READER_SESSION = "qtrio_reader"
MAKER_SESSION = "qtrio_maker"
STATE_FILE = ".qtrio_state.json"
# Group-creating accounts. Two is the useful minimum: while one is cooling down
# from a creation FloodWait the other keeps the pipeline moving.
MAX_MAKERS = 8
# Telegram's hard cap on message ids per forwardMessages call. One call moves
# this many videos, which is where nearly all of the speed comes from.
FORWARD_BATCH = 100
# Sources mirrored at the same time. Batches within one source stay sequential
# so the destination keeps the original chronological order; the concurrency is
# across different destinations.
FORWARD_CONCURRENCY = 3
# Groups created ahead of the forwarder. Creation for source N+1 overlaps with
# forwarding of source N, and this bounds how far ahead it may run.
PROVISION_LOOKAHEAD = 2
# Minimum spacing between two group creations, and between two forward calls.
# The forward gap widens on its own whenever Telegram pushes back.
CREATE_INTERVAL = 2.0
FORWARD_INTERVAL = 1.0
MAX_FORWARD_INTERVAL = 30.0
# Total time the run will spend waiting for every maker to leave cooldown
# before it gives up on a source and moves on.
MAX_CREATE_WAIT = 300.0
# Scanned server-side, so the history is never walked message by message.
MEDIA_FILTERS = (
    types.InputMessagesFilterVideo(),
    types.InputMessagesFilterRoundVideo(),
)


@dataclass(slots=True)
class Crew:
    """The logged-in accounts, split by role."""

    reader: Session
    makers: list[Session]
    # Resolving the reader by @username lets a maker invite it without the two
    # accounts ever having shared a chat before.
    reader_username: str | None = None


@dataclass(slots=True)
class Candidate:
    """One group or channel the reader account is already sitting in."""

    entity: types.Chat | types.Channel
    title: str
    kind: str
    mirrored: bool


@dataclass(slots=True)
class Job:
    """One source chat paired with the destination group it mirrors into."""

    index: int
    source: types.Chat | types.Channel
    source_title: str
    source_key: str
    brand: str
    # The reader's own view of both peers. Access hashes are per-account, so
    # the maker's handle on the group is useless to the reader and vice versa.
    source_peer: Any
    destination: Any
    group_title: str
    invite_link: str | None
    done: set[int]


@dataclass(slots=True)
class SourceResult:
    index: int
    source_title: str
    group_title: str
    destination: Any | None = None
    invite_link: str | None = None
    forwarded: int = 0
    already: int = 0
    gone: int = 0
    failed: int = 0
    throttled: bool = False
    error: str | None = None


class QtrioState:
    """Brand-keyed checkpoints so a rerun resumes instead of duplicating.

    Destination groups are keyed by the same ``brand_key`` the backup script
    uses, so sibling sources ("chochlate qt", "chochlate 18+") mirror into one
    group. Forwarded source ids are tracked per source inside each group, which
    keeps de-duplication correct when several sources share a destination.

    ``access_hash`` is always the *reader's* hash: it is the account that
    forwards, so its handle on the group is the one worth persisting.
    """

    def __init__(self) -> None:
        self.path = Path(__file__).resolve().parent / STATE_FILE
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            self.data: dict[str, Any] = raw if isinstance(raw, dict) else {}
        except FileNotFoundError:
            self.data = {}
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"Could not read mirror state: {error}") from error
        self.groups: dict[str, dict[str, Any]] = self.data.setdefault("groups", {})
        # Several sources are mirrored at once, so every mutation is serialized.
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
            raise RuntimeError(f"Could not save mirror state: {error}") from error

    def source_record(self, brand: str, source_key: str, title: str) -> dict[str, Any]:
        group = self.groups.setdefault(brand, {})
        sources = group.setdefault("sources", {})
        return sources.setdefault(source_key, {"title": title, "forwarded": []})

    async def remember(self, brand: str, group: dict[str, Any]) -> None:
        async with self._lock:
            self.groups[brand] = group
            self.save()

    async def mark_forwarded(self, job: Job, message_ids: Sequence[int]) -> None:
        """Record ids as handled and flush, so a crash never re-sends them."""
        async with self._lock:
            job.done.update(message_ids)
            record = self.source_record(job.brand, job.source_key, job.source_title)
            record["title"] = job.source_title
            record["forwarded"] = sorted(job.done)
            self.save()

    async def forget(self, brand: str) -> None:
        async with self._lock:
            self.groups.pop(brand, None)
            self.save()


class Pacer:
    """Minimum gap between forward calls, widened whenever Telegram pushes back.

    Every forwarding task shares one pacer because the limit being respected
    belongs to the reader account, not to any single source.
    """

    def __init__(self, interval: float) -> None:
        self.interval = interval
        self._last = 0.0
        self._lock = asyncio.Lock()

    async def wait(self) -> None:
        async with self._lock:
            gap = self.interval - (time.monotonic() - self._last)
            if gap > 0:
                await asyncio.sleep(gap)
            self._last = time.monotonic()

    def back_off(self) -> None:
        widened = min(self.interval * 2, MAX_FORWARD_INTERVAL)
        if widened > self.interval:
            self.interval = widened
            console.print(
                f"[yellow]Easing off: one forward call every "
                f"{widened:.0f}s from here[/yellow]"
            )


class MakerPool:
    """Round-robin over the group-creating accounts.

    A creation FloodWait pauses only the maker that hit it; the next maker in
    the rotation picks up the same request, so one throttled account costs a
    couple of seconds instead of the whole run.
    """

    def __init__(self, makers: list[Session]) -> None:
        if not makers:
            raise ValueError("At least one maker account is required.")
        self.makers = makers
        self._cursor = 0
        self._last_create = 0.0

    def _rotation(self) -> list[Session]:
        return self.makers[self._cursor :] + self.makers[: self._cursor]

    async def create(self, source_title: str) -> tuple[Session, str, types.Channel]:
        waited = 0.0
        while True:
            now = time.monotonic()
            ready = [maker for maker in self._rotation() if maker.cooldown_until <= now]
            for maker in ready:
                self._cursor = (self.makers.index(maker) + 1) % len(self.makers)
                gap = CREATE_INTERVAL - (time.monotonic() - self._last_create)
                if gap > 0:
                    await asyncio.sleep(gap)
                try:
                    title, channel = await create_private_group(
                        maker.client, source_title
                    )
                except (FloodWaitError, FloodTooLongError) as error:
                    seconds = int(getattr(error, "seconds", MAX_FLOOD_WAIT))
                    maker.cooldown_until = time.monotonic() + seconds
                    self._last_create = time.monotonic()
                    console.print(
                        f"[yellow]{maker.label} is rate-limited on group creation "
                        f"~{seconds}s; handing this one to the next maker[/yellow]"
                    )
                    continue
                self._last_create = time.monotonic()
                return maker, title, channel

            wait = min(maker.cooldown_until for maker in self.makers) - time.monotonic()
            if wait <= 0:
                continue
            if waited + wait > MAX_CREATE_WAIT:
                raise RuntimeError(
                    "Every maker account is rate-limited on group creation; "
                    "progress is saved, so rerun later to resume."
                )
            console.print(
                f"[yellow]All {len(self.makers)} maker account(s) cooling down "
                f"~{int(wait)}s[/yellow]"
            )
            await asyncio.sleep(wait)
            waited += wait


def banner() -> None:
    console.print(
        Panel(
            Align.center(
                "[bold bright_magenta]Q T R I O[/bold bright_magenta]\n"
                "[dim]Forward-only Telegram video mirror · one reader, many "
                "group makers[/dim]"
            ),
            border_style="bright_magenta",
            padding=(1, 4),
        )
    )


def chunked(values: Sequence[int], size: int) -> Iterator[list[int]]:
    for start in range(0, len(values), size):
        yield list(values[start : start + size])


async def authenticate_crew() -> Crew:
    """Log the reader in, then as many makers as the user asks for.

    All sessions share one set of API credentials; each account only needs its
    phone and OTP once, after which its session file on disk is reused.
    """
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
        "\n[bold bright_magenta]Reader account[/bold bright_magenta] "
        "[dim]· the one that is in the source groups[/dim]"
    )
    reader_client, reader_me = await login_client(
        READER_SESSION, api_id, api_hash, "Reader"
    )
    crew = Crew(
        reader=Session(
            client=reader_client,
            label="reader",
            user_id=int(reader_me.id),
            name=utils.get_display_name(reader_me) or "",
        ),
        makers=[],
        reader_username=getattr(reader_me, "username", None),
    )

    count_text = Prompt.ask(
        f"\n[bright_cyan]How many maker accounts (1-{MAX_MAKERS})[/bright_cyan]",
        default="2",
    ).strip()
    count = min(MAX_MAKERS, int(count_text)) if count_text.isdigit() else 2
    count = max(1, count)

    seen = {crew.reader.user_id}
    for number in range(1, count + 1):
        console.print(
            f"\n[bold bright_magenta]Maker {number}[/bold bright_magenta] "
            f"[dim]· creates the destination groups[/dim]"
        )
        try:
            client, me = await login_client(
                f"{MAKER_SESSION}{number}", api_id, api_hash, f"Maker {number}"
            )
        except (RPCError, RuntimeError, ValueError) as error:
            console.print(
                f"[yellow]Maker {number} skipped ({escape(str(error))}).[/yellow]"
            )
            continue
        if int(me.id) in seen:
            console.print(
                f"[yellow]Maker {number} is the same account as another session; "
                f"skipping the duplicate.[/yellow]"
            )
            await disconnect_client(client)
            continue
        seen.add(int(me.id))
        crew.makers.append(
            Session(
                client=client,
                label=f"maker{number}",
                user_id=int(me.id),
                name=utils.get_display_name(me) or "",
            )
        )

    if not crew.makers:
        raise RuntimeError(
            "No maker account could log in, so there is nothing to create the "
            "destination groups."
        )
    console.print(
        f"\n[green]Crew ready:[/green] reader + {len(crew.makers)} maker(s) "
        f"[dim]({', '.join(maker.label for maker in crew.makers)})[/dim]"
    )
    return crew


def mirror_channel_ids(state: QtrioState) -> set[int]:
    """Channel ids this tool created, so they are never mirrored into again."""
    ids: set[int] = set()
    for group in state.groups.values():
        try:
            ids.add(int(group["channel_id"]))
        except (KeyError, TypeError, ValueError):
            continue
    return ids


def is_own_output(title: str, peer_id: int, made_ids: set[int]) -> bool:
    """True for a group this tool (or the backup script) produced.

    Without this the reader's own destination groups show up as sources and the
    run mirrors its output back into itself. Ids cover this tool's groups; the
    title suffix also catches groups made by ``telegram_folder_backup.py``.
    """
    if peer_id in made_ids:
        return True
    return title.rstrip().endswith(TITLE_SUFFIX.strip())


async def fetch_reader_groups(crew: Crew, state: QtrioState) -> list[Candidate]:
    """List every group and channel the reader account is already a member of.

    Telegram returns dialogs most-recent-first, and that order is kept, so the
    chats worth mirroring tend to be at the top of the list.
    """
    made_ids = mirror_channel_ids(state)
    candidates: list[Candidate] = []
    seen: set[int] = set()
    console.print("[dim]Reading the reader account's chat list…[/dim]")
    async for dialog in crew.reader.client.iter_dialogs():
        entity = dialog.entity
        # Users and bots are not sources; forbidden and dead chats cannot be read.
        if not isinstance(entity, (types.Chat, types.Channel)):
            continue
        if getattr(entity, "deactivated", False):
            continue
        peer_id = utils.get_peer_id(entity)
        if peer_id in seen:
            continue
        title = utils.get_display_name(entity) or f"Chat {peer_id}"
        if is_own_output(title, int(getattr(entity, "id", 0)), made_ids):
            continue
        seen.add(peer_id)
        if isinstance(entity, types.Channel) and not entity.megagroup:
            kind = "channel"
        else:
            kind = "group"
        candidates.append(
            Candidate(
                entity=entity,
                title=title,
                kind=kind,
                mirrored=brand_key(title) in state.groups,
            )
        )
    return candidates


def show_candidates(candidates: Sequence[Candidate]) -> None:
    table = Table(
        title=f"Groups the reader is in ({len(candidates)})",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("#", justify="right")
    table.add_column("Title")
    table.add_column("Kind")
    table.add_column("Mirrored")
    for number, candidate in enumerate(candidates, start=1):
        table.add_row(
            str(number),
            escape(candidate.title),
            candidate.kind,
            "yes" if candidate.mirrored else "-",
        )
    console.print(table)


def parse_selection(raw: str, count: int) -> list[int]:
    """Turn "all" or "1,4,7-12" into zero-based indexes, order preserved."""
    cleaned = raw.strip().lower()
    if not cleaned or cleaned in {"all", "*"}:
        return list(range(count))
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
    return ordered


async def choose_sources(
    crew: Crew, state: QtrioState
) -> list[types.Chat | types.Channel]:
    """Pick sources from the reader's own chat list, or from pasted links."""
    console.print("\n[bold bright_magenta]Sources[/bold bright_magenta]")
    try:
        candidates = await fetch_reader_groups(crew, state)
    except (RPCError, RuntimeError) as error:
        console.print(
            f"[yellow]Could not read the reader's chat list "
            f"({escape(str(error))}); paste links instead.[/yellow]"
        )
        return await sources_from_links(crew)

    if not candidates:
        console.print(
            "[yellow]The reader account is not in any group or channel yet."
            "[/yellow]"
        )
        return await sources_from_links(crew)

    show_candidates(candidates)
    while True:
        raw = Prompt.ask(
            "[bright_cyan]Which ones[/bright_cyan] [dim]· all · 1,4,7-12 · "
            "'links' to paste links instead[/dim]",
            default="all",
        ).strip()
        if raw.lower() in {"links", "link", "paste"}:
            return await sources_from_links(crew)
        try:
            picked = parse_selection(raw, len(candidates))
        except ValueError as error:
            console.print(f"[yellow]{escape(str(error))}[/yellow]")
            continue
        return [candidates[index].entity for index in picked]


async def sources_from_links(crew: Crew) -> list[types.Chat | types.Channel]:
    """The original path: paste links and let the reader join them."""
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
    return await collect_sources(crew, targets)


async def collect_sources(
    crew: Crew, targets: Sequence[Target]
) -> list[types.Chat | types.Channel]:
    """Join every pasted link with the reader and flatten it into source chats.

    Only the reader joins: it is the account that reads the history, and
    keeping the makers out of the sources leaves them clean.
    """
    client = crew.reader.client
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
                entity = await join_target_chat(client, target, "Reader")
                found = [entity]
                name = utils.get_display_name(entity) or target.label
                console.print(f"[green]Joined:[/green] [bold]{escape(name)}[/bold]")
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
    return sources


async def invite_reader(maker: Session, crew: Crew, channel_id: int) -> bool:
    """Have the maker pull the reader into the group it just created.

    Tries the maker's own cache first, then an @username resolve. After the
    first shared group the cache is warm, so later invites need no resolve at
    all. Returns ``False`` when only a self-join can work.
    """
    client = maker.client
    try:
        channel = cast(
            Any,
            utils.get_input_channel(
                await client.get_input_entity(types.PeerChannel(channel_id))
            ),
        )
    except (RPCError, ValueError, TypeError):
        return False

    handles: list[int | str] = [crew.reader.user_id]
    if crew.reader_username:
        handles.append(crew.reader_username)
    for handle in handles:
        try:
            user = cast(
                Any, utils.get_input_user(await client.get_input_entity(handle))
            )
        except (RPCError, ValueError, TypeError):
            continue
        try:
            await client(
                channels.InviteToChannelRequest(channel=channel, users=[user])
            )
            return True
        except UserAlreadyParticipantError:
            return True
        except UserPrivacyRestrictedError:
            # The reader blocks being added by anyone; only a self-join works.
            return False
        except (FloodWaitError, RPCError):
            continue
    return False


async def attach_reader(
    maker: Session, crew: Crew, channel_id: int, invite_link: str | None
) -> Any | None:
    """Get the reader into the group and return the reader's own peer handle."""
    if not await invite_reader(maker, crew, channel_id) and invite_link:
        # Falling back to a join is rate-limited, so it is paced like every
        # other join this project makes.
        await pace_joins()
        try:
            await crew.reader.client(
                messages.ImportChatInviteRequest(parse_invite_hash(invite_link))
            )
        except UserAlreadyParticipantError:
            pass
        except FloodWaitError as error:
            console.print(
                f"[yellow]Reader cannot join right now "
                f"({int(error.seconds)}s rate limit)[/yellow]"
            )
            return None
        except (RPCError, RuntimeError):
            return None
    return await worker_channel_peer(crew.reader.client, channel_id, invite_link)


async def reuse_group(
    crew: Crew, record: dict[str, Any]
) -> tuple[Any, str, str | None] | None:
    """Re-open a destination saved by an earlier run, or ``None`` if it is gone."""
    try:
        peer = types.InputPeerChannel(
            channel_id=int(record["channel_id"]),
            access_hash=int(record["access_hash"]),
        )
    except (KeyError, TypeError, ValueError):
        return None
    try:
        await rpc_call(
            "verify saved group", lambda: crew.reader.client.get_entity(peer)
        )
    except (RPCError, RuntimeError, ValueError):
        return None
    title = str(record.get("title") or "")
    link = record.get("invite_link")
    return peer, title, link if isinstance(link, str) else None


async def provision_source(
    crew: Crew,
    pool: MakerPool,
    source: types.Chat | types.Channel,
    state: QtrioState,
    index: int,
    total: int,
) -> Job:
    """Pair one source with a destination group, creating it when needed."""
    source_title = utils.get_display_name(source) or f"Chat {utils.get_peer_id(source)}"
    source_key = str(utils.get_peer_id(source))
    brand = brand_key(source_title)
    group_title = backup_chat_title(source_title)

    destination: Any | None = None
    invite_link: str | None = None
    record = state.groups.get(brand)
    if record:
        reused = await reuse_group(crew, record)
        if reused is None:
            console.print(
                f"[yellow]Saved group for '{escape(brand)}' is unavailable; "
                f"creating a new one.[/yellow]"
            )
            await state.forget(brand)
        else:
            destination, saved_title, invite_link = reused
            group_title = saved_title or group_title
            console.print(
                f"[bright_cyan]Reusing[/bright_cyan] [bold]{escape(group_title)}"
                f"[/bold] for [bold]{escape(source_title)}[/bold]"
            )

    if destination is None:
        maker, group_title, created = await pool.create(source_title)
        if created.access_hash is None:
            raise RuntimeError("The new group came back without an access hash.")
        try:
            invite_link = await export_private_group_link(maker.client, created)
        except (RPCError, RuntimeError) as error:
            invite_link = None
            console.print(
                f"[yellow]{maker.label} created the group but its invite link "
                f"failed: {escape(str(error))}[/yellow]"
            )
        destination = await attach_reader(maker, crew, created.id, invite_link)
        if destination is None:
            raise RuntimeError(
                f"{maker.label} created '{group_title}' but the reader could not "
                f"be added, so nothing can be forwarded into it."
            )
        # Admin rights keep the reader clear of slow mode and any future
        # restriction on the group it does not own.
        await promote_workers(maker.client, created, [crew.reader])
        await state.remember(
            brand,
            {
                "title": group_title,
                "channel_id": int(created.id),
                # Persist the reader's hash: it is the account that forwards.
                "access_hash": int(getattr(destination, "access_hash", 0) or 0),
                "invite_link": invite_link,
                "made_by": maker.label,
                "sources": (state.groups.get(brand) or {}).get("sources", {}),
            },
        )
        console.print(
            f"[green]{maker.label} created[/green] [bold]{escape(group_title)}[/bold] "
            f"[dim]· reader attached[/dim]"
        )

    if invite_link:
        print_named_link(group_title, invite_link)

    source_peer = await crew.reader.client.get_input_entity(to_peer(source))
    record = state.source_record(brand, source_key, source_title)
    done = {int(value) for value in record.get("forwarded", [])}
    console.print(
        f"[dim]{index}/{total} queued · {escape(source_title)} → "
        f"{escape(group_title)}[/dim]"
    )
    return Job(
        index=index,
        source=source,
        source_title=source_title,
        source_key=source_key,
        brand=brand,
        source_peer=source_peer,
        destination=destination,
        group_title=group_title,
        invite_link=invite_link,
        done=done,
    )


async def pending_video_ids(crew: Crew, job: Job) -> list[int]:
    """Server-side scan for videos this source has not sent over yet.

    Telegram does the filtering, so the whole history is never walked. Ids come
    back ascending so the destination ends up in the original order.
    """
    found: set[int] = set()
    for media_filter in MEDIA_FILTERS:
        async for message in crew.reader.client.iter_messages(
            job.source, reverse=True, filter=media_filter
        ):
            if message.id in job.done or message.id in found:
                continue
            if not getattr(message, "video", None):
                continue
            found.add(message.id)
    return sorted(found)


async def forward_batch(crew: Crew, job: Job, ids: Sequence[int], pacer: Pacer) -> int:
    """Forward one batch and return how many messages actually landed.

    ``drop_author`` is what hides the original sender; captions are left alone.
    ``silent`` keeps a few hundred forwards from ringing every member's phone.
    """
    await pacer.wait()
    sent = cast(
        Any,
        await rpc_call(
            f"forward {len(ids)} → {job.group_title}",
            lambda: crew.reader.client.forward_messages(
                job.destination,
                list(ids),
                from_peer=job.source_peer,
                drop_author=True,
                silent=True,
            ),
        ),
    )
    if sent is None:
        return 0
    if not isinstance(sent, (list, tuple)):
        return 1
    return sum(1 for message in sent if message is not None)


async def forward_source(
    crew: Crew, job: Job, state: QtrioState, pacer: Pacer
) -> SourceResult:
    """Mirror every pending video of one source, in batches, in order."""
    result = SourceResult(
        index=job.index,
        source_title=job.source_title,
        group_title=job.group_title,
        destination=job.destination,
        invite_link=job.invite_link,
        already=len(job.done),
    )
    try:
        pending = await pending_video_ids(crew, job)
    except (FloodWaitError, FloodTooLongError) as error:
        result.throttled = True
        result.error = f"Scan throttled: {error}"
        console.print(f"[yellow]{escape(result.error)}[/yellow]")
        return result
    except (RPCError, RuntimeError, ValueError) as error:
        result.error = f"Scan failed: {error}"
        console.print(f"[red]{escape(result.error)}[/red]")
        return result

    if not pending:
        console.print(
            f"[dim]{escape(job.source_title)} · nothing new "
            f"({result.already} already mirrored)[/dim]"
        )
        return result

    console.print(
        f"[bright_cyan]{escape(job.source_title)}[/bright_cyan] · "
        f"{len(pending)} new video(s) → [bold]{escape(job.group_title)}[/bold]"
    )
    for batch in chunked(pending, FORWARD_BATCH):
        try:
            sent = await forward_batch(crew, job, batch, pacer)
        except ChatForwardsRestrictedError:
            result.error = (
                "This chat restricts forwarding; use telegram_folder_backup.py, "
                "which re-uploads instead."
            )
            console.print(f"[red]{escape(job.source_title)}: {result.error}[/red]")
            break
        except (FloodWaitError, FloodTooLongError) as error:
            seconds = int(getattr(error, "seconds", MAX_FLOOD_WAIT))
            pacer.back_off()
            result.throttled = True
            console.print(
                f"[yellow]Reader throttled ~{seconds}s on "
                f"{escape(job.group_title)}; progress saved, rerun to "
                f"finish[/yellow]"
            )
            break
        except (RPCError, RuntimeError, ValueError) as error:
            # One unforwardable message must not sink the other 99, so the
            # batch is retried id by id.
            console.print(
                f"[yellow]Batch of {len(batch)} failed ({escape(str(error))}); "
                f"retrying one by one[/yellow]"
            )
            sent = 0
            batch_failed = 0
            landed: list[int] = []
            for message_id in batch:
                try:
                    sent += await forward_batch(crew, job, [message_id], pacer)
                    landed.append(message_id)
                except (FloodWaitError, FloodTooLongError):
                    pacer.back_off()
                    result.throttled = True
                    break
                except (RPCError, RuntimeError, ValueError):
                    # Deleted or otherwise unreachable: bank it so later runs
                    # do not keep retrying it forever.
                    batch_failed += 1
                    landed.append(message_id)
            result.forwarded += sent
            result.failed += batch_failed
            result.gone += max(0, len(landed) - sent - batch_failed)
            await state.mark_forwarded(job, landed)
            if result.throttled:
                break
            continue

        result.forwarded += sent
        result.gone += len(batch) - sent
        await state.mark_forwarded(job, batch)
        console.print(
            f"  [green]✓[/green] {sent}/{len(batch)} forwarded "
            f"[dim]· {escape(job.group_title)}[/dim]"
        )
    return result


async def mirror_sources(
    crew: Crew,
    pool: MakerPool,
    sources: Sequence[types.Chat | types.Channel],
    state: QtrioState,
) -> list[SourceResult]:
    """Run provisioning and forwarding as two overlapping stages.

    The single provisioning task walks the sources in order and pushes ready
    jobs onto a short queue; the forwarding tasks drain it. That way the group
    for the next source is being created while the current one is still moving
    videos, and neither stage waits on the other.
    """
    queue: asyncio.Queue[Job | None] = asyncio.Queue(maxsize=PROVISION_LOOKAHEAD)
    results: list[SourceResult] = []
    pacer = Pacer(FORWARD_INTERVAL)
    total = len(sources)
    workers = max(1, min(FORWARD_CONCURRENCY, total))

    async def provision_stage() -> None:
        for index, source in enumerate(sources, start=1):
            title = (
                utils.get_display_name(source) or f"Chat {utils.get_peer_id(source)}"
            )
            try:
                job = await provision_source(crew, pool, source, state, index, total)
            except (RPCError, RuntimeError, ValueError, TypeError) as error:
                console.print(
                    f"[red]No group for '{escape(title)}':[/red] "
                    f"{escape(str(error))}"
                )
                results.append(
                    SourceResult(
                        index=index,
                        source_title=title,
                        group_title=backup_chat_title(title),
                        error=str(error),
                    )
                )
                continue
            await queue.put(job)
        for _ in range(workers):
            await queue.put(None)

    async def forward_stage() -> None:
        while True:
            job = await queue.get()
            if job is None:
                return
            results.append(await forward_source(crew, job, state, pacer))

    await asyncio.gather(
        provision_stage(), *(forward_stage() for _ in range(workers))
    )
    results.sort(key=lambda item: item.index)
    return results


def result_status(result: SourceResult) -> str:
    if result.destination is None:
        return "group failed"
    if result.error:
        return "stopped"
    if result.throttled:
        return "throttled"
    if result.failed:
        return "partial"
    return "complete"


def show_summary(
    results: list[SourceResult], folder_title: str, link: str | None
) -> bool:
    complete = bool(results) and all(
        result_status(result) == "complete" for result in results
    )
    table = Table(
        title="Mirror report",
        border_style="bright_magenta",
        header_style="bold bright_magenta",
    )
    table.add_column("Source")
    table.add_column("Group")
    table.add_column("Forwarded", justify="right")
    table.add_column("Already", justify="right")
    table.add_column("Gone", justify="right")
    table.add_column("Status")
    for result in results:
        table.add_row(
            escape(result.source_title),
            escape(result.group_title) if result.destination else "Not created",
            str(result.forwarded),
            str(result.already),
            str(result.gone + result.failed),
            result_status(result),
        )
    console.print("\n", table)

    linked = [
        result
        for result in results
        if result.invite_link and result.destination is not None
    ]
    if linked:
        console.print("[bold bright_magenta]Group links[/bold bright_magenta]")
        seen: set[str] = set()
        for result in linked:
            assert result.invite_link is not None
            if result.invite_link in seen:
                continue
            seen.add(result.invite_link)
            print_named_link(result.group_title, result.invite_link)
        console.print()

    label = "MIRROR COMPLETE" if complete else "MIRROR PARTIAL"
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
    if link:
        print_named_link(folder_title, link, folder=True)
    return complete


async def run() -> bool:
    banner()
    _silence_shutdown_noise()
    crew: Crew | None = None
    try:
        crew = await authenticate_crew()

        # Loaded before the sources are picked so the groups this tool already
        # made can be filtered out of the reader's chat list.
        state = QtrioState()

        sources = await choose_sources(crew, state)
        if not sources:
            raise RuntimeError("No source chat was selected.")
        console.print(
            f"\n[green]{len(sources)} source chat(s) ready[/green] "
            f"[dim]· forwarding with the sender name hidden[/dim]"
        )

        pool = MakerPool(crew.makers)
        results = await mirror_sources(crew, pool, sources, state)

        # One folder over every destination, de-duplicated because sibling
        # sources share a group.
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

        folder_title = "ᴍɪʀʀᴏʀ"
        link: str | None = None
        if destinations:
            try:
                folder_title, link = await create_backup_folder(
                    crew.reader.client,
                    results[0].source_title if results else "mirror",
                    destinations,
                )
            except (RPCError, RuntimeError) as error:
                console.print(
                    f"[yellow]Groups are ready but the folder could not be "
                    f"created: {escape(str(error))}[/yellow]"
                )
        return show_summary(results, folder_title, link)
    finally:
        if crew is not None:
            for session in [crew.reader, *crew.makers]:
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
                f"[bold red]Mirror stopped[/bold red]\n{escape(str(error))}",
                border_style="red",
            )
        )
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
