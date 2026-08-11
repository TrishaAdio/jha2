#!/usr/bin/env python3
"""
Telegram bot: on the FIRST /start, lock onto that user and send them the
~/jha2 folder as a zip (split into parts if larger than Telegram's bot
upload limit). Later users are told the bot is already claimed.

Run:
    export BOT_TOKEN="123456:ABC..."     # from @BotFather
    python3 send_jha2_bot.py

Optional env vars:
    FOLDER      path to send      (default: ~/jha2)
    OWNER_FILE  where the locked   (default: ~/.jha2_bot_owner)
                owner id is stored
"""

import os
import sys
import time
import zipfile
import tempfile
import requests

TOKEN = os.environ.get("BOT_TOKEN", "").strip()
FOLDER = os.path.expanduser(os.environ.get("FOLDER", "~/jha2"))
OWNER_FILE = os.path.expanduser(os.environ.get("OWNER_FILE", "~/.jha2_bot_owner"))

API = f"https://api.telegram.org/bot{TOKEN}"
CHUNK = 45 * 1024 * 1024  # 45 MB per part (under the 50 MB bot limit)


def api(method, **kwargs):
    r = requests.post(f"{API}/{method}", timeout=120, **kwargs)
    r.raise_for_status()
    return r.json()


def send_message(chat_id, text):
    api("sendMessage", data={"chat_id": chat_id, "text": text})


def zip_folder(folder):
    """Zip the folder into a temp file. Returns the zip path."""
    fd, zip_path = tempfile.mkstemp(prefix="jha2_", suffix=".zip")
    os.close(fd)
    base = os.path.dirname(os.path.abspath(folder))
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
        for root, _dirs, files in os.walk(folder):
            for name in files:
                full = os.path.join(root, name)
                # skip the bot's own transient files / broken symlinks
                if not os.path.isfile(full):
                    continue
                arc = os.path.relpath(full, base)
                try:
                    zf.write(full, arc)
                except (OSError, ValueError):
                    pass
    return zip_path


def split_file(path, chunk=CHUNK):
    """Yield (part_path, part_name) pieces of `path` if it's too big."""
    size = os.path.getsize(path)
    if size <= chunk:
        yield path, os.path.basename(path)
        return
    with open(path, "rb") as f:
        idx = 1
        while True:
            data = f.read(chunk)
            if not data:
                break
            part_path = f"{path}.part{idx:03d}"
            with open(part_path, "wb") as pf:
                pf.write(data)
            yield part_path, os.path.basename(part_path)
            idx += 1


def send_folder(chat_id):
    send_message(chat_id, f"Packing {FOLDER} ...")
    zip_path = zip_folder(FOLDER)
    try:
        size = os.path.getsize(zip_path)
        parts = list(split_file(zip_path))
        if len(parts) > 1:
            send_message(
                chat_id,
                f"Archive is {size/1024/1024:.1f} MB, sending in {len(parts)} "
                f"parts. Rejoin with:  cat {os.path.basename(zip_path)}.part* "
                f"> {os.path.basename(zip_path)}",
            )
        for part_path, part_name in parts:
            with open(part_path, "rb") as fh:
                api(
                    "sendDocument",
                    data={"chat_id": chat_id},
                    files={"document": (part_name, fh)},
                )
            if part_path != zip_path:
                os.remove(part_path)
        send_message(chat_id, "Done.")
    finally:
        if os.path.exists(zip_path):
            os.remove(zip_path)


def load_owner():
    if os.path.exists(OWNER_FILE):
        try:
            return int(open(OWNER_FILE).read().strip())
        except ValueError:
            return None
    return None


def save_owner(chat_id):
    with open(OWNER_FILE, "w") as f:
        f.write(str(chat_id))


def main():
    if not TOKEN:
        sys.exit("BOT_TOKEN is not set. Run: export BOT_TOKEN='...'")
    if not os.path.isdir(FOLDER):
        sys.exit(f"Folder not found: {FOLDER}")

    owner = load_owner()
    print(f"Bot up. Folder={FOLDER}  owner={owner}")

    offset = None
    while True:
        try:
            resp = api(
                "getUpdates",
                data={"timeout": 50, "offset": offset} if offset else {"timeout": 50},
            )
        except Exception as e:
            print("getUpdates error:", e)
            time.sleep(3)
            continue

        for upd in resp.get("result", []):
            offset = upd["update_id"] + 1
            msg = upd.get("message") or upd.get("edited_message")
            if not msg:
                continue
            text = (msg.get("text") or "").strip()
            chat_id = msg["chat"]["id"]

            if not text.startswith("/start"):
                continue

            if owner is None:
                owner = chat_id
                save_owner(owner)
                print(f"Locked onto owner {owner}")
                try:
                    send_folder(chat_id)
                except Exception as e:
                    print("send error:", e)
                    send_message(chat_id, f"Failed to send: {e}")
            elif chat_id == owner:
                # owner can re-request
                try:
                    send_folder(chat_id)
                except Exception as e:
                    print("send error:", e)
                    send_message(chat_id, f"Failed to send: {e}")
            else:
                send_message(chat_id, "This bot is already claimed.")


if __name__ == "__main__":
    main()
