"""
RiotHub
=======
One-click Riot account switching, an instant game launcher and a full VALORANT companion.
RiotHub isn't endorsed by Riot Games and doesn't reflect the views or opinions of Riot
Games or anyone officially involved in producing or managing Riot Games properties.

Switching works like TcNo: no passwords are stored or typed. The app saves the
Riot Client's own "Stay signed in" login files per account and swaps them in.

Features
  Accounts     tiles or list, drag to reorder, tags/notes, hotkeys, tray,
               desktop shortcuts, expired-login detection, playtime tracking
  Profile      rank, peak, RR graph, battle pass, penalties, match history,
               inventory (equip skins/cards/titles), collections, inventory value,
               full match scoreboards with round-by-round results, leaderboard
  Store        daily store, night market and bundles for every account,
               wishlist with Windows notifications
  Live         agent select / in-game lobby ranks, peaks, levels, your party,
               "played with before" (hidden names stay hidden), click anyone to
               see their full skin loadout, leave match from agent select,
               mini agent picker with favourites
  Loadout      equip skins, skin roulette, presets you can apply across accounts
  Compare      every account side by side
  Friends      friends list with online alerts, VALORANT server status
  League       LoL / TFT rank and champion mastery when the League client is open
  Extras       mini always-on-top overlay, OBS rank overlay, PIN lock, weekly
               encrypted backups, TcNo import, custom background
  Sync         copy crosshair / keybinds / sensitivity, crosshair library
  Status       appear offline / mobile (experimental built-in chat proxy,
               or hand off to Deceive.exe)
  Settings     themes, layouts, streamer mode, background refresh,
               password-protected backup / restore

Recommended extras:   py -m pip install pillow pystray
Data lives in %APPDATA%\\RiotHub

VALORANT data comes from Riot's unofficial in-game API and valorant-api.com.
It only ever reads/changes data of accounts you log into yourself.
"""

import base64
import csv
import ctypes
import hashlib
import hmac
import io
import itertools
import json
import os
import queue
import re
import math
import ntpath
import secrets
import shutil
import socket
import ssl
import subprocess
import sys
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import zipfile
import zlib
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

try:
    from tkinter import filedialog
except Exception:  # pragma: no cover
    filedialog = None
try:
    from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageOps, ImageTk
    HAS_PIL = True
except Exception:
    HAS_PIL = False
try:
    import pystray
    HAS_TRAY = HAS_PIL
except Exception:
    HAS_TRAY = False

APP_NAME = "RiotHub"
OLD_APP_NAMES = ["RiotAccountSwitcher"]      # data folders from before the rename
VERSION = "1.3.4"   # stamped from the release tag by the GitHub workflow
APP_TITLE = "RiotHub"
# GitHub "owner/repo" whose releases this app updates from. Leave empty to turn updates off.
UPDATE_REPO = ""

# ================================================================ paths / constants
LOCAL = Path(os.environ.get("LOCALAPPDATA", ""))
RIOT_DIR = LOCAL / "Riot Games" / "Riot Client"
LOCKFILE = RIOT_DIR / "Config" / "lockfile"
LOGIN_ITEMS = [
    "Data/Cookies",
    "Data/Sessions",
    "Data/RiotClientPrivateSettings.yaml",
    "Data/RiotGamesPrivateSettings.yaml",
    "Config/RiotClientSettings.yaml",
]
SESSION_MARKERS = ["Data/RiotClientPrivateSettings.yaml", "Data/RiotGamesPrivateSettings.yaml",
                   "Data/Sessions"]
INSTALLS_JSON = (Path(os.environ.get("PROGRAMDATA", r"C:\ProgramData"))
                 / "Riot Games" / "RiotClientInstalls.json")
APP_DIR = Path(os.environ.get("APPDATA", "")) / APP_NAME


def migrate_old_data():
    """Move saved accounts/settings from the old app name, once."""
    if APP_DIR.exists():
        return
    for old in OLD_APP_NAMES:
        src = APP_DIR.with_name(old)
        if src.is_dir():
            try:
                src.rename(APP_DIR)
            except OSError:
                try:
                    shutil.copytree(src, APP_DIR)
                except Exception:
                    pass
            return


migrate_old_data()
ACC_DIR = APP_DIR / "accounts"
META_DIR = APP_DIR / "meta"
PREFS_DIR = APP_DIR / "prefs"
PREFS_BACKUP_DIR = APP_DIR / "prefs_backups"
CACHE_DIR = APP_DIR / "cache"
MATCH_DIR = CACHE_DIR / "matches"
IMG_DIR = CACHE_DIR / "img"
VIDEO_DIR = CACHE_DIR / "video"
ICON_DIR = APP_DIR / "icons"
BACKUP_DIR = APP_DIR / "_last_backup"
STATE = APP_DIR / "state.json"
IPC_PORT = 47821

CLIENT_PROCS = ["RiotClientServices.exe", "RiotClientUx.exe", "RiotClientUxRender.exe",
                "Riot Client.exe", "RiotClientCrashHandler.exe",
                "LeagueClient.exe", "LeagueClientUx.exe", "LeagueClientUxRender.exe"]
GAME_PROCS = ["League of Legends.exe", "VALORANT-Win64-Shipping.exe", "LoR.exe",
              "Lion-Win64-Shipping.exe"]
GAMES = {
    "VALORANT": "valorant",
    "League / TFT": "league_of_legends",
    "Runeterra": "bacon",
    "2XKO": "lion",
    "Client only": None,
}
GAME_EXE = {"valorant": "VALORANT-Win64-Shipping.exe", "league_of_legends": "League of Legends.exe",
            "bacon": "LoR.exe", "lion": "Lion-Win64-Shipping.exe"}
METADATA_DIR = Path(os.environ.get("PROGRAMDATA", r"C:\ProgramData")) / "Riot Games" / "Metadata"


def installed_games():
    """Games from GAMES that the Riot Client has installed (all of them if we can't tell)."""
    try:
        have = {p.name.split(".")[0].lower() for p in METADATA_DIR.iterdir() if p.is_dir()}
    except Exception:
        have = None
    out = []
    for g, prod in GAMES.items():
        if prod is None or have is None or not have or prod in have:
            out.append(g)
    return out
DECEIVE_ARG = {"valorant": "valorant", "league_of_legends": "lol", "bacon": "lor"}
NO_WINDOW = 0x08000000 if os.name == "nt" else 0

ITEM_TYPES = {
    "skins": "e7c63390-eda7-46e0-bb7a-a6abdacd2433",
    "chromas": "3ad1b2b2-acdb-4524-852f-954a76ddae0a",
    "buddies": "dd3bf334-87f3-40bd-b043-682a57a8dc3a",
    "cards": "3f296c07-64c3-494c-923b-fe692a4fa1bd",
    "sprays": "d5f120f8-ff8c-4aac-92ea-f2b5acbe9475",
    "titles": "de7caa6b-adf7-4588-bbd1-143831e786c6",
    "agents": "01bb38e1-da47-4e6a-9b3d-945fe4655707",
}
VP = "85ad13f7-3d1b-5128-9eb2-7cd8ee0b5741"
CURRENCIES = [("VP", VP),
              ("Radianite", "e59aa87c-4cbf-517a-5983-6e81511be9b7"),
              ("Kingdom", "85ca954a-41f2-ce94-9b45-8ca3dd39a00d")]
REGION_TO_SHARD = {"na": "na", "latam": "na", "br": "na", "eu": "eu", "ap": "ap", "kr": "kr"}
SHARD_PREFS = {"na": "usw2", "eu": "euc1", "ap": "apse1", "kr": "apne1"}
LOL_TO_VAL = {"EUW": "eu", "EUNE": "eu", "TR": "eu", "RU": "eu", "ME1": "eu", "NA": "na",
              "NA1": "na", "LA1": "latam", "LA2": "latam", "LAN": "latam", "LAS": "latam",
              "BR": "br", "BR1": "br", "KR": "kr", "JP": "ap", "OC": "ap", "OCE": "ap",
              "PH": "ap", "SG": "ap", "TH": "ap", "TW": "ap", "VN": "ap", "SEA": "ap"}
REGIONS = ["Auto", "eu", "na", "ap", "kr", "latam", "br"]
CLIENT_PLATFORM = base64.b64encode(json.dumps({
    "platformType": "PC", "platformOS": "Windows",
    "platformOSVersion": "10.0.19042.1.256.64bit", "platformChipset": "Unknown"}).encode()).decode()
WEAPON_ORDER = ["Vandal", "Phantom", "Operator", "Sheriff", "Classic", "Ghost", "Spectre",
                "Melee", "Guardian", "Marshal", "Outlaw", "Bulldog", "Stinger", "Frenzy",
                "Shorty", "Judge", "Bucky", "Ares", "Odin"]
QUEUES = {"competitive": "Competitive", "unrated": "Unrated", "swiftplay": "Swiftplay",
          "spikerush": "Spike Rush", "deathmatch": "Deathmatch", "ggteam": "Escalation",
          "onefa": "Replication", "hurm": "Team Deathmatch", "premier": "Premier",
          "newmap": "New Map", "snowball": "Snowball Fight", "": "Custom"}
UA = f"RiotHub/{VERSION}"

# ================================================================ theme
THEMES = {
    #           accent     accent_hi  soft       glow       brand
    "Violet":  ("#7b4cff", "#946dff", "#b9a4ff", "#3b157a", "#2c1059"),
    "Crimson": ("#ff4655", "#ff6b78", "#ffb3ba", "#5a1220", "#3d0a14"),
    "Ocean":   ("#2f8cff", "#55a2ff", "#a8cfff", "#0f3570", "#0a2550"),
    "Emerald": ("#16b877", "#2fd18f", "#9ff0cc", "#0d4d36", "#083a29"),
    "Sunset":  ("#ff7a2f", "#ff9555", "#ffd0ad", "#5c2a10", "#3e1c0a"),
    "Rose":    ("#e0458f", "#ee67a6", "#f8b6d5", "#55163a", "#3a0f28"),
    "Mono":    ("#7d7d92", "#9696ab", "#d4d4e0", "#262630", "#1c1c24"),
}
BG = "#07060c"
BAR = "#0b0913"
SURFACE = "#110d1d"
CARD = "#1a1430"
CARD_HI = "#251c45"
LINE = "#231a3d"
BRAND = "#2c1059"
GLOW = "#3b157a"
ACCENT = "#7b4cff"
ACCENT_HI = "#946dff"
SOFT = "#b9a4ff"
TEXT = "#f4f0fb"
MUTED = "#9a90b4"
DIM = "#5d5478"
DANGER = "#ff5c7a"
GOOD = "#3ddc97"
GOLD = "#f5c451"
LABEL_COLORS = ["#ff4655", "#ff9a3c", "#f5c451", "#3ddc97", "#2fb7ff", "#7b4cff", "#e0458f",
                "#c9c9d6"]
AVATARS = ["#5a2bd1", "#8a2be2", "#b0379f", "#3f2ab8", "#6d28d9", "#c0266b",
           "#2f3fc4", "#7e22ce", "#9d3cc9", "#4c1d95"]


def mix(a, b, t):
    a = [int(a[i:i + 2], 16) for i in (1, 3, 5)]
    b = [int(b[i:i + 2], 16) for i in (1, 3, 5)]
    return "#" + "".join(f"{max(0, min(255, round(x + (y - x) * t))):02x}" for x, y in zip(a, b))


def custom_palette(hexcol):
    return (hexcol, mix(hexcol, "#ffffff", 0.16), mix(hexcol, "#ffffff", 0.55),
            mix(hexcol, "#000000", 0.55), mix(hexcol, "#000000", 0.7))


def apply_theme(name):
    """Swap the palette. Surfaces get a faint tint of the accent too."""
    global ACCENT, ACCENT_HI, SOFT, GLOW, BRAND, SURFACE, CARD, CARD_HI, LINE, BAR, MUTED, DIM
    ACCENT, ACCENT_HI, SOFT, GLOW, BRAND = THEMES.get(name, THEMES["Violet"])
    base = "#0d0c12"
    SURFACE = mix(base, BRAND, 0.35)
    CARD = mix("#16151d", BRAND, 0.45)
    CARD_HI = mix("#1f1d29", GLOW, 0.45)
    LINE = mix("#1b1a24", BRAND, 0.45)
    BAR = mix("#0a0a0e", BRAND, 0.12)
    MUTED = mix("#9893a6", SOFT, 0.18)
    DIM = mix("#5a5668", SOFT, 0.12)


def avatar_color(name):
    return AVATARS[sum(map(ord, name)) % len(AVATARS)]


# ================================================================ login files
ACC_GEN = [0]      # bumped whenever saved logins change, so App.accounts() re-reads


def _rm(p: Path):
    ACC_GEN[0] += 1
    if p.is_dir():
        shutil.rmtree(p, ignore_errors=True)
    elif p.exists():
        p.unlink(missing_ok=True)


def _cp(src: Path, dst: Path):
    if not src.exists():
        return
    dst.parent.mkdir(parents=True, exist_ok=True)
    _rm(dst)
    if src.is_dir():
        shutil.copytree(src, dst)
    else:
        shutil.copy2(src, dst)


def has_login(root: Path) -> bool:
    for m in SESSION_MARKERS:
        p = root / m
        if p.is_file() and p.stat().st_size > 0:
            return True
        if p.is_dir() and any(p.iterdir()):
            return True
    return False


def login_fingerprint(root: Path):
    """Changes whenever Riot rewrites the sign-in files."""
    h = hashlib.sha1()
    for item in LOGIN_ITEMS:
        p = root / item
        if p.is_file():
            try:
                h.update(p.read_bytes())
            except OSError:
                pass
    return h.hexdigest()


PREV_DIR_NAME = "_previous_login"


def snapshot(dst_root: Path, keep_prev=True):
    ACC_GEN[0] += 1
    try:
        return _snapshot(dst_root, keep_prev)
    finally:
        ACC_GEN[0] += 1      # again once the folder really exists


def _snapshot(dst_root: Path, keep_prev=True):
    if keep_prev and dst_root.parent == ACC_DIR and has_login(dst_root):
        prev = APP_DIR / PREV_DIR_NAME / dst_root.name
        try:
            _rm(prev)
            prev.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(dst_root, prev)
        except Exception:
            pass
    tmp = dst_root.with_name(dst_root.name + ".tmp")
    _rm(tmp)
    tmp.mkdir(parents=True, exist_ok=True)
    for item in LOGIN_ITEMS:
        _cp(RIOT_DIR / item, tmp / item)
    if dst_root.parent == ACC_DIR and has_login(dst_root) and not has_login(tmp):
        _rm(tmp)
        raise RuntimeError("The Riot Client has no saved sign-in to copy.")
    _rm(dst_root)
    if dst_root.exists():
        shutil.copytree(tmp, dst_root, dirs_exist_ok=True)
        _rm(tmp)
    else:
        tmp.rename(dst_root)


def clear_login():
    for item in LOGIN_ITEMS:
        _rm(RIOT_DIR / item)


def restore(src_root: Path):
    clear_login()
    for item in LOGIN_ITEMS:
        _cp(src_root / item, RIOT_DIR / item)


# ================================================================ processes
def running_processes():
    try:
        out = subprocess.run(["tasklist", "/FO", "CSV", "/NH"], capture_output=True,
                             text=True, creationflags=NO_WINDOW).stdout
        return {row[0].lower() for row in csv.reader(io.StringIO(out)) if row}
    except Exception:
        return set()


def games_running(procs=None):
    r = procs if procs is not None else running_processes()
    return [p.replace(".exe", "").replace("-Win64-Shipping", "") for p in GAME_PROCS
            if p.lower() in r]


def quit_client_gracefully(wait=8):
    """Ask the Riot Client to quit itself (it saves its refreshed sign-in on the way out).
    Returns True if every client process was gone within `wait` seconds."""
    lf = read_lockfile()
    if not lf:
        return False
    try:
        local_get(lf, "/process-control/v1/process/quit", "POST", timeout=4)
    except Exception:
        return False
    wanted = {p.lower() for p in CLIENT_PROCS}
    end = time.time() + wait
    while time.time() < end:
        time.sleep(0.4)
        if not (running_processes() & wanted):
            return True
    return False


def close_client(timeout=15, allow_prompt=True):
    quit_client_gracefully()
    wanted = {p.lower() for p in CLIENT_PROCS}

    def kill(names):
        for p in names:
            subprocess.run(["taskkill", "/F", "/T", "/IM", p], capture_output=True,
                           creationflags=NO_WINDOW)

    def gone(wait, rekill=False):
        end = time.time() + wait
        last_kill = time.time()
        while time.time() < end:
            left = running_processes() & wanted
            if not left:
                time.sleep(1)
                try:
                    LOCKFILE.unlink(missing_ok=True)  # stale after a forced close
                except Exception:
                    pass
                return True
            if rekill and time.time() - last_kill > 2:
                # the crash handler / League client can outlive (or restart after) the
                # first kill - keep at it instead of failing and making you try again
                kill([p for p in CLIENT_PROCS if p.lower() in left])
                last_kill = time.time()
            time.sleep(0.4)
        return False

    kill(CLIENT_PROCS + ["Deceive.exe"])
    if gone(min(timeout, 10), rekill=True):
        return True
    # still there: it's almost always a Riot Client running as administrator
    left = [p for p in CLIENT_PROCS if p.lower() in running_processes()]
    if left and allow_prompt:
        ELEVATED_SEEN["close"] = True
        params = " ".join(f'/IM "{p}"' for p in left)
        if shell_run("taskkill", f"/F {params}", verb="runas", show=0):
            return gone(timeout)
    return gone(2)


ELEVATED_SEEN = {"launch": False, "close": False}
RIOT_EXE_NAMES = {"riotclientservices.exe", "riot client.exe", "riotclientux.exe",
                  "riotclientuxrender.exe"}
COMPAT_KEY = r"Software\Microsoft\Windows NT\CurrentVersion\AppCompatFlags\Layers"


def shell_run(exe, params="", cwd=None, verb="open", show=1):
    """ShellExecute: unlike CreateProcess it shows Windows' permission prompt when a program
    insists on running as administrator. Returns True if Windows started it."""
    try:
        r = ctypes.windll.shell32.ShellExecuteW(None, verb, str(exe), params or None,
                                                str(cwd) if cwd else None, show)
        return int(r) > 32
    except Exception:
        return False


def start_process(args, cwd=None, flags=0):
    try:
        subprocess.Popen(args, cwd=cwd, creationflags=flags)
    except OSError as e:
        if getattr(e, "winerror", None) != 740:
            raise
        ELEVATED_SEEN["launch"] = True
        if not shell_run(args[0], subprocess.list2cmdline(args[1:]),
                         cwd or str(Path(args[0]).parent)):
            raise RuntimeError("The Riot Client is set to run as administrator and Windows "
                               "didn't get permission to start it.") from e


def riot_admin_flags():
    """[(hive, exe path)] where Windows is told to always run a Riot Client exe as admin."""
    out = []
    try:
        import winreg
    except ImportError:
        return out
    for hive, hname in ((winreg.HKEY_CURRENT_USER, "user"), (winreg.HKEY_LOCAL_MACHINE, "all")):
        try:
            k = winreg.OpenKey(hive, COMPAT_KEY)
        except OSError:
            continue
        i = 0
        while True:
            try:
                path, val, _ = winreg.EnumValue(k, i)
            except OSError:
                break
            i += 1
            if ntpath.basename(path).lower() in RIOT_EXE_NAMES and \
                    "RUNASADMIN" in str(val).upper():
                out.append((hname, path))
        winreg.CloseKey(k)
    return out


def clear_riot_admin_flags():
    """Untick 'Run as administrator' for the Riot Client (your user only - no admin needed).
    Returns how many entries are left that need admin rights to change."""
    import winreg
    left = 0
    for hname, path in riot_admin_flags():
        if hname != "user":
            left += 1
            continue
        try:
            k = winreg.OpenKey(winreg.HKEY_CURRENT_USER, COMPAT_KEY, 0,
                               winreg.KEY_READ | winreg.KEY_SET_VALUE)
            val, _ = winreg.QueryValueEx(k, path)
            rest = [t for t in str(val).split() if t.upper() != "RUNASADMIN"]
            if not [t for t in rest if t != "~"]:
                winreg.DeleteValue(k, path)
            else:
                winreg.SetValueEx(k, path, 0, winreg.REG_SZ, " ".join(rest))
            winreg.CloseKey(k)
        except OSError:
            left += 1
    return left


def client_exe():
    try:
        data = json.loads(INSTALLS_JSON.read_text(encoding="utf-8"))
        for k in ("rc_default", "rc_live", "rc_beta"):
            if data.get(k) and Path(data[k]).exists():
                return data[k]
    except Exception:
        pass
    p = Path(r"C:\Riot Games\Riot Client\RiotClientServices.exe")
    return str(p) if p.exists() else None


# ================================================================ state / meta
DEFAULT_SETTINGS = {
    "close_to_tray": True, "start_with_windows": False, "close_after_launch": False,
    "hotkeys": True, "theme": "Violet", "layout": "grid", "streamer": False,
    "bg_refresh": True, "bg_minutes": 10, "status_mode": "online",
    "status_enabled": False, "status_engine": "builtin", "deceive_path": "", "wishlist_alerts": True,
    "match_count": 10, "live_alerts": True, "match_sound": False, "animations": True, "rank_glow": True,
    "overlay": False, "startup_account": None, "bg_image": "", "obs_overlay": False,
    "auto_offline": False, "offline_from": 0, "offline_to": 8, "pin": None,
    "auto_backup": None, "toured": False, "chat_control": True, "auto_live": True,
    "agent_picker": True, "fav_agents": [], "instant_lock": True, "open_client": True,
    "warm_client": True, "tuck_client": True, "play_account": None, "start_page": "play",
    "focus_mode": False, "agent_grid": True, "agent_grid_ok": False, "lol_auto_accept": False, "lol_random_skin": False,
}


def load_state():
    try:
        s = json.loads(STATE.read_text(encoding="utf-8"))
    except Exception:
        s = {}
    s.setdefault("active", None)
    s.setdefault("game", "VALORANT")
    s.setdefault("order", [])
    s.setdefault("last_used", {})
    s.setdefault("settings", {})
    s.setdefault("wishlist", [])
    s.setdefault("notified", [])
    s.setdefault("playtime", {})
    s.setdefault("crosshairs", [])
    s.setdefault("presets", [])
    s.setdefault("previous", None)
    s.setdefault("active_since", None)
    for k, v in DEFAULT_SETTINGS.items():
        s["settings"].setdefault(k, v)
    if s["game"] not in GAMES:
        s["game"] = "VALORANT"
    return s


def save_state(s):
    APP_DIR.mkdir(parents=True, exist_ok=True)
    tmp = STATE.with_suffix(".tmp")
    tmp.write_text(json.dumps(s, indent=1), encoding="utf-8")
    tmp.replace(STATE)


def meta_path(name):
    return META_DIR / f"{name}.json"


def load_meta(name):
    try:
        return json.loads(meta_path(name).read_text(encoding="utf-8"))
    except Exception:
        return {}


def save_meta(name, m):
    META_DIR.mkdir(parents=True, exist_ok=True)
    tmp = meta_path(name).with_suffix(".tmp")
    tmp.write_text(json.dumps(m), encoding="utf-8")
    tmp.replace(meta_path(name))


def clean_name(name):
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "", name or "").strip().rstrip(".")
    return name[:32]


def ago(ts, prefix="Used"):
    if not ts:
        return "Never used" if prefix == "Used" else "Never"
    d = time.time() - ts
    if d < 60:
        return f"{prefix} just now"
    for secs, unit in ((86400 * 7, "w"), (86400, "d"), (3600, "h"), (60, "m")):
        if d >= secs:
            return f"{prefix} {int(d // secs)}{unit} ago"
    return prefix


def dur(secs, short=True):
    secs = int(max(0, secs))
    d, r = divmod(secs, 86400)
    h, r = divmod(r, 3600)
    m = r // 60
    if d:
        return f"{d}d {h}h"
    if h:
        return f"{h}h {m}m"
    return f"{m}m"


def today_key(offset=0):
    return (datetime.now() - timedelta(days=offset)).strftime("%Y-%m-%d")


# ================================================================ http
_LOCAL_CTX = ssl.create_default_context()
_LOCAL_CTX.check_hostname = False
_LOCAL_CTX.verify_mode = ssl.CERT_NONE


def _web_ctx():
    """Certificates for real websites (GitHub, valorant-api, Riot). Python only sees the root
    certificates already sitting in the Windows store, but Windows adds most roots lazily, the
    first time its *own* networking needs one - so on many PCs GitHub's root isn't there yet and
    every request fails with CERTIFICATE_VERIFY_FAILED. Trust the bundled Mozilla list too
    (certifi), on top of the Windows store (which keeps antivirus / company roots working)."""
    ctx = ssl.create_default_context()
    try:
        import certifi
        ctx.load_verify_locations(certifi.where())
    except Exception:
        pass
    return ctx


WEB_CTX = _web_ctx()
urllib.request.install_opener(
    urllib.request.build_opener(urllib.request.HTTPSHandler(context=WEB_CTX)))


def is_cert_error(e):
    r = getattr(e, "reason", e)
    return (isinstance(r, ssl.SSLCertVerificationError)
            or "CERTIFICATE_VERIFY_FAILED" in str(r))


def curl_fetch(url, headers=None, out=None, timeout=60):
    """Last resort when Python still can't verify a certificate: Windows' own curl.exe uses the
    Windows TLS stack, which fetches a missing root from Windows Update by itself (and after
    that Python requests work too). Returns bytes, or writes to `out` and returns None."""
    exe = Path(os.environ.get("SystemRoot") or r"C:\Windows") / "System32" / "curl.exe"
    if not exe.exists():
        raise RuntimeError("secure connection failed (the certificate couldn't be checked)")
    cmd = [str(exe), "-sSfL", "--max-time", str(int(timeout)), "-A", UA]
    for k, v in (headers or {}).items():
        cmd += ["-H", f"{k}: {v}"]
    cmd += ["-o", str(out)] if out else []
    cmd.append(url)
    r = subprocess.run(cmd, capture_output=True, timeout=timeout + 10, creationflags=NO_WINDOW)
    if r.returncode != 0:
        msg = (r.stderr or b"").decode("utf-8", "replace").strip().replace("curl: ", "")
        raise RuntimeError(msg[:120] or f"download failed (curl {r.returncode})")
    return None if out else r.stdout


def http(url, headers=None, method="GET", body=None, timeout=12, local=False, raw=False):
    if isinstance(body, (bytes, bytearray)):
        data = bytes(body)
    else:
        data = json.dumps(body).encode() if body is not None else None
    h = {"User-Agent": UA}
    h.update(headers or {})
    if data is not None:
        h["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=h, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout,
                                    context=_LOCAL_CTX if local else None) as r:
            payload = r.read()
    except urllib.error.URLError as e:
        if local or data is not None or method != "GET" or not is_cert_error(e):
            raise
        payload = curl_fetch(url, h, timeout=max(timeout, 15))
    if raw:
        return payload
    return json.loads(payload) if payload else None


class NotLoggedIn(Exception):
    pass


class ClientDown(Exception):
    pass


def read_lockfile():
    try:
        parts = LOCKFILE.read_text(encoding="utf-8").strip().split(":")
    except Exception:
        return None
    if len(parts) < 5:
        return None
    return {"port": parts[2], "password": parts[3]}


def describe_err(e):
    """Short, readable reason for a failed request (status + what the server said)."""
    if isinstance(e, NotLoggedIn):
        return "the Riot Client isn't signed in. Log into an account first"
    if isinstance(e, OSError) and getattr(e, "winerror", None) == 740:
        return "the Riot Client is set to run as administrator, so Windows blocked it"
    if isinstance(e, ClientDown):
        return "the Riot Client isn't running. Log into an account first"
    if isinstance(e, urllib.error.HTTPError):
        detail = ""
        try:
            raw = e.read().decode("utf-8", "replace")
            j = json.loads(raw) if raw.strip().startswith("{") else {}
            detail = j.get("message") or j.get("errorCode") or raw[:80]
        except Exception:
            pass
        host = urllib.parse.urlparse(e.url or "").netloc if getattr(e, "url", None) else ""
        bits = [f"{e.code} {e.reason}"]
        if detail:
            bits.append(str(detail).strip())
        if host:
            bits.append(f"from {host}")
        return " · ".join(bits)
    if isinstance(e, urllib.error.URLError):
        if is_cert_error(e):
            return "secure connection failed (the certificate couldn't be checked)"
        return f"can't connect ({e.reason})"
    return str(e) or e.__class__.__name__


def local_get(lf, path, method="GET", body=None, timeout=5):
    auth = base64.b64encode(f"riot:{lf['password']}".encode()).decode()
    return http(f"https://127.0.0.1:{lf['port']}{path}", {"Authorization": "Basic " + auth},
                method, body, timeout, local=True)


def local_tokens(lf):
    try:
        t = local_get(lf, "/entitlements/v1/token")
    except urllib.error.HTTPError as e:
        raise NotLoggedIn(str(e))
    except (urllib.error.URLError, OSError) as e:
        raise ClientDown(str(e))
    if not t or not t.get("accessToken") or not t.get("token") or not t.get("subject"):
        raise NotLoggedIn("no token yet")
    return t["accessToken"], t["token"], t["subject"]


def jwt_payload(token):
    try:
        part = token.split(".")[1]
        part += "=" * (-len(part) % 4)
        return json.loads(base64.urlsafe_b64decode(part))
    except Exception:
        return {}


def detect_regions(lf, access):
    """Best guesses for the account's VALORANT region, most reliable first."""
    found = []
    try:
        idt = local_get(lf, "/rso-auth/v1/authorization/id-token") or {}
        if idt.get("token"):
            r = http("https://riot-geo.pas.si.riotgames.com/pas/v1/product/valorant",
                     {"Authorization": "Bearer " + access}, "PUT", {"id_token": idt["token"]})
            live = ((r or {}).get("affinities") or {}).get("live")
            if live:
                found.append(live)
    except Exception:
        pass
    try:
        sessions = local_get(lf, "/product-session/v1/external-sessions") or {}
        for s in sessions.values():
            for a in (s.get("launchConfiguration") or {}).get("arguments") or []:
                m = re.match(r"-ares-deployment=(\w+)", str(a))
                if m:
                    found.append(m.group(1))
    except Exception:
        pass
    try:
        rl = local_get(lf, "/riotclient/region-locale") or {}
        v = LOL_TO_VAL.get(str(rl.get("region", "")).upper())
        if v:
            found.append(v)
    except Exception:
        pass
    try:
        log = LOCAL / "VALORANT" / "Saved" / "Logs" / "ShooterGame.log"
        m = re.search(r"https://glz-(\w+)-1\.(\w+)\.a\.pvp\.net",
                      log.read_text(encoding="utf-8", errors="ignore"))
        if m:
            found.append(m.group(1))
    except Exception:
        pass
    return found


_CV_CACHE = {"mt": None, "v": ""}


def game_client_version():
    """The exact build of VALORANT installed here, from its own log ("CI server version:
    release-11.10-shipping-..."). Riot rejects changes (equipping, etc.) sent with an older
    version, and valorant-api.com's copy can lag a patch by hours."""
    log = LOCAL / "VALORANT" / "Saved" / "Logs" / "ShooterGame.log"
    try:
        mt = log.stat().st_mtime
    except Exception:
        return ""
    if _CV_CACHE["mt"] == mt:
        return _CV_CACHE["v"]
    v = ""
    try:
        with open(log, "rb") as f:
            head = f.read(2 * 1024 * 1024).decode("utf-8", "ignore")
        m = re.search(r"CI server version:\s*(release-[\w.\-]+)", head)
        if m:
            v = m.group(1)
            # the log prints "...-shipping-11-2662335"; the header wants the same shape
    except Exception:
        pass
    _CV_CACHE.update(mt=mt, v=v)
    return v


# ================================================================ valorant-api.com assets
def _parse_time(s):
    try:
        return datetime.fromisoformat(str(s).replace("Z", "+00:00"))
    except Exception:
        return None


def _hex(c, default="8a8f99"):
    c = str(c or default)
    return "#" + (c[:6] if re.fullmatch(r"[0-9a-fA-F]{6,8}", c) else default)


def _title(text):
    """Title-case but keep roman numerals and season codes like V26 / ACT VI upright."""
    out = []
    for w in str(text or "").split():
        if re.fullmatch(r"[IVXLC]+|[ivxlc]+", w) or re.fullmatch(r"[A-Za-z]\d+", w):
            out.append(w.upper())
        else:
            out.append(w[:1].upper() + w[1:].lower())
    return " ".join(out)


class Assets:
    BASE = "https://valorant-api.com/v1"

    def __init__(self):
        self.lock = threading.Lock()
        self.ready = False
        self.error = None
        self.version = ""
        self.tiers, self.ctiers, self.skins, self.skin_levels = {}, {}, {}, {}
        self.chroma_to_skin = {}
        self.buddy_levels, self.cards, self.sprays, self.titles = {}, {}, {}, {}
        self.currency_icons, self.maps, self.agents, self.themes = {}, {}, {}, {}
        self.bundles, self.contracts, self.weapons = {}, {}, {}
        self.missions, self.weapon_by_name = {}, {}
        self.act_start = {}
        self.act_label = {}
        self.current_act = None
        self.current_act_label = ""
        self.offers = {}

    def _get(self, key, path, max_age, force=False):
        f = CACHE_DIR / f"{key}.json"
        if not force and f.exists() and time.time() - f.stat().st_mtime < max_age:
            try:
                return json.loads(f.read_text(encoding="utf-8"))
            except Exception:
                pass
        try:
            data = http(self.BASE + path, timeout=45)["data"]
            CACHE_DIR.mkdir(parents=True, exist_ok=True)
            f.write_text(json.dumps(data), encoding="utf-8")
            return data
        except Exception:
            if f.exists():
                return json.loads(f.read_text(encoding="utf-8"))
            raise

    def ensure(self, force=False):
        with self.lock:
            if self.ready and not force:
                return True
            try:
                self._load(force)
                self.ready, self.error = True, None
            except Exception as e:
                self.error = str(e)
            return self.ready

    def _load(self, force):
        day = 86400
        g = lambda k, p, age=day * 3: self._get(k, p, age, force)  # noqa: E731
        self.version = (g("version", "/version", day) or {}).get("riotClientVersion", "")

        sets = g("tiers", "/competitivetiers") or []
        self.tiers = {}
        if sets:
            for t in sets[-1].get("tiers") or []:
                self.tiers[t["tier"]] = {
                    "name": str(t.get("tierName", "")).title(),
                    "icon": t.get("smallIcon") or t.get("largeIcon"),
                    "large": t.get("largeIcon") or t.get("smallIcon"),
                    "color": _hex(t.get("color"), "ffffff"),
                }
        self.ctiers = {c["uuid"].lower(): {"name": c.get("devName") or c.get("displayName") or "",
                                   "display": c.get("displayName") or "",
                                   "color": _hex(c.get("highlightColor")),
                                   "icon": c.get("displayIcon"), "rank": c.get("rank", 0)}
                       for c in g("contenttiers", "/contenttiers") or []}
        self.themes = {t["uuid"]: t.get("displayName", "") for t in g("themes", "/themes") or []}

        skins, levels, chroma_map, weapons = {}, {}, {}, {}
        for w in g("weapons", "/weapons") or []:
            wname = w.get("displayName", "")
            weapons[w["uuid"]] = {"name": wname, "icon": w.get("displayIcon"),
                                  "default_skin": (w.get("defaultSkinUuid") or "")}
            for s in w.get("skins") or []:
                name = s.get("displayName", "")
                standard = (name.startswith("Standard") or "Random Favorite" in name
                            or name == "Melee" or s["uuid"] == w.get("defaultSkinUuid"))
                lv = [{"uuid": x["uuid"], "name": x.get("displayName") or "",
                       "icon": x.get("displayIcon"), "video": x.get("streamedVideo"),
                       "item": (x.get("levelItem") or "").split("::")[-1]}
                      for x in s.get("levels") or []]
                ch = [{"uuid": x["uuid"], "name": x.get("displayName") or "",
                       "render": x.get("fullRender") or x.get("displayIcon"),
                       "swatch": x.get("swatch"), "video": x.get("streamedVideo")}
                      for x in s.get("chromas") or []]
                skins[s["uuid"]] = {
                    "uuid": s["uuid"], "name": name, "weapon": wname, "weapon_id": w["uuid"],
                    "tier": (s.get("contentTierUuid") or "").lower() or None,
                    "theme": s.get("themeUuid"),
                    "standard": standard,
                    "icon": (lv[0]["icon"] if lv else None) or s.get("displayIcon")
                    or (ch[0]["render"] if ch else None),
                    "levels": lv, "chromas": ch,
                }
                levels[s["uuid"]] = s["uuid"]
                for x in lv:
                    levels[x["uuid"]] = s["uuid"]
                for x in ch:
                    chroma_map[x["uuid"]] = s["uuid"]
        self.skins, self.skin_levels, self.chroma_to_skin = skins, levels, chroma_map
        self.weapons = weapons

        bl = {}
        for b in g("buddies", "/buddies") or []:
            info = {"uuid": b["uuid"], "name": b.get("displayName", ""),
                    "icon": b.get("displayIcon")}
            bl[b["uuid"]] = info
            for level in b.get("levels") or []:
                bl[level["uuid"]] = info
        self.buddy_levels = bl
        self.cards = {c["uuid"]: {"name": c.get("displayName", ""), "small": c.get("smallArt"),
                                  "wide": c.get("wideArt"), "large": c.get("largeArt")}
                      for c in g("cards", "/playercards") or []}
        self.sprays = {s["uuid"]: {"name": s.get("displayName", ""),
                                   "icon": s.get("fullTransparentIcon") or s.get("displayIcon")}
                       for s in g("sprays", "/sprays") or []}
        self.titles = {t["uuid"]: t.get("titleText") or t.get("displayName") or ""
                       for t in g("titles", "/playertitles") or []}
        self.currency_icons = {c["uuid"]: c.get("displayIcon")
                               for c in g("currencies", "/currencies") or []}
        self.maps = {}
        for mp in g("maps", "/maps") or []:
            info = {"name": mp.get("displayName", ""), "icon": mp.get("listViewIcon"),
                    "splash": mp.get("splash")}
            if mp.get("mapUrl"):
                self.maps[mp["mapUrl"]] = info
            self.maps[mp["uuid"]] = info
        self.agents = {a["uuid"].lower(): {"name": a.get("displayName", ""),
                                           "icon": a.get("displayIcon"),
                                           "base": bool(a.get("isBaseContent")),
                                           "role": (a.get("role") or {}).get("displayName", "")}
                       for a in g("agents", "/agents?isPlayableCharacter=true") or []}
        self.missions = {}
        try:
            for mi in g("missions", "/missions") or []:
                self.missions[mi["uuid"]] = {
                    "title": mi.get("title") or mi.get("displayName") or "Mission",
                    "type": str(mi.get("type") or ""), "target": mi.get("progressToComplete") or 1,
                    "xp": mi.get("xpGrant") or 0}
        except Exception:
            pass
        self.bundles = {b["uuid"]: {"name": b.get("displayName", ""),
                                    "icon": b.get("displayIcon2") or b.get("displayIcon"),
                                    "tall": b.get("verticalPromoImage")}
                        for b in g("bundles", "/bundles") or []}
        contracts = {}
        for c in g("contracts", "/contracts") or []:
            content = c.get("content") or {}
            xp = [lv.get("xp", 0) for ch in content.get("chapters") or []
                  for lv in ch.get("levels") or []]
            contracts[c["uuid"]] = {"name": c.get("displayName", ""),
                                    "type": content.get("relationType") or "",
                                    "levels": xp}
        self.contracts = contracts
        self.weapon_by_name = {w["name"]: wid for wid, w in self.weapons.items()}

        now = datetime.now(timezone.utc)
        seasons = g("seasons", "/seasons", day) or []
        by_id = {s["uuid"]: s for s in seasons}
        self.act_start, self.current_act, self.current_act_label = {}, None, ""
        for s in seasons:
            if s.get("type") != "EAresSeasonType::Act":
                continue
            st, en = _parse_time(s.get("startTime")), _parse_time(s.get("endTime"))
            if st:
                self.act_start[s["uuid"]] = st
            par = by_id.get(s.get("parentUuid") or "", {})
            ep = _title(par.get("displayName", "")).replace("Episode ", "E")
            self.act_label[s["uuid"]] = (ep + " " + _title(s.get("displayName", ""))
                                         .replace("Act ", "A")).strip()
            if st and en and st <= now <= en:
                self.current_act = s["uuid"]
                parent = by_id.get(s.get("parentUuid") or "", {})
                self.current_act_label = " ".join(
                    x for x in (_title(parent.get("displayName", "")),
                                _title(s.get("displayName", ""))) if x)
        try:
            self.offers = json.loads((CACHE_DIR / "offers.json").read_text(encoding="utf-8"))
        except Exception:
            self.offers = {}

    # helpers -----------------------------------------------------------
    def tier_name(self, t):
        if not t or t < 3:
            return "Unranked"
        return self.tiers.get(t, {}).get("name") or f"Tier {t}"

    def tier_icon(self, t, large=False):
        return self.tiers.get(t or 0, {}).get("large" if large else "icon")

    def tier_color(self, t):
        return self.tiers.get(t or 0, {}).get("color") if t and t >= 3 else None

    TIER_PRICES = {"select": 875, "deluxe": 1275, "premium": 1775, "exclusive": 2175,
                   "ultra": 2475}

    # known content tier uuids, in case valorant-api renames things
    TIER_UUIDS = {"12683d76-48d7-84a3-4e09-6985794f0445": 875,    # Select
                  "0cebb8be-46d7-c12a-d306-e9907bfc5a25": 1275,   # Deluxe
                  "60bca009-4182-7998-dee7-b8a2558dc369": 1775,   # Premium
                  "e046854e-406c-37f4-6607-19a9ba8426fc": 2175,   # Exclusive
                  "411e4a55-4e59-7757-41f0-86a53f101bb5": 2475}   # Ultra

    def edition_price(self, tier_uuid):
        if not tier_uuid:
            return None
        tier_uuid = str(tier_uuid).lower()
        if tier_uuid in self.TIER_UUIDS:
            return self.TIER_UUIDS[tier_uuid]
        ct = self.ctiers.get(tier_uuid) or next(
            (v for k, v in self.ctiers.items() if str(k).lower() == tier_uuid), {})
        label = " ".join(str(ct.get(k) or "") for k in ("name", "display")).lower()
        for word, price in self.TIER_PRICES.items():
            if word in label:
                return price
        return None

    def skin_price(self, skin_uuid, estimate=True):
        return self.skin_price_info(skin_uuid, estimate)[0]

    def skin_price_info(self, skin_uuid, estimate=True):
        """(price, exact). Real store prices when Riot gave them to us, otherwise the
        standard price for the skin's edition (Select 875, Deluxe 1275 ...)."""
        s = self.skins.get(skin_uuid)
        if not s or s.get("standard"):
            return None, True
        for lv in s["levels"][:1]:
            p = self.offers.get(lv["uuid"])
            if p:
                return p, True
        p = self.offers.get(skin_uuid)
        if p or not estimate:
            return p, True
        base = self.edition_price(s.get("tier"))
        if not base:
            return None, True
        return (base * 2 if s.get("weapon") == "Melee" else base), False

    def skin_view(self, skin_uuid, owned_levels=None, owned_chromas=None):
        s = self.skins.get(skin_uuid)
        if not s:
            return None
        ct = self.ctiers.get(s.get("tier") or "", {})
        return {"id": skin_uuid, "name": s["name"], "sub": s["weapon"], "icon": s["icon"],
                "color": ct.get("color"), "tier_icon": ct.get("icon"),
                "rank": ct.get("rank", 0), "weapon": s["weapon"], "kind": "skin",
                "price": self.skin_price(skin_uuid)}


ASSETS = Assets()
PEAK_CUTOFF = datetime(2022, 6, 20, tzinfo=timezone.utc)  # Ascendant added; tiers renumbered


# ================================================================ parsing
def parse_mmr(mmr):
    comp = ((mmr or {}).get("QueueSkills") or {}).get("competitive") or {}
    seasons = comp.get("SeasonalInfoBySeasonID") or {}
    out = {"tier": 0, "rr": 0, "peak_tier": 0, "wins": None, "games": None}
    act = ASSETS.current_act
    if act:
        info = seasons.get(act) or {}
        out["tier"] = info.get("CompetitiveTier", 0) or 0
        out["rr"] = info.get("RankedRating", 0) or 0
        out["wins"] = info.get("NumberOfWinsWithPlacements")
        out["games"] = info.get("NumberOfGames")
    else:
        lu = (mmr or {}).get("LatestCompetitiveUpdate") or {}
        out["tier"] = lu.get("TierAfterUpdate", 0) or 0
        out["rr"] = lu.get("RankedRatingAfterUpdate", 0) or 0
    peak, peak_act = out["tier"], (act if out["tier"] else None)
    for sid, info in seasons.items():
        st = ASSETS.act_start.get(sid)
        if ASSETS.act_start and (st is None or st < PEAK_CUTOFF):
            continue
        best = max([info.get("Rank", 0) or 0, info.get("CompetitiveTier", 0) or 0]
                   + [int(k) for k in (info.get("WinsByTier") or {}) if str(k).isdigit()])
        if best > peak:
            peak, peak_act = best, sid
    out["peak_tier"] = peak
    out["peak_act"] = ASSETS.act_label.get(peak_act or "", "")
    acts = []
    for sid, info in seasons.items():
        games = info.get("NumberOfGames") or 0
        tier = info.get("Rank") or info.get("CompetitiveTier") or 0
        if not games:
            continue
        st = ASSETS.act_start.get(sid)
        acts.append({"id": sid, "tier": tier, "games": games,
                     "wins": info.get("NumberOfWinsWithPlacements") or 0,
                     "t": st.timestamp() if st else 0,
                     "old": bool(st and st < PEAK_CUTOFF)})
    acts.sort(key=lambda a: a["t"])
    out["acts"] = acts[-8:]
    return out


def parse_comp_updates(data):
    out = []
    for m in (data or {}).get("Matches") or []:
        out.append({"id": m.get("MatchID"), "start": (m.get("MatchStartTime") or 0) / 1000,
                    "tier": m.get("TierAfterUpdate", 0) or 0,
                    "rr": m.get("RankedRatingAfterUpdate", 0) or 0,
                    "delta": m.get("RankedRatingEarned", 0) or 0,
                    "map": m.get("MapID", "")})
    out.sort(key=lambda x: x["start"])
    return out


def summarize_match(d, puuid, rr_delta=None):
    info = d.get("matchInfo") or {}
    me = next((p for p in d.get("players") or [] if p.get("subject") == puuid), None)
    if not me:
        return None
    st = me.get("stats") or {}
    teams = {t.get("teamId"): t for t in d.get("teams") or []}
    mine = teams.get(me.get("teamId")) or {}
    others = [t for k, t in teams.items() if k != me.get("teamId")]
    won = mine.get("won")
    if others and mine:
        score = f"{mine.get('roundsWon', 0)}-{others[0].get('roundsWon', 0)}"
        if not won and mine.get("roundsWon") == others[0].get("roundsWon"):
            won = None  # draw
    else:
        score = ""
        won = None if won is None else won
    rounds = max(1, st.get("roundsPlayed") or 1)
    q = info.get("queueID") or info.get("queueId") or ""
    return {"id": info.get("matchId"), "start": (info.get("gameStartMillis") or 0) / 1000,
            "map": info.get("mapId", ""), "queue": QUEUES.get(q, q.title() or "Custom"),
            "agent": str(me.get("characterId") or "").lower(),
            "k": st.get("kills", 0), "d": st.get("deaths", 0), "a": st.get("assists", 0),
            "acs": round((st.get("score") or 0) / rounds), "won": won, "score": score,
            "length": (info.get("gameLengthMillis") or 0) / 1000,
            "tier": me.get("competitiveTier", 0), "rr": rr_delta,
            **((d.get("extra") or {}).get(puuid) or {})}


def parse_store(sf, now=None):
    """Turn a storefront response into a compact snapshot."""
    now = now or time.time()
    out = {"fetched": now, "daily": [], "night": [], "bundles": []}
    sp = (sf or {}).get("SkinsPanelLayout") or {}
    offers = {o.get("OfferID"): o for o in sp.get("SingleItemStoreOffers") or []}
    for lid in sp.get("SingleItemOffers") or []:
        o = offers.get(lid) or {}
        out["daily"].append({"skin": ASSETS.skin_levels.get(lid, lid), "level": lid,
                             "cost": (o.get("Cost") or {}).get(VP)})
    out["daily_expires"] = now + (sp.get("SingleItemOffersRemainingDurationInSeconds") or 0)
    bonus = (sf or {}).get("BonusStore") or {}
    for b in bonus.get("BonusStoreOffers") or []:
        offer = b.get("Offer") or {}
        rewards = offer.get("Rewards") or [{}]
        lid = rewards[0].get("ItemID") or offer.get("OfferID")
        out["night"].append({"skin": ASSETS.skin_levels.get(lid, lid), "level": lid,
                             "cost": (offer.get("Cost") or {}).get(VP),
                             "price": (b.get("DiscountCosts") or {}).get(VP),
                             "percent": b.get("DiscountPercent", 0), "seen": b.get("IsSeen")})
    if bonus:
        out["night_expires"] = now + (bonus.get("BonusStoreRemainingDurationInSeconds") or 0)
    fb = (sf or {}).get("FeaturedBundle") or {}
    for b in fb.get("Bundles") or ([fb["Bundle"]] if fb.get("Bundle") else []):
        price = (b.get("TotalDiscountedCost") or {}).get(VP)
        if price is None:
            price = sum((it.get("DiscountedPrice") or 0) for it in b.get("Items") or [])
        out["bundles"].append({
            "id": b.get("DataAssetID"), "price": price,
            "expires": now + (b.get("DurationRemainingInSeconds")
                              or fb.get("BundleRemainingDurationInSeconds") or 0),
            "skins": [ASSETS.skin_levels.get((it.get("Item") or {}).get("ItemID"))
                      for it in b.get("Items") or []
                      if ASSETS.skin_levels.get((it.get("Item") or {}).get("ItemID"))]})
    return out


def parse_contracts(c):
    out = {"bp": None, "agents": []}
    active = (c or {}).get("ActiveSpecialContract")
    for item in (c or {}).get("Contracts") or []:
        d = ASSETS.contracts.get(item.get("ContractDefinitionID") or "")
        if not d:
            continue
        lvl = item.get("ProgressionLevelReached", 0) or 0
        toward = item.get("ProgressionTowardsNextLevel", 0) or 0
        need = d["levels"][lvl] if lvl < len(d["levels"]) else None
        entry = {"name": d["name"], "level": lvl, "total": len(d["levels"]),
                 "toward": toward, "need": need}
        if item.get("ContractDefinitionID") == active:
            out["bp"] = entry
        elif d["type"].lower() == "agent" and lvl > 0:
            out["agents"].append(entry)
    out["agents"].sort(key=lambda x: (-x["level"], x["name"]))
    return out


def parse_missions(c):
    out = []
    for mi in (c or {}).get("Missions") or []:
        d = ASSETS.missions.get(mi.get("ID") or "", {})
        prog = sum(v for v in (mi.get("Objectives") or {}).values() if isinstance(v, (int, float)))
        t = d.get("type", "")
        kind = "Daily" if "Daily" in t else "Weekly" if "Weekly" in t else "Mission"
        exp = _parse_time(mi.get("ExpirationTime"))
        out.append({"title": d.get("title", "Mission"), "kind": kind, "progress": prog,
                    "target": d.get("target", 1), "done": bool(mi.get("Complete")),
                    "xp": d.get("xp", 0), "expires": exp.timestamp() if exp else None})
    out.sort(key=lambda x: (x["done"], x["kind"] != "Daily", x["title"]))
    return out


SKIN_SOCKET = "bcef87d6-209b-46c6-8b19-fbe40bd95abc"


CHROMA_SOCKET = "3ad1b2b2-acdb-4524-852f-954a76ddae0a"
BUDDY_SOCKETS = ("77258665-71d1-4623-bc72-44db9bd5b3b3", "dd3bf334-87f3-40bd-b043-682a57a8dc3a")


def parse_loadouts(data, order=None, full=None):
    """{puuid: {weapon_id_lower: skin_uuid}} from a pregame/core-game loadouts response.
    Pass a dict as `full` to also get {puuid: {weapon: {skin, chroma, buddy}}}."""
    out = {}
    for i, e in enumerate((data or {}).get("Loadouts") or []):
        lo = e.get("Loadout") if isinstance(e.get("Loadout"), dict) else e
        subj = lo.get("Subject") or e.get("Subject") or (order[i] if order and i < len(order) else None)
        items = lo.get("Items") or {}
        skins, det = {}, {}
        for wid, it in items.items():
            socks = it.get("Sockets") or {}
            sid = ((socks.get(SKIN_SOCKET) or {}).get("Item") or {}).get("ID")
            if sid:
                skins[wid.lower()] = sid
                bud = None
                for bs in BUDDY_SOCKETS:
                    bud = bud or ((socks.get(bs) or {}).get("Item") or {}).get("ID")
                det[wid.lower()] = {"skin": sid, "buddy": bud, "chroma": (
                    (socks.get(CHROMA_SOCKET) or {}).get("Item") or {}).get("ID")}
        if subj:
            out[subj] = skins
            if full is not None:
                full[subj] = det
    return out


def chat_history(lf, cid):
    """Recent messages with one friend from the Riot Client's chat."""
    last = None
    for v in ("v6", "v5"):
        try:
            r = local_get(lf, f"/chat/{v}/messages?cid={urllib.parse.quote(cid)}") or {}
            msgs = r.get("messages") or []
            msgs.sort(key=lambda m_: int(m_.get("time") or 0))
            return msgs
        except Exception as e:
            last = e
    raise last


def chat_send(lf, cid, text):
    last = None
    for v in ("v6", "v5"):
        try:
            return local_get(lf, f"/chat/{v}/messages", "POST",
                             {"cid": cid, "message": text, "type": "chat"})
        except Exception as e:
            last = e
    raise last


def presence_parties(lf):
    """{puuid: partyId} from Riot chat presences (players whose presence you can see)."""
    out = {}
    try:
        for p in (local_get(lf, "/chat/v4/presences") or {}).get("presences") or []:
            if p.get("product") != "valorant":
                continue
            priv = decode_private(p.get("private"))
            pid = priv.get("partyId") or (priv.get("partyPresenceData") or {}).get("partyId")
            if pid and p.get("puuid"):
                out[p["puuid"]] = pid
    except Exception:
        pass
    return out


ROUND_ENDS = {"Elimination": ("E", "Eliminated"), "Detonate": ("B", "Spike detonated"),
              "Defuse": ("D", "Spike defused"), "": ("T", "Time ran out"),
              "Surrendered": ("S", "Surrendered")}


def match_detail(d, me, known=None):
    """Scoreboard + round-by-round view of one cached match. Names are only shown for you,
    your party and your own saved accounts - everyone else is shown by agent, like the
    in-game scoreboard does for players who hide their name."""
    known = known or {}
    info = d.get("matchInfo") or {}
    players = d.get("players") or []
    meP = next((p for p in players if p.get("subject") == me), {}) or {}
    my_team, my_party = meP.get("teamId"), meP.get("partyId")
    rounds = d.get("roundResults") or d.get("rounds") or []
    extra = {}
    for p in players:
        extra[p.get("subject")] = ((d.get("extra") or {}).get(p.get("subject"))
                                   if not d.get("roundResults") else None) \
            or player_extra(d, p.get("subject"))
    rows = []
    for p in players:
        st = p.get("stats") or {}
        sub = p.get("subject")
        rp = max(1, st.get("roundsPlayed") or len(rounds) or 1)
        agent = str(p.get("characterId") or "").lower()
        ag_name = (ASSETS.agents.get(agent) or {}).get("name") or "Player"
        show = sub == me or (my_party and p.get("partyId") == my_party) or sub in known
        name = (known.get(sub) or (f"{p.get('gameName')}#{p.get('tagLine')}"
                                   if p.get("gameName") else ag_name)) if show else ag_name
        ex = extra.get(sub) or {}
        rows.append({"puuid": sub, "team": p.get("teamId"), "agent": agent, "name": name,
                     "named": bool(show), "me": sub == me,
                     "party": bool(my_party and p.get("partyId") == my_party and sub != me),
                     "tier": p.get("competitiveTier") or 0, "card": p.get("playerCard"),
                     "k": st.get("kills", 0) or 0, "d": st.get("deaths", 0) or 0,
                     "a": st.get("assists", 0) or 0,
                     "acs": round((st.get("score", 0) or 0) / rp),
                     "hs": ex.get("hs"), "adr": ex.get("adr"), "fb": ex.get("fb") or 0,
                     "dd": ex.get("dd"), "rk": ex.get("rk") or []})
    teams = {}
    for r in rows:
        teams.setdefault(r["team"], []).append(r)
    for t in teams.values():
        t.sort(key=lambda r: -r["acs"])
    tinfo = {t.get("teamId"): t for t in d.get("teams") or []}
    order = sorted(teams, key=lambda t: (t != my_team, str(t)))
    if len(teams) > 2:      # deathmatch etc: one big table
        allr = sorted(rows, key=lambda r: -r["acs"])
        tabs = [{"id": "all", "label": "Scoreboard", "won": None, "rounds": None, "rows": allr}]
    else:
        tabs = [{"id": t, "label": ("Your team" if t == my_team else "Enemy team"),
                 "won": (tinfo.get(t) or {}).get("won"),
                 "rounds": (tinfo.get(t) or {}).get("roundsWon"), "rows": teams[t]}
                for t in order]
    rlist = []
    for r in rounds:
        code = r.get("roundResultCode") or ""
        short, long_ = ROUND_ENDS.get(code, ("?", r.get("roundResult") or code))
        rlist.append({"n": (r.get("roundNum") or 0) + 1, "won": r.get("winningTeam") == my_team,
                      "short": short, "long": long_,
                      "planted": bool(r.get("plantSite")), "site": r.get("plantSite") or ""})
    mine = tinfo.get(my_team) or {}
    other = next((t for k, t in tinfo.items() if k != my_team), {}) or {}
    return {"map": info.get("mapId", ""), "queue": QUEUES.get(info.get("queueID") or info.get(
        "queueId") or "", info.get("queueID") or "Custom"),
            "start": (info.get("gameStartMillis") or 0) / 1000,
            "length": (info.get("gameLengthMillis") or 0) / 1000,
            "won": mine.get("won"), "score": (mine.get("roundsWon"), other.get("roundsWon")),
            "teams": tabs, "rounds": rlist, "full": bool(d.get("v") or d.get("roundResults"))}


def fetch_leaderboard(vc, region, start=0, size=50):
    act = ASSETS.current_act
    if not act:
        raise RuntimeError("Season info isn't loaded yet.")
    r = vc.pd(f"/mmr/v1/leaderboards/affinity/{region}/queue/competitive/season/{act}"
              f"?startIndex={start}&size={size}") or {}
    out = []
    for p in r.get("Players") or []:
        anon = p.get("IsAnonymized") or not p.get("gameName")
        out.append({"rank": p.get("leaderboardRank"), "rr": p.get("rankedRating", 0),
                    "wins": p.get("numberOfWins", 0), "tier": p.get("competitiveTier", 0),
                    "card": p.get("PlayerCardID"), "puuid": p.get("puuid"),
                    "name": "Secret Agent" if anon else f"{p['gameName']}#{p.get('tagLine', '')}",
                    "anon": bool(anon)})
    return out, r.get("totalPlayers") or 0


def pregame_quit(vc, region, match_id):
    glz = f"https://glz-{region}-1.{vc.shard}.a.pvp.net"
    return http(f"{glz}/pregame/v1/matches/{match_id}/quit", vc.headers(), "POST", b"")


def pregame_action(vc, region, match_id, agent_id, lock=False):
    glz = f"https://glz-{region}-1.{vc.shard}.a.pvp.net"
    verb = "lock" if lock else "select"
    return http(f"{glz}/pregame/v1/matches/{match_id}/{verb}/{agent_id}", vc.headers(), "POST")


PENALTY_KINDS = [   # (match in effect name, label, what it usually means)
    ("gameban", "Game ban", "You can't play VALORANT until it ends. Given for repeated or "
                            "serious offences."),
    ("riotrestriction", "Account restriction", "A Riot-wide restriction on the account."),
    ("rankedrating", "RR penalty", "Ranked Rating taken away, usually for a dodge or an AFK in "
                                   "competitive."),
    ("rrpenalty", "RR penalty", "Ranked Rating taken away, usually for a dodge or an AFK in "
                                "competitive."),
    ("queuerestriction", "Queue restriction", "You can't queue for some or all modes. Usually "
                                              "from AFKs, leaving or repeated dodges."),
    ("queuedelay", "Queue delay", "A wait before you can queue again, usually after leaving "
                                  "agent select (a dodge)."),
    ("xpdenial", "XP withheld", "No XP for the affected games, usually for being AFK."),
    ("textchat", "Chat restricted", "Text chat is off. Given for chat that broke the Community "
                                    "Code."),
    ("voicechat", "Voice restricted", "Voice chat is off. Given for voice comms that broke the "
                                      "Community Code."),
    ("chatmute", "Chat restricted", "Chat is off. Given for chat that broke the Community Code."),
    ("warning", "Warning", "A heads-up - no restriction yet, but more of the same escalates."),
]
PENALTY_HELP_URL = "https://support.riotgames.com/valorant/penalties/penalties-and-bans-faq"
PENALTY_APPEAL_URL = "https://support-valorant.riotgames.com/hc/en-us/requests/new"


def _penalty_kind(effect):
    e = effect.lower()
    for key, label, why in PENALTY_KINDS:
        if key in e:
            return label, why
    pretty = re.sub(r"(?<!^)(?=[A-Z])", " ", effect.replace("Effect", "")).strip()
    return pretty or "Restriction", ""


def parse_penalties(p):
    """Every active penalty with what it is, what usually causes it, when it started and
    ends, games left, and the match it came from when Riot says."""
    items = []
    skip = ("logging", "rmsnotification")
    for pen in (p or {}).get("Penalties") or []:
        effects = [k for k, v in pen.items() if k.endswith("Effect") and v
                   and not any(x in k.lower() for x in skip)]
        kinds = []
        for e in effects:
            lab, why = _penalty_kind(e)
            if lab not in [k_[0] for k_ in kinds]:
                kinds.append((lab, why))
        exp = _parse_time(pen.get("Expiry"))
        start = _parse_time(pen.get("StartedAt") or pen.get("IssuedAt"))
        match = next((v for k, v in pen.items() if isinstance(v, str) and v
                      and ("MatchID" in k or "GameID" in k)), None)
        reason = next((v for k, v in pen.items() if isinstance(v, str) and v
                       and "reason" in k.lower()), None)
        detail = {}
        for e in effects:
            ev = pen.get(e)
            if isinstance(ev, dict):
                for k, v in ev.items():
                    nice = re.sub(r"(?<=[a-z])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])", " ", k).replace("I Ds", "IDs").replace("Queue IDs", "Queues")
                    if isinstance(v, list) and v and all(isinstance(x, str) for x in v):
                        detail[nice] = ", ".join(QUEUES.get(x, x) for x in v)
                    elif isinstance(v, (int, float, str)) and v not in ("", 0):
                        detail[nice] = v
        games = pen.get("GamesRemaining")
        items.append({"label": ", ".join(k_[0] for k_ in kinds) or "Restriction",
                      "kinds": kinds, "expires": exp.timestamp() if exp else None,
                      "started": start.timestamp() if start else None, "games": games,
                      "match": match, "reason": reason, "detail": detail,
                      "id": pen.get("ID")})
    active = [i for i in items if (i["expires"] is None or i["expires"] > time.time()
                                   or (i["games"] or 0) > 0)]
    active = [i for i in active if not (len(i["kinds"]) == 1 and i["kinds"][0][0] == "Warning"
                                        and not i["expires"])] or active
    return {"checked": time.time(), "items": active}


def chime_wav(path):
    """Write a short, soft two-note chime (no bundled audio files needed)."""
    import struct
    import wave
    rate = 44100
    frames = bytearray()
    for freq, length in ((880.0, 0.16), (1318.5, 0.34)):
        n = int(rate * length)
        for i in range(n):
            t = i / rate
            env = min(1.0, i / (rate * 0.006)) * math.exp(-5.5 * t)
            v = env * (0.55 * math.sin(2 * math.pi * freq * t)
                       + 0.18 * math.sin(4 * math.pi * freq * t))
            frames += struct.pack("<h", int(max(-1, min(1, v)) * 21000))
    path.parent.mkdir(parents=True, exist_ok=True)
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(bytes(frames))
    return path


def play_chime():
    try:
        import winsound
    except ImportError:
        return False
    f = APP_DIR / "match-found.wav"
    try:
        if not f.exists():
            chime_wav(f)
        winsound.PlaySound(str(f), winsound.SND_FILENAME | winsound.SND_ASYNC
                           | winsound.SND_NODEFAULT)
        return True
    except Exception:
        return False


UI_SOUNDS = {
    # name: [(freq Hz, seconds, volume 0-1)] - all short and quiet on purpose
    "tap": [(1850.0, 0.022, 0.16)],
    "toggle": [(1320.0, 0.03, 0.15), (1760.0, 0.035, 0.12)],
    "success": [(784.0, 0.07, 0.17), (1174.7, 0.16, 0.15)],
    "error": [(415.3, 0.09, 0.17), (311.1, 0.16, 0.15)],
}


def ui_sound_wav(name, path):
    import struct
    import wave
    rate = 44100
    frames = bytearray()
    for freq, length, vol in UI_SOUNDS[name]:
        n = int(rate * length)
        for i in range(n):
            t = i / rate
            env = min(1.0, i / (rate * 0.003)) * math.exp(-t / (length * 0.38))
            v = env * vol * (math.sin(2 * math.pi * freq * t)
                             + 0.25 * math.sin(4 * math.pi * freq * t))
            frames += struct.pack("<h", int(max(-1, min(1, v)) * 32000))
    path.parent.mkdir(parents=True, exist_ok=True)
    with wave.open(str(path), "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(bytes(frames))
    return path


def play_ui_sound(name):
    try:
        import winsound
    except ImportError:
        return False
    f = APP_DIR / "sounds" / f"{name}.wav"
    try:
        if not f.exists():
            ui_sound_wav(name, f)
        winsound.PlaySound(str(f), winsound.SND_FILENAME | winsound.SND_ASYNC
                           | winsound.SND_NODEFAULT)
        return True
    except Exception:
        return False


def flash_taskbar(widget, count=6):
    """Flash RiotHub's taskbar button until it's focused (like the Riot Client does)."""
    if sys.platform != "win32":
        return

    class FLASHWINFO(ctypes.Structure):
        _fields_ = [("cbSize", ctypes.c_uint), ("hwnd", ctypes.c_void_p),
                    ("dwFlags", ctypes.c_uint), ("uCount", ctypes.c_uint),
                    ("dwTimeout", ctypes.c_uint)]
    try:
        u = ctypes.windll.user32
        hwnd = u.GetParent(widget.winfo_id()) or widget.winfo_id()
        fi = FLASHWINFO(ctypes.sizeof(FLASHWINFO), hwnd, 0x3 | 0xC, count, 0)
        u.FlashWindowEx(ctypes.byref(fi))
    except Exception:
        pass


RANKED_BLOCKERS = ("Game ban", "Account restriction", "Queue restriction", "Queue delay")
RANKED_LEVEL = 20


def ranked_status(m, now=None):
    """Can this account queue competitive right now?
    Returns (state, short label, longer explanation); state is 'ready', 'blocked', 'level',
    'expired' or None when we don't know enough yet."""
    now = now or time.time()
    if m.get("expired"):
        return "expired", "Re-login", "The saved login expired. Log in once to check ranked."
    pens = [i for i in (m.get("penalties") or {}).get("items") or []
            if i.get("expires") is None or i["expires"] > now or (i.get("games") or 0) > 0]
    block = [i for i in pens if any((k[0] if isinstance(k, (list, tuple)) else k)
                                    in RANKED_BLOCKERS for k in i.get("kinds") or [])]
    if block:
        ends = [i["expires"] for i in block if i.get("expires")]
        games = sum(i.get("games") or 0 for i in block)
        if ends:
            left = dur(max(ends) - now)
            return "blocked", f"Ranked in {left}", f"Queue restricted for another {left}."
        if games:
            return ("blocked", f"{games} game{'s' if games != 1 else ''} left",
                    f"Restricted for {games} more game{'s' if games != 1 else ''}.")
        return "blocked", "Restricted", "This account has a queue restriction."
    lvl = m.get("level")
    if lvl is None:
        return None, "", ""
    if lvl < RANKED_LEVEL:
        n = RANKED_LEVEL - lvl
        return "level", f"Lvl {lvl}/{RANKED_LEVEL}", f"{n} more level{'s' if n != 1 else ''} until ranked."
    return "ready", "Ranked ready", "Level 20+, no queue restrictions."


def queue_elapsed(d):
    """Seconds since the party started queueing (falls back to when we first saw it)."""
    try:
        return max(0.0, time.time() - datetime.fromisoformat(
            str(d.get("queue_since")).replace("Z", "+00:00")).timestamp())
    except Exception:
        return max(0.0, time.time() - d.get("t", time.time()))


def owned_ids(meta, kind):
    return set((meta.get("owned") or {}).get(kind) or [])


def owned_skin_set(meta):
    return {ASSETS.skin_levels[i] for i in owned_ids(meta, "skins")
            if i in ASSETS.skin_levels and not ASSETS.skins.get(
                ASSETS.skin_levels[i], {}).get("standard")}


def owned_items(meta, tab):
    items, seen = [], set()
    if tab == "skins":
        for su in owned_skin_set(meta):
            v = ASSETS.skin_view(su)
            if v:
                items.append(v)
        wi = {w: n for n, w in enumerate(WEAPON_ORDER)}
        items.sort(key=lambda s: (wi.get(s["weapon"], 99), s["weapon"], -s["rank"], s["name"]))
    elif tab == "buddies":
        for i in owned_ids(meta, "buddies"):
            b = ASSETS.buddy_levels.get(i)
            if b and b["uuid"] not in seen:
                seen.add(b["uuid"])
                items.append({"id": b["uuid"], "name": b["name"], "sub": "Gun buddy",
                              "icon": b["icon"], "kind": "buddy"})
    elif tab == "cards":
        for i in owned_ids(meta, "cards"):
            c = ASSETS.cards.get(i)
            if c:
                items.append({"id": i, "name": c["name"], "sub": "Player card",
                              "icon": c["small"], "kind": "card"})
    elif tab == "sprays":
        for i in owned_ids(meta, "sprays"):
            s = ASSETS.sprays.get(i)
            if s:
                items.append({"id": i, "name": s["name"], "sub": "Spray", "icon": s["icon"],
                              "kind": "spray"})
    elif tab == "titles":
        for i in owned_ids(meta, "titles"):
            t = ASSETS.titles.get(i)
            if t:
                items.append({"id": i, "name": t, "sub": "Title", "icon": None,
                              "kind": "title"})
    if tab != "skins":
        items.sort(key=lambda x: x["name"].lower())
    return items


def store_prices(sf):
    """{item uuid: VP} from a storefront response (daily shop, night market, bundles)."""
    out = {}
    sf = sf or {}
    for o in (sf.get("SkinsPanelLayout") or {}).get("SingleItemStoreOffers") or []:
        cost = (o.get("Cost") or {}).get(VP)
        for rw in o.get("Rewards") or []:
            if cost and rw.get("ItemID"):
                out[rw["ItemID"]] = cost
    for b in (sf.get("BonusStore") or {}).get("BonusStoreOffers") or []:
        o = b.get("Offer") or {}
        cost = (o.get("Cost") or {}).get(VP)
        for rw in o.get("Rewards") or []:
            if cost and rw.get("ItemID"):
                out[rw["ItemID"]] = cost
    return out


def inventory_value(meta):
    """(VP total, skins priced). Uses store prices where known, edition prices otherwise."""
    total, priced = 0, 0
    for su in owned_skin_set(meta):
        p = ASSETS.skin_price(su)
        if p:
            total += p
            priced += 1
    return total, priced


def collections(meta):
    """Group skins by theme -> completion progress."""
    owned = owned_skin_set(meta)
    groups = {}
    for su, s in ASSETS.skins.items():
        if s.get("standard") or not s.get("theme"):
            continue
        groups.setdefault(s["theme"], []).append(su)
    out = []
    for th, skins in groups.items():
        if len(skins) < 2:
            continue
        have = [x for x in skins if x in owned]
        if not have:
            continue
        name = ASSETS.themes.get(th) or ASSETS.skins[skins[0]]["name"].split(" ")[0]
        wi = {w: n for n, w in enumerate(WEAPON_ORDER)}
        skins.sort(key=lambda x: wi.get(ASSETS.skins[x]["weapon"], 99))
        out.append({"id": th, "name": name, "skins": skins, "have": len(have),
                    "total": len(skins)})
    out.sort(key=lambda c: (-(c["have"] / c["total"]), -c["have"], c["name"]))
    return out


# ================================================================ VALORANT client
class ValClient:
    def __init__(self, access, ent, puuid, shard):
        self.access, self.ent, self.puuid, self.shard = access, ent, puuid, shard

    def headers(self):
        return {"Authorization": "Bearer " + self.access,
                "X-Riot-Entitlements-JWT": self.ent,
                "X-Riot-ClientPlatform": CLIENT_PLATFORM,
                "X-Riot-ClientVersion": getattr(self, "_cv_override", None)
                or game_client_version() or ASSETS.version or ""}

    def pd(self, path, method="GET", body=None, timeout=12):
        return http(f"https://pd.{self.shard}.a.pvp.net{path}", self.headers(), method, body,
                    timeout)

    # ---- player preferences (settings sync)
    def _pref_hosts(self):
        hosts = [f"https://player-preferences-{SHARD_PREFS.get(self.shard, 'usw2')}.pp.sgp.pvp.net",
                 "https://player-preferences-euc1.pp.sgp.pvp.net",
                 "https://playerpreferences.riotgames.com"]
        return list(dict.fromkeys(hosts))

    LOCAL_PREFS = "/player-preferences/v1/data-json/Ares.PlayerSettings"

    def _read_remote(self, host):
        r = http(f"{host}/playerPref/v3/getPreference/Ares.PlayerSettings",
                 {"Authorization": "Bearer " + self.access})
        return unwrap_settings(r)

    def _read_local(self, lf):
        return unwrap_settings(local_get(lf, self.LOCAL_PREFS, timeout=8))

    def get_settings(self):
        """Returns (settings, where) - where is "local" (the Riot Client) or a server URL."""
        errs = []
        lf = read_lockfile()
        if lf:
            try:
                st = self._read_local(lf)
                if st:
                    return st, "local"
                errs.append("Riot Client: empty")
            except Exception as e:
                errs.append(f"Riot Client: {describe_err(e)}")
        for host in self._pref_hosts():
            try:
                st = self._read_remote(host)
                if st:
                    return st, host
                errs.append(f"{host.split('//')[1].split('.')[0]}: empty")
            except Exception as e:
                errs.append(describe_err(e))
        raise RuntimeError("Couldn't read settings: " + "; ".join(errs[:3]))

    def put_settings(self, settings, host=None):
        """Save through the Riot Client first (what VALORANT itself uses), then the settings
        servers. Each write is read back, so a 'success' that didn't stick isn't reported."""
        lf = read_lockfile()
        routes = []
        if lf:
            routes.append("local")
        routes += self._pref_hosts()
        if host in routes:
            routes.remove(host)
            routes.insert(0, host)
        errs = []
        for rt in routes:
            try:
                if rt == "local":
                    local_get(lf, self.LOCAL_PREFS, "PUT", settings, timeout=10)
                    reader = lambda: self._read_local(lf)
                else:
                    http(f"{rt}/playerPref/v3/savePreference",
                         {"Authorization": "Bearer " + self.access}, "PUT",
                         {"type": "Ares.PlayerSettings", "data": encode_settings(settings)})
                    reader = lambda rt=rt: self._read_remote(rt)
            except Exception as e:
                errs.append(("Riot Client: " if rt == "local" else "") + describe_err(e))
                continue
            try:
                back = reader()
            except Exception:
                return rt  # saved, couldn't double-check
            if settings_match(settings, back):
                return rt
            errs.append(("Riot Client" if rt == "local" else rt.split("//")[1].split(".")[0])
                        + ": saved but didn't stick")
        raise RuntimeError("Couldn't save settings: " + "; ".join(errs[:3]))

    # ---- loadout
    def get_loadout(self):
        last = None
        for v in ("v3", "v2"):
            try:
                lo = self.pd(f"/personalization/{v}/players/{self.puuid}/playerloadout")
                if lo:
                    self._lo_ver = v
                    return lo
            except Exception as e:
                last = e
        raise last or RuntimeError("Couldn't read loadout")

    def put_loadout(self, lo):
        v = getattr(self, "_lo_ver", "v2")
        path = f"/personalization/{v}/players/{self.puuid}/playerloadout"
        body = {k: val for k, val in lo.items() if k not in ("Subject", "Version")}
        try:
            return self.pd(path, "PUT", body)
        except urllib.error.HTTPError as e:
            if e.code not in (400, 403, 409):
                raise
            # most often a stale client version right after a patch: get the live one, retry
            try:
                live = http(Assets.BASE + "/version", timeout=8)["data"]["riotClientVersion"]
            except Exception:
                raise e
            if not live or live == self.headers()["X-Riot-ClientVersion"]:
                raise
            self._cv_override = live
            ASSETS.version = live
            return self.pd(path, "PUT", body)


def decode_settings(data):
    return json.loads(zlib.decompress(base64.b64decode(data), -15).decode("utf-8"))


def encode_settings(settings):
    co = zlib.compressobj(9, zlib.DEFLATED, -15)
    raw = co.compress(json.dumps(settings, separators=(",", ":")).encode()) + co.flush()
    return base64.b64encode(raw).decode()


SYNC_CATEGORIES = {
    "crosshair": "Crosshair",
    "sensitivity": "Sensitivity",
    "keybinds": "Keybinds",
    "everything": "Everything",
}


def unwrap_settings(r):
    """The Riot Client hands back plain JSON; the servers wrap it base64+deflate in "data"."""
    if not isinstance(r, dict):
        return None
    d = r.get("data")
    if isinstance(d, str) and d:
        return decode_settings(d)
    if isinstance(d, dict) and d:
        return d
    if any(k in r for k in ("floatSettings", "stringSettings", "boolSettings", "intSettings",
                            "actionMappings", "axisMappings", "settingsVersion")):
        return r
    return None


def _settings_index(st):
    out = {}
    for kind in ("floatSettings", "stringSettings", "boolSettings", "intSettings"):
        for e in (st or {}).get(kind) or []:
            if isinstance(e, dict) and "settingEnum" in e:
                out[(kind, e["settingEnum"])] = e.get("value")
    return out


def settings_match(want, got):
    """True if every value we wrote is there when read back (floats within rounding)."""
    a, b = _settings_index(want), _settings_index(got)
    if not a:
        return bool(got)
    for k, v in a.items():
        g = b.get(k)
        if isinstance(v, float) or isinstance(g, float):
            try:
                if abs(float(v) - float(g)) > 1e-3:
                    return False
            except (TypeError, ValueError):
                return False
        elif g != v:
            return False
    return True


def merge_settings(target, source, cats):
    """Copy chosen categories of VALORANT settings from source onto target."""
    if "everything" in cats:
        return json.loads(json.dumps(source))
    out = json.loads(json.dumps(target))

    def pred(enum):
        e = str(enum)
        return (("crosshair" in cats and "Crosshair" in e)
                or ("sensitivity" in cats and "Sensitivity" in e))

    for key, val in source.items():
        if key.endswith("Settings") and isinstance(val, list):
            picked = [x for x in val if isinstance(x, dict) and pred(x.get("settingEnum"))]
            if not picked:
                continue
            enums = {x.get("settingEnum") for x in picked}
            kept = [x for x in out.get(key) or [] if x.get("settingEnum") not in enums]
            out[key] = kept + picked
    if "keybinds" in cats:
        for key in ("actionMappings", "axisMappings"):
            if key in source:
                out[key] = source[key]
    return out


def connect(region_override=None, known_shard=None):
    """Tokens + a working VALORANT shard for whoever is logged into the client."""
    ASSETS.ensure()
    lf = read_lockfile()
    if not lf:
        raise ClientDown("Riot Client isn't running.")
    access, ent, puuid = local_tokens(lf)
    order = []
    if region_override and region_override != "Auto":
        order.append(region_override)
    if known_shard:
        order.append(known_shard)
    order += detect_regions(lf, access) + ["eu", "na", "ap", "kr"]
    tried = set()
    for reg in order:
        shard = REGION_TO_SHARD.get(str(reg).lower())
        if not shard or shard in tried:
            continue
        tried.add(shard)
        vc = ValClient(access, ent, puuid, shard)
        try:
            xp = vc.pd(f"/account-xp/v1/players/{puuid}")
            if xp and xp.get("Progress") is not None:
                return vc, xp, str(reg).lower(), lf
        except Exception:
            continue
    raise RuntimeError("Couldn't load VALORANT data for this account. Has it played "
                       "VALORANT? You can set its region in Edit.")


def fetch_all(region_override=None, known_shard=None, match_count=10, log=None):
    """Read everything for the logged-in account. Runs in a worker thread."""
    vc, xp, region, lf = connect(region_override, known_shard)
    puuid = vc.puuid
    out = {"puuid": puuid, "shard": vc.shard, "region": region, "updated": time.time(),
           "level": (xp.get("Progress") or {}).get("Level"),
           "xp": (xp.get("Progress") or {}).get("XP")}
    say = log or (lambda s: None)

    try:
        n = vc.pd("/name-service/v2/players", "PUT", [puuid]) or []
        if n:
            out["game_name"], out["tag"] = n[0].get("GameName"), n[0].get("TagLine")
    except Exception:
        try:
            s = local_get(lf, "/chat/v1/session") or {}
            out["game_name"], out["tag"] = s.get("game_name"), s.get("game_tag")
        except Exception:
            pass
    try:
        lo = vc.get_loadout() or {}
        ident = lo.get("Identity") or {}
        out["card"] = ident.get("PlayerCardID")
        out["title"] = ident.get("PlayerTitleID")
        out["loadout"] = {g.get("ID"): {"skin": g.get("SkinID"), "chroma": g.get("ChromaID"),
                                        "buddy": g.get("CharmID")}
                          for g in lo.get("Guns") or []}
    except Exception:
        pass
    say("rank")
    try:
        out.update(parse_mmr(vc.pd(f"/mmr/v1/players/{puuid}")))
    except Exception as e:
        out["rank_error"] = str(e)
    rr_by_match = {}
    try:
        raw = []
        for start in (0, 20, 40):
            page = vc.pd(f"/mmr/v1/players/{puuid}/competitiveupdates?startIndex={start}"
                         f"&endIndex={start + 20}&queue=competitive") or {}
            raw += page.get("Matches") or []
            if len(page.get("Matches") or []) < 20:
                break
        cu = parse_comp_updates({"Matches": raw})
        out["rr_history"] = cu
        rr_by_match = {c["id"]: c["delta"] for c in cu}
    except Exception:
        pass
    try:
        out["wallet"] = (vc.pd(f"/store/v1/wallet/{puuid}") or {}).get("Balances") or {}
    except Exception:
        pass
    say("inventory")
    owned = {}
    for key, tid in ITEM_TYPES.items():
        try:
            r = vc.pd(f"/store/v1/entitlements/{puuid}/{tid}") or {}
            owned[key] = [e["ItemID"] for e in (r.get("Entitlements") or []) if e.get("ItemID")]
        except Exception:
            pass
    out["owned"] = owned
    say("store")
    try:
        try:
            sf = vc.pd(f"/store/v3/storefront/{puuid}", "POST", {})
        except Exception:
            sf = vc.pd(f"/store/v2/storefront/{puuid}")
        out["store"] = parse_store(sf)
    except Exception as e:
        out["store_error"] = str(e)
    try:
        if not ASSETS.offers or time.time() - (CACHE_DIR / "offers.json").stat().st_mtime > 86400 * 3:
            raise FileNotFoundError
    except Exception:
        offers = {}
        try:
            for o in (vc.pd("/store/v1/offers/") or {}).get("Offers") or []:
                cost = (o.get("Cost") or {}).get(VP)
                for rw in o.get("Rewards") or []:
                    if cost and rw.get("ItemID"):
                        offers[rw["ItemID"]] = cost
        except Exception:
            pass
        if offers:
            ASSETS.offers = offers
            try:
                (CACHE_DIR / "offers.json").write_text(json.dumps(offers), encoding="utf-8")
            except Exception:
                pass
    # whatever's in today's shop and night market has a real price - remember it
    try:
        learned = store_prices(sf)
        if learned:
            ASSETS.offers.update({k: v for k, v in learned.items() if k not in ASSETS.offers})
            (CACHE_DIR / "offers.json").write_text(json.dumps(ASSETS.offers), encoding="utf-8")
    except Exception:
        pass
    try:
        craw = vc.pd(f"/contracts/v1/contracts/{puuid}")
        out["contracts"] = parse_contracts(craw)
        out["missions"] = parse_missions(craw)
    except Exception:
        pass
    try:
        out["penalties"] = parse_penalties(vc.pd("/restrictions/v3/penalties"))
    except Exception:
        pass
    say("matches")
    try:
        hist = vc.pd(f"/match-history/v1/history/{puuid}?startIndex=0&endIndex={match_count}")
        MATCH_DIR.mkdir(parents=True, exist_ok=True)
        matches = []
        for h in (hist or {}).get("History") or []:
            mid = h.get("MatchID")
            if not mid:
                continue
            f = MATCH_DIR / f"{mid}.json"
            d = None
            if f.exists():
                try:
                    d = json.loads(f.read_text(encoding="utf-8"))
                except Exception:
                    d = None
            if d is None:
                try:
                    d = vc.pd(f"/match-details/v1/matches/{mid}", timeout=20)
                    slim = slim_match(d)
                    f.write_text(json.dumps(slim), encoding="utf-8")
                    d = slim
                    time.sleep(0.25)
                except Exception:
                    continue
            s = summarize_match(d, puuid, rr_by_match.get(mid))
            if s:
                matches.append(s)
        out["matches"] = matches
    except Exception:
        pass
    try:
        top = [p for p, e in duo_partners(puuid).items() if e["n"] >= 2][:6]
        if top:
            out["duo_names"] = {n.get("Subject"): f"{n.get('GameName')}#{n.get('TagLine')}"
                                for n in vc.pd("/name-service/v2/players", "PUT", top) or []
                                if n.get("GameName")}
    except Exception:
        pass
    try:
        out["friends"] = [{"puuid": f["puuid"], "name": f["name"]} for f in fetch_friends(lf)
                          if f.get("puuid")]
    except Exception:
        pass
    say("settings")
    try:
        settings, host = vc.get_settings()
        PREFS_DIR.mkdir(parents=True, exist_ok=True)
        out["_settings"] = settings
    except Exception:
        pass
    return out


# ================================================================ live match / party
def fetch_live(vc, region, cache, lf=None):
    """Agent select / in-game lobby with ranks. Hidden (incognito) names stay hidden."""
    glz = f"https://glz-{region}-1.{vc.shard}.a.pvp.net"
    h = vc.headers()
    out = {"phase": "none", "players": [], "party": [], "t": time.time()}
    try:
        p = http(f"{glz}/parties/v1/players/{vc.puuid}", h) or {}
        pid = p.get("CurrentPartyID")
        if pid:
            party = http(f"{glz}/parties/v1/parties/{pid}", h) or {}
            out["party"] = [m.get("Subject") for m in party.get("Members") or [] if m.get("Subject")]
            out["party_id"] = pid
            out["queue"] = (party.get("MatchmakingData") or {}).get("QueueID") or ""
            out["party_state"] = party.get("State", "")
            out["party_open"] = str(party.get("Accessibility", "")).upper() == "OPEN"
            out["queues"] = party.get("EligibleQueues") or []
            out["queue_since"] = party.get("QueueEntryTime") or ""
            out["party_owner"] = next((m.get("Subject") for m in party.get("Members") or []
                                       if m.get("IsOwner")), None)
    except Exception:
        pass
    match, players = None, []
    for phase, base in (("pregame", "pregame/v1"), ("ingame", "core-game/v1")):
        try:
            mid = (http(f"{glz}/{base}/players/{vc.puuid}", h) or {}).get("MatchID")
        except Exception:
            mid = None
        if not mid:
            continue
        try:
            match = http(f"{glz}/{base}/matches/{mid}", h)
        except Exception:
            match = None
        if match:
            out["phase"], out["match_id"] = phase, mid
            break
    if match and out["phase"] == "pregame":
        team = match.get("AllyTeam") or {}
        players = [dict(p, TeamID=team.get("TeamID")) for p in team.get("Players") or []]
        out["map"] = match.get("MapID", "")
        out["queue"] = match.get("QueueID") or out.get("queue", "")
        out["timer"] = match.get("PhaseTimeRemainingNS", 0) / 1e9
        out["timer_t"] = time.time()
        out["side"] = "Attack" if str(team.get("TeamID", "")).lower() == "red" else "Defense"
    elif match:
        players = match.get("Players") or []
        out["map"] = match.get("MapID", "")
        out["queue"] = (match.get("MatchmakingData") or {}).get("QueueID") or out.get("queue", "")
    else:
        players = [{"Subject": s, "TeamID": "party"} for s in out["party"]]
    subjects = [p.get("Subject") for p in players if p.get("Subject")]
    names = {}
    try:
        for n in vc.pd("/name-service/v2/players", "PUT", subjects) or []:
            names[n.get("Subject")] = (n.get("GameName"), n.get("TagLine"))
    except Exception:
        pass
    my_team = next((p.get("TeamID") for p in players if p.get("Subject") == vc.puuid), None)
    if out["phase"] == "ingame" and my_team:
        out["side"] = "Attack" if str(my_team).lower() == "red" else "Defense"
    skins, full = {}, {}
    if out["phase"] != "none":
        base = "pregame/v1" if out["phase"] == "pregame" else "core-game/v1"
        try:
            skins = parse_loadouts(http(f"{glz}/{base}/matches/{out['match_id']}/loadouts", h),
                                   [p.get("Subject") for p in players], full)
        except Exception:
            skins = {}
    parties = presence_parties(lf) if lf else {}
    for p in players:
        s = p.get("Subject")
        if not s:
            continue
        ident = p.get("PlayerIdentity") or {}
        mine = s == vc.puuid or s in out["party"]
        hidden = bool(ident.get("Incognito")) and not mine
        r = cache.get(s)
        if not r or time.time() - r["t"] > 900:
            try:
                r = dict(parse_mmr(vc.pd(f"/mmr/v1/players/{s}")), t=time.time())
                cache[s] = r
                time.sleep(0.15)
            except Exception:
                r = cache.get(s) or {"tier": 0, "rr": 0, "peak_tier": 0, "t": 0}
        nm = names.get(s)
        out["players"].append({
            "puuid": s, "team": p.get("TeamID"), "ally": p.get("TeamID") == my_team,
            "agent": str(p.get("CharacterID") or "").lower(),
            "locked": p.get("CharacterSelectionState") == "locked",
            "level": None if (ident.get("HideAccountLevel") and not mine) else ident.get("AccountLevel"),
            "card": ident.get("PlayerCardID"), "hidden": hidden,
            "name": None if hidden or not nm or not nm[0] else f"{nm[0]}#{nm[1]}",
            "tier": r.get("tier", 0), "rr": r.get("rr", 0), "peak": r.get("peak_tier", 0),
            "me": s == vc.puuid, "party": s in out["party"],
            "skins": skins.get(s) or {}, "loadout": full.get(s) or {},
            "spray": None, "title": ident.get("PlayerTitleID"), "pid": parties.get(s)})
    counts = {}
    for p in out["players"]:
        if p["pid"]:
            counts[p["pid"]] = counts.get(p["pid"], 0) + 1
    groups = [pid for pid, n in counts.items() if n >= 2]
    for p in out["players"]:
        p["group"] = groups.index(p["pid"]) if p["pid"] in groups else None
    me = next((p for p in out["players"] if p["me"]), None)
    if me:
        out["my_agent"], out["my_locked"] = me["agent"], me["locked"]
    out["players"].sort(key=lambda x: (not x["ally"], not x["me"], not x["party"]))
    return out


def party_action(vc, region, party_id, action, arg=None):
    """Party controls the game's own menu has: queue start/stop, queue mode, open/closed,
    invite by Riot ID."""
    glz = f"https://glz-{region}-1.{vc.shard}.a.pvp.net/parties/v1/parties/{party_id}"
    h = vc.headers()
    if action == "join":
        return http(f"{glz}/matchmaking/join", h, "POST", b"")
    if action == "leave":
        return http(f"{glz}/matchmaking/leave", h, "POST", b"")
    if action == "queue":
        return http(f"{glz}/queue", h, "POST", {"queueID": arg})
    if action == "access":
        return http(f"{glz}/accessibility", h, "POST", {"accessibility": "OPEN" if arg else "CLOSED"})
    if action == "invite":
        name, tag = arg
        return http(f"{glz}/invites/name/{urllib.parse.quote(name)}/tag/{urllib.parse.quote(tag)}",
                    h, "POST", b"")
    raise ValueError(action)


def encounter_index(me):
    """{puuid: {"n": games together, "last": ts}} from cached match files."""
    idx = {}
    if not MATCH_DIR.exists():
        return idx
    for f in MATCH_DIR.glob("*.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            continue
        subs = [p.get("subject") for p in d.get("players") or []]
        if me not in subs:
            continue
        t = ((d.get("matchInfo") or {}).get("gameStartMillis") or 0) / 1000
        for s in subs:
            if s and s != me:
                e = idx.setdefault(s, {"n": 0, "last": 0})
                e["n"] += 1
                e["last"] = max(e["last"], t)
    return idx


# ================================================================ crosshairs / loadouts / goals
def crosshair_entries(settings):
    out = {}
    for key, val in (settings or {}).items():
        if key.endswith("Settings") and isinstance(val, list):
            picked = [x for x in val if isinstance(x, dict) and "Crosshair" in str(x.get("settingEnum"))]
            if picked:
                out[key] = picked
    return out


def apply_crosshair(current, entries):
    return merge_settings(current, entries, {"crosshair"})


def pick_roulette(meta, rng=None):
    """Random owned skin per weapon -> {weapon_id: skin_uuid}."""
    import random
    rng = rng or random.Random()
    by_weapon = {}
    for su in owned_skin_set(meta):
        s = ASSETS.skins.get(su)
        if s:
            by_weapon.setdefault(s["weapon_id"].lower(), []).append(su)
    return {w: rng.choice(v) for w, v in by_weapon.items()}


def goal_progress(m):
    g = m.get("goal") or {}
    target = g.get("tier")
    if not target:
        return None
    cur = (m.get("tier") or 0) * 100 + (m.get("rr") or 0)
    start = g.get("start", cur)
    want = target * 100
    span = max(1, want - start)
    hist = m.get("rr_history") or []
    week = [x for x in hist if x["start"] > time.time() - 7 * 86400]
    per_game = sum(x["delta"] for x in hist) / len(hist) if hist else 0
    per_day = sum(x["delta"] for x in week) / 7 if week else 0
    left = max(0, want - cur)
    return {"target": target, "frac": max(0, min(1, (cur - start) / span)), "left": left,
            "per_game": per_game, "per_day": per_day, "done": cur >= want,
            "games": (left / per_game) if per_game > 0 else None}


def today_summary(m):
    midnight = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0).timestamp()
    games = [x for x in m.get("rr_history") or [] if x["start"] >= midnight]
    w = sum(1 for x in games if x["delta"] > 0)
    l = sum(1 for x in games if x["delta"] < 0)
    streak, kind = 0, None
    for x in m.get("matches") or []:  # newest first
        if x.get("won") is None:
            break
        if kind is None:
            kind = x["won"]
        if x["won"] != kind:
            break
        streak += 1
    return {"w": w, "l": l, "rr": sum(x["delta"] for x in games), "games": len(games),
            "streak": streak, "streak_win": kind}


def match_breakdown(matches, key):
    out = {}
    for mt in matches or []:
        k = mt.get(key)
        if not k:
            continue
        e = out.setdefault(k, {"n": 0, "w": 0, "k": 0, "d": 0})
        e["n"] += 1
        e["w"] += 1 if mt.get("won") is True else 0
        e["k"] += mt.get("k", 0)
        e["d"] += mt.get("d", 0)
    return sorted(out.items(), key=lambda kv: -kv[1]["n"])


def add_store_history(m, store):
    hist = m.get("store_history") or []
    key = int(store.get("daily_expires", 0)) // 3600
    if not store.get("daily") or any(h.get("k") == key for h in hist):
        return hist
    hist.append({"k": key, "t": store.get("fetched", time.time()),
                 "daily": [o["skin"] for o in store.get("daily") or []],
                 "night": [o["skin"] for o in store.get("night") or []]})
    return hist[-90:]


def last_seen(meta_by_name, skin):
    best = None
    for name, m in meta_by_name.items():
        for h in m.get("store_history") or []:
            if skin in h.get("daily", []) or skin in h.get("night", []):
                if not best or h["t"] > best[1]:
                    best = (name, h["t"])
    return best


# ================================================================ more stats
def player_extra(d, puuid):
    """Headshot %, damage per round, damage delta (dealt - taken per round), first bloods and
    kills in every round for one player in a match."""
    hs = bs = ls = dmg = taken = fb = 0
    rounds = d.get("roundResults") or []
    if not rounds and (d.get("extra") or {}).get(puuid):
        return d["extra"][puuid]
    per_round = []
    for r in rounds:
        first = None
        kills = 0
        for ps in r.get("playerStats") or []:
            for k in ps.get("kills") or []:
                t = k.get("roundTime", k.get("timeSinceRoundStartMillis", 0)) or 0
                if first is None or t < first[0]:
                    first = (t, k.get("killer"))
            for dm in ps.get("damage") or []:
                if dm.get("receiver") == puuid and ps.get("subject") != puuid:
                    taken += dm.get("damage", 0) or 0
            if ps.get("subject") == puuid:
                kills = len(ps.get("kills") or [])
                for dm in ps.get("damage") or []:
                    hs += dm.get("headshots", 0) or 0
                    bs += dm.get("bodyshots", 0) or 0
                    ls += dm.get("legshots", 0) or 0
                    dmg += dm.get("damage", 0) or 0
        per_round.append(kills)
        if first and first[1] == puuid:
            fb += 1
    shots = hs + bs + ls
    n = len(rounds)
    return {"hs": round(100 * hs / shots, 1) if shots else None,
            "adr": round(dmg / n) if n else None, "fb": fb,
            "dd": round((dmg - taken) / n) if n else None, "rk": per_round}


def slim_match(d):
    """What we keep on disk per match: enough for every scoreboard and round view."""
    extra = {p.get("subject"): player_extra(d, p.get("subject"))
             for p in d.get("players") or [] if p.get("subject")}
    rounds = [{"roundNum": r.get("roundNum"), "winningTeam": r.get("winningTeam"),
               "roundResultCode": r.get("roundResultCode"), "roundResult": r.get("roundResult"),
               "plantSite": r.get("plantSite")} for r in d.get("roundResults") or []]
    return {"matchInfo": d.get("matchInfo"), "teams": d.get("teams"), "extra": extra,
            "rounds": rounds, "v": 2,
            "players": [{"subject": p.get("subject"), "teamId": p.get("teamId"),
                         "characterId": p.get("characterId"),
                         "competitiveTier": p.get("competitiveTier"),
                         "stats": p.get("stats"), "partyId": p.get("partyId"),
                         "gameName": p.get("gameName"), "tagLine": p.get("tagLine"),
                         "playerCard": p.get("playerCard"),
                         "accountLevel": p.get("accountLevel")}
                        for p in d.get("players") or []]}


def duo_partners(me):
    """People who queued with you: {puuid: {"n", "w"}} from cached matches."""
    out = {}
    if not MATCH_DIR.exists():
        return out
    for f in MATCH_DIR.glob("*.json"):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            continue
        players = d.get("players") or []
        mine = next((p for p in players if p.get("subject") == me), None)
        if not mine or not mine.get("partyId"):
            continue
        won = next((t.get("won") for t in d.get("teams") or []
                    if t.get("teamId") == mine.get("teamId")), None)
        for p in players:
            if p.get("subject") != me and p.get("partyId") == mine["partyId"]:
                e = out.setdefault(p["subject"], {"n": 0, "w": 0})
                e["n"] += 1
                e["w"] += 1 if won else 0
    return dict(sorted(out.items(), key=lambda kv: -kv[1]["n"]))


def time_of_day(matches):
    buckets = {"Morning": (5, 12), "Afternoon": (12, 17), "Evening": (17, 22), "Night": (22, 29)}
    out = {k: {"n": 0, "w": 0} for k in buckets}
    for mt in matches or []:
        if not mt.get("start"):
            continue
        hr = datetime.fromtimestamp(mt["start"]).hour
        hr2 = hr + 24 if hr < 5 else hr
        for k, (a, b) in buckets.items():
            if a <= hr2 < b:
                out[k]["n"] += 1
                out[k]["w"] += 1 if mt.get("won") is True else 0
    return out


def week_summary(m, playtime_week):
    cut = time.time() - 7 * 86400
    games = [x for x in m.get("rr_history") or [] if x["start"] >= cut]
    ms = [x for x in m.get("matches") or [] if (x.get("start") or 0) >= cut]
    return {"ranked": len(games), "rr": sum(x["delta"] for x in games),
            "w": sum(1 for x in ms if x.get("won") is True),
            "l": sum(1 for x in ms if x.get("won") is False), "time": playtime_week}


def agent_tips(matches, map_id=None):
    """Your agents ranked by results, overall and on one map."""
    def rank(ms):
        rows = match_breakdown(ms, "agent")
        rows = [(a, e) for a, e in rows if e["n"] >= 1]
        rows.sort(key=lambda kv: (-(kv[1]["w"] + 1) / (kv[1]["n"] + 2), -kv[1]["n"]))
        return rows
    on_map = [x for x in matches or [] if map_id and x.get("map") == map_id]
    return {"map": rank(on_map)[:3], "all": rank(matches)[:3]}


def team_gap(players):
    ts = [p["tier"] for p in players if p.get("ally") and p.get("tier", 0) >= 3]
    return (max(ts) - min(ts)) if len(ts) >= 2 else 0


def inventory_csv(meta):
    rows = ["Weapon,Skin,Rarity,Price (VP)"]
    for it in owned_items(meta, "skins"):
        ct = next((c["name"] for c in ASSETS.ctiers.values() if c.get("color") == it.get("color")),
                  "")
        name = it["name"].replace('"', "'")
        rows.append(f'{it["weapon"]},"{name}",{ct},{it.get("price") or ""}')
    return "\n".join(rows) + "\n"


# ================================================================ TcNo import / game config
TCNO_MAP = {"Cookies": "Data/Cookies", "Sessions": "Data/Sessions",
            "RiotClientPrivateSettings.yaml": "Data/RiotClientPrivateSettings.yaml",
            "RiotGamesPrivateSettings.yaml": "Data/RiotGamesPrivateSettings.yaml",
            "RiotClientSettings.yaml": "Config/RiotClientSettings.yaml"}


def tcno_accounts(folder):
    """Find TcNo-style Riot login caches under a folder."""
    found = []
    root = Path(folder)
    cands = [root] + [p for p in root.rglob("*") if p.is_dir()][:500]
    for d in cands:
        hits = [k for k in TCNO_MAP if (d / k).exists()]
        if any(h.endswith(".yaml") and "Private" in h for h in hits):
            found.append(d)
    return found


def import_tcno_folder(src, name):
    dst = ACC_DIR / name
    _rm(dst)
    for k, rel in TCNO_MAP.items():
        _cp(src / k, dst / rel)
    return has_login(dst)


def val_config_dir(puuid):
    base = LOCAL / "VALORANT" / "Saved" / "Config"
    if not puuid or not base.exists():
        return None
    for d in base.iterdir():
        if d.is_dir() and d.name.lower().startswith(puuid.lower()):
            return d
    return None


def copy_video_settings(src_puuid, dst_puuid):
    s, d = val_config_dir(src_puuid), val_config_dir(dst_puuid)
    if not s or not d:
        raise RuntimeError("Both accounts need to have launched VALORANT on this PC once.")
    src = s / "Windows" / "GameUserSettings.ini"
    dst = d / "Windows" / "GameUserSettings.ini"
    if not src.exists():
        raise RuntimeError("No graphics settings found for the source account.")
    if dst.exists():
        PREFS_BACKUP_DIR.mkdir(parents=True, exist_ok=True)
        shutil.copy2(dst, PREFS_BACKUP_DIR / f"video__{dst_puuid[:8]}__{int(time.time())}.ini")
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


# ================================================================ friends / status / league
def decode_private(p):
    try:
        return json.loads(base64.b64decode(p or "") or b"{}")
    except Exception:
        return {}


def fetch_friends(lf):
    friends = (local_get(lf, "/chat/v4/friends") or {}).get("friends") or []
    pres = (local_get(lf, "/chat/v4/presences") or {}).get("presences") or []
    by = {}
    for p in pres:
        by.setdefault(p.get("puuid"), []).append(p)
    out = []
    for f in friends:
        ps = by.get(f.get("puuid")) or []
        val = next((p for p in ps if p.get("product") == "valorant"), None)
        any_p = val or (ps[0] if ps else None)
        state = (any_p or {}).get("state") or "offline"
        detail = ""
        pres = {}
        if val:
            priv = decode_private(val.get("private"))
            pres = presence_info(priv)
            loop = pres.get("loop") or ""
            detail = {"MENUS": "In menus", "PREGAME": "Agent select",
                      "INGAME": "In a match"}.get(loop, "")
        elif any_p:
            detail = {"league_of_legends": "League", "keystone": "Riot Client",
                      "bacon": "Runeterra"}.get(any_p.get("product"), "")
        out.append({"puuid": f.get("puuid"), "pid": f.get("pid"),
                    "name": f"{f.get('game_name') or f.get('name') or '?'}#{f.get('game_tag') or ''}",
                    "state": "offline" if not ps else state, "detail": detail,
                    "online": bool(ps) and state not in ("offline",),
                    "product": (any_p or {}).get("product") or "", "pres": pres,
                    "note": f.get("note") or ""})
    out.sort(key=lambda x: (not x["online"], x["name"].lower()))
    return out


def presence_info(priv):
    """The useful bits of a VALORANT presence. Riot has used a flat layout and a nested one
    (playerPresenceData / matchPresenceData / partyPresenceData); read whichever is there.
    Anything missing stays missing - nothing is guessed."""
    pp = priv.get("playerPresenceData") or {}
    mp = priv.get("matchPresenceData") or {}
    party = priv.get("partyPresenceData") or {}

    def pick(*vals):
        for v in vals:
            if v not in (None, ""):
                return v
        return None
    out = {
        "tier": pick(pp.get("competitiveTier"), priv.get("competitiveTier")),
        "level": pick(pp.get("accountLevel"), priv.get("accountLevel")),
        "card": pick(pp.get("playerCardId"), priv.get("playerCardId")),
        "title": pick(pp.get("playerTitleId"), priv.get("playerTitleId")),
        "loop": pick(mp.get("sessionLoopState"), priv.get("sessionLoopState")),
        "map": pick(mp.get("matchMap"), priv.get("matchMap"), priv.get("partyOwnerMatchMap")),
        "queue": pick(mp.get("queueId"), priv.get("queueId")),
        "party_size": pick(party.get("partySize"), priv.get("partySize")),
        "ally": pick(party.get("partyOwnerMatchScoreAllyTeam"),
                     priv.get("partyOwnerMatchScoreAllyTeam")),
        "enemy": pick(party.get("partyOwnerMatchScoreEnemyTeam"),
                      priv.get("partyOwnerMatchScoreEnemyTeam")),
        "lb": pick(pp.get("leaderboardPosition"), priv.get("leaderboardPosition")),
    }
    return {k: v for k, v in out.items() if v is not None}


def fetch_player_profile(vc, puuid, n_matches=8, stop=None):
    """Rank, act history, RR movement and recent competitive matches for any player on your
    region, read with your own signed-in session (the same endpoints the game uses for the
    career tab). Each part fails on its own, with the reason, instead of sinking the rest."""
    out = {"t": time.time(), "puuid": puuid, "errors": {}, "matches": []}
    try:
        out["mmr"] = parse_mmr(vc.pd(f"/mmr/v1/players/{puuid}"))
    except Exception as e:
        out["errors"]["rank"] = describe_err(e)
        out["errors"]["rank_code"] = getattr(e, "code", None)
    try:
        cu = vc.pd(f"/mmr/v1/players/{puuid}/competitiveupdates?startIndex=0&endIndex=20"
                   "&queue=competitive") or {}
        out["updates"] = parse_comp_updates(cu)
    except Exception as e:
        out["errors"]["history"] = describe_err(e)
        out["updates"] = []
    recent = sorted(out["updates"], key=lambda u: -u["start"])[:n_matches]
    MATCH_DIR.mkdir(parents=True, exist_ok=True)
    failed = 0
    for u in recent:
        if stop and stop():
            break
        mid = u.get("id")
        if not mid:
            continue
        f = MATCH_DIR / f"{mid}.json"
        d = None
        if f.exists():
            try:
                d = json.loads(f.read_text(encoding="utf-8"))
            except Exception:
                d = None
        if d is None:
            try:
                d = slim_match(vc.pd(f"/match-details/v1/matches/{mid}", timeout=20))
                f.write_text(json.dumps(d), encoding="utf-8")
                time.sleep(0.2)
            except Exception as e:
                failed += 1
                out["errors"]["matches"] = describe_err(e)
                continue
        sm = summarize_match(d, puuid, u.get("delta"))
        if not sm:
            continue
        sm["tier_after"], sm["rr_after"] = u.get("tier"), u.get("rr")
        me = next((p for p in d.get("players") or [] if p.get("subject") == puuid), {}) or {}
        sm["card"] = me.get("playerCard")
        sm["level"] = me.get("accountLevel")
        if me.get("gameName"):
            out.setdefault("name", f"{me['gameName']}#{me.get('tagLine', '')}")
        out["matches"].append(sm)
    if out["matches"]:
        out["card"] = out["matches"][0].get("card")
        out["level"] = out["matches"][0].get("level")
    out["failed_matches"] = failed
    return out


def send_friend_request(lf, name, puuid=None):
    gn, _, tag = name.partition("#")
    body = {"game_name": gn, "game_tag": tag}
    if puuid:
        body["puuid"] = puuid
    return local_get(lf, "/chat/v4/friendrequests", "POST", body)


def server_status(region):
    return game_status("val", region)


def parse_status(d):
    merged = {}
    for kind in ("incidents", "maintenances"):
        for it in d.get(kind) or []:
            title = next((t.get("content") for t in it.get("titles") or []
                          if str(t.get("locale", "")).startswith("en")), None) or "Issue"
            upd = next((u for u in reversed(it.get("updates") or []) if u), {})
            note = next((t.get("content") for t in upd.get("translations") or []
                         if str(t.get("locale", "")).startswith("en")), "")
            plats = it.get("platforms") or []
            key = (kind, title.strip().lower())
            e = merged.setdefault(key, {"kind": kind[:-1], "title": title.strip(), "count": 0,
                                        "platforms": set(), "note": "",
                                        "severity": it.get("incident_severity")
                                        or it.get("maintenance_status"),
                                        "updated": it.get("updated_at") or it.get("created_at")})
            e["count"] += 1
            e["platforms"].update(plats)
            if note and not e["note"]:
                e["note"] = note
    out = []
    for e in merged.values():
        e["platforms"] = sorted(e["platforms"])
        upd = _parse_time(e.get("updated"))
        e["old"] = bool(upd and time.time() - upd.timestamp() > 14 * 86400)
        plats = {p_.lower() for p_ in e["platforms"]}
        e["pc"] = not plats or "windows" in plats
        sev = str(e.get("severity") or "").lower()
        if e["kind"] == "maintenance":
            e["level"] = "maint"
        elif sev == "info":
            e["level"] = "info"
        elif sev == "critical":
            e["level"] = "critical"
        else:
            e["level"] = "warning"
        out.append(e)
    order = {"critical": 0, "warning": 1, "maint": 2, "info": 3}
    out.sort(key=lambda e: (e["old"], not e["pc"], order[e["level"]]))
    return out


def status_issues(items):
    """What actually affects a PC player right now."""
    return [e for e in items or [] if e.get("pc", True) and not e.get("old")
            and e.get("level", "warning") != "info"]


HENRIK = "https://api.henrikdev.xyz"
HENRIK_KEY_URL = "https://api.henrikdev.xyz/dashboard/"


class NeedKey(Exception):
    pass


def henrik_get(path, key=None, timeout=15):
    h = {"Accept": "application/json"}
    if key:
        h["Authorization"] = key
    try:
        return http(HENRIK + path, h, timeout=timeout) or {}
    except urllib.error.HTTPError as e:
        if e.code in (401, 403):
            raise NeedKey("HenrikDev needs a free API key") from e
        raise


def _tid(v):
    if isinstance(v, dict):
        return v.get("id") or 0
    return v or 0


def henrik_profile(puuid, region, key=None):
    """Rank, peak, level and recent RR for any account by PUUID - no login needed."""
    out = {}
    d = (henrik_get(f"/valorant/v3/by-puuid/mmr/{region}/pc/{puuid}", key).get("data") or {})
    cur = d.get("current") or {}
    if cur:
        out["tier"] = _tid(cur.get("tier"))
        out["rr"] = cur.get("rr", 0) or 0
    peak = d.get("peak") or {}
    if peak:
        out["peak_tier"] = _tid(peak.get("tier"))
        out["peak_act"] = str((peak.get("season") or {}).get("short") or "").upper()
    try:
        acc = henrik_get(f"/valorant/v2/by-puuid/account/{puuid}", key).get("data") or {}
        if acc.get("account_level"):
            out["level"] = acc["account_level"]
        if acc.get("name"):
            out["game_name"], out["tag"] = acc["name"], acc.get("tag")
    except NeedKey:
        raise
    except Exception:
        pass
    try:
        hist = henrik_get(f"/valorant/v2/by-puuid/mmr-history/{region}/pc/{puuid}",
                          key).get("data") or {}
        rows = []
        for hrow in hist.get("history") or []:
            t = _parse_time(hrow.get("date"))
            rows.append({"id": hrow.get("match_id"), "start": t.timestamp() if t else 0,
                         "tier": _tid(hrow.get("tier")), "rr": hrow.get("rr", 0) or 0,
                         "delta": hrow.get("last_change", 0) or 0,
                         "map": ((hrow.get("map") or {}).get("id") or "")})
        if rows:
            rows.sort(key=lambda r: r["start"])
            out["rr_history"] = rows[-60:]
    except NeedKey:
        raise
    except Exception:
        pass
    if out:
        out["ext_updated"] = time.time()
    return out


def henrik_leaderboard(region, page=1, size=50, key=None, name=None, tag=None):
    q = f"?size={size}&page={page}"
    if name:
        q += f"&name={urllib.parse.quote(name)}&tag={urllib.parse.quote(tag or '')}"
    r = henrik_get(f"/valorant/v3/leaderboard/{region}/pc{q}", key)
    d = r.get("data") or {}
    rows = []
    for p in d.get("players") or []:
        anon = p.get("is_anonymized") or not p.get("name")
        rows.append({"rank": p.get("leaderboard_rank"), "rr": p.get("rr", 0),
                     "wins": p.get("wins", 0), "tier": p.get("tier", 0), "card": p.get("card"),
                     "puuid": p.get("puuid"), "anon": bool(anon),
                     "name": "Secret Agent" if anon else f"{p['name']}#{p.get('tag', '')}"})
    return rows, ((r.get("results") or {}).get("total") or 0)


STATUS_REGIONS = {"eu": "Europe", "na": "North America", "ap": "Asia Pacific", "kr": "Korea",
                  "latam": "Latin America", "br": "Brazil"}
LOL_STATUS_REGION = {"eu": "euw1", "na": "na1", "ap": "oc1", "kr": "kr", "latam": "la1",
                     "br": "br1"}


def game_status(game, region):
    """Active incidents/maintenance for VALORANT or League in a region."""
    if game == "lol":
        url = (f"https://lol.secure.dyn.riotcdn.net/channels/public/x/status/"
               f"{LOL_STATUS_REGION.get(region, 'euw1')}.json")
    else:
        url = f"https://valorant.secure.dyn.riotcdn.net/channels/public/x/status/{region}.json"
    return parse_status(http(url, timeout=10) or {})


def league_lockfile():
    paths = []
    try:
        y = (Path(os.environ.get("PROGRAMDATA", r"C:\ProgramData")) / "Riot Games" / "Metadata" /
             "league_of_legends.live" / "league_of_legends.live.product_settings.yaml"
             ).read_text(encoding="utf-8", errors="ignore")
        m = re.search(r'product_install_full_path:\s*"?([^"\n]+)"?', y)
        if m:
            paths.append(Path(m.group(1).strip()) / "lockfile")
    except Exception:
        pass
    paths.append(Path(r"C:\Riot Games\League of Legends\lockfile"))
    for p in paths:
        try:
            parts = p.read_text(encoding="utf-8").strip().split(":")
            if len(parts) >= 5:
                return {"port": parts[2], "password": parts[3]}
        except Exception:
            continue
    return None


def fetch_league():
    lf = league_lockfile()
    if not lf:
        raise ClientDown("League client isn't open.")
    me = local_get(lf, "/lol-summoner/v1/current-summoner") or {}
    out = {"updated": time.time(), "name": me.get("gameName") or me.get("displayName"),
           "tag": me.get("tagLine"), "level": me.get("summonerLevel"),
           "icon": me.get("profileIconId"), "puuid": me.get("puuid"), "queues": {}}
    try:
        qm = (local_get(lf, "/lol-ranked/v1/current-ranked-stats") or {}).get("queueMap") or {}
        for q, label in (("RANKED_SOLO_5x5", "Solo/Duo"), ("RANKED_FLEX_SR", "Flex"),
                         ("RANKED_TFT", "TFT"), ("RANKED_TFT_DOUBLE_UP", "TFT Double Up")):
            e = qm.get(q) or {}
            if e.get("tier") and e["tier"] not in ("NONE", ""):
                out["queues"][label] = {"tier": e["tier"].title(), "div": e.get("division", ""),
                                        "lp": e.get("leaguePoints", 0), "w": e.get("wins", 0),
                                        "l": e.get("losses", 0)}
    except Exception:
        pass
    try:
        ms = local_get(lf, "/lol-champion-mastery/v1/local-player/champion-mastery") or []
        out["mastery"] = [{"id": x.get("championId"), "level": x.get("championLevel"),
                           "points": x.get("championPoints")} for x in ms[:8]]
    except Exception:
        out["mastery"] = []
    return out


def lol_ready_check(lf):
    """Accept a League ready check if one is waiting. Returns True if accepted."""
    try:
        rc = local_get(lf, "/lol-matchmaking/v1/ready-check") or {}
    except Exception:
        return False
    if rc.get("state") == "InProgress" and rc.get("playerResponse") == "None":
        local_get(lf, "/lol-matchmaking/v1/ready-check/accept", "POST")
        return True
    return False


def lol_random_skin(lf, done):
    """After you lock a champion, pick a random owned skin once per champ select."""
    import random
    try:
        ses = local_get(lf, "/lol-champ-select/v1/session") or {}
    except Exception:
        done.clear()
        return None
    cell = ses.get("localPlayerCellId")
    me = next((p for p in ses.get("myTeam") or [] if p.get("cellId") == cell), None)
    if not me or not me.get("championId"):
        return None
    locked = any(a.get("actorCellId") == cell and a.get("type") == "pick" and a.get("completed")
                 for group in ses.get("actions") or [] for a in group)
    key = (ses.get("gameId"), me["championId"])
    if not locked or key in done:
        return None
    done.add(key)
    skins = [sk for sk in local_get(lf, "/lol-champ-select/v1/skin-carousel-skins") or []
             if sk.get("unlocked") and not sk.get("disabled")
             and sk.get("championId") == me["championId"]]
    if len(skins) < 2:
        return None
    pick = random.choice([sk for sk in skins if sk.get("id") != me.get("selectedSkinId")] or skins)
    local_get(lf, "/lol-champ-select/v1/session/my-selection", "PATCH",
              {"selectedSkinId": pick["id"]})
    return pick.get("name") or "a random skin"


class DDragon:
    def __init__(self):
        self.version = None
        self.champs = {}

    def ensure(self):
        if self.version:
            return
        try:
            self.version = http("https://ddragon.leagueoflegends.com/api/versions.json")[0]
            data = http(f"https://ddragon.leagueoflegends.com/cdn/{self.version}/data/en_US/"
                        "champion.json")["data"]
            self.champs = {int(c["key"]): {"name": c["name"], "id": c["id"]} for c in data.values()}
        except Exception:
            self.version = None

    def champ_icon(self, cid):
        c = self.champs.get(cid)
        return (f"https://ddragon.leagueoflegends.com/cdn/{self.version}/img/champion/{c['id']}.png"
                if c and self.version else None)

    def profile_icon(self, iid):
        return (f"https://ddragon.leagueoflegends.com/cdn/{self.version}/img/profileicon/{iid}.png"
                if iid is not None and self.version else None)


DDRAGON = DDragon()
LEAGUE_COLORS = {"Iron": "#7b6f6a", "Bronze": "#a8714a", "Silver": "#9fb0ba", "Gold": "#e2b85c",
                 "Platinum": "#4fb3a3", "Emerald": "#2fbf71", "Diamond": "#6f8cff",
                 "Master": "#b05fe0", "Grandmaster": "#e0485a", "Challenger": "#f4d27a"}


# ================================================================ DPAPI (auto-backup password)
def dpapi(data: bytes, protect=True):
    if os.name != "nt":
        return data
    from ctypes import wintypes as wt

    class Blob(ctypes.Structure):
        _fields_ = [("cbData", wt.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]
    buf = ctypes.create_string_buffer(data, len(data))
    inp = Blob(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
    out = Blob()
    fn = ctypes.windll.crypt32.CryptProtectData if protect else ctypes.windll.crypt32.CryptUnprotectData
    if not fn(ctypes.byref(inp), None, None, None, None, 0x1, ctypes.byref(out)):
        raise ctypes.WinError()
    try:
        return ctypes.string_at(out.pbData, out.cbData)
    finally:
        ctypes.windll.kernel32.LocalFree(ctypes.cast(out.pbData, ctypes.c_void_p))


def pin_hash(pin, salt=None):
    salt = salt or secrets.token_hex(16)
    return salt, hashlib.pbkdf2_hmac("sha256", pin.encode(), bytes.fromhex(salt), 200_000).hex()


# ================================================================ appear offline / mobile
# The Riot Client is launched with a local client-config URL. That local server
# forwards config requests to Riot and points the chat server at a local TLS
# proxy, which forwards everything to the real chat server and only rewrites
# your own global <presence> broadcasts. Lobby/party chat is untouched.
LOCAL_CERT = """
-----BEGIN CERTIFICATE-----
MIIDJTCCAg2gAwIBAgIUQn5kPShREkQS4iOsKhq4h1TtJMgwDQYJKoZIhvcNAQEL
BQAwFDESMBAGA1UEAwwJMTI3LjAuMC4xMB4XDTI2MTExOTAwMTU1MloXDTM2MTEx
NjAwMTU1MlowFDESMBAGA1UEAwwJMTI3LjAuMC4xMIIBIjANBgkqhkiG9w0BAQEF
AAOCAQ8AMIIBCgKCAQEA3RXOZo6Ag4hacfurFVO6xAmJAyF6CPMbrBRiUDA3kT3q
nnItSPnIwV8YZi+XJedE8e1PeeEGyNLu8KG1ghqjh/fHiBukJtYBXaN0jL6RdWOr
ha4fPLiR3TdQOfKvSx0wVUwH9Bprx/LWE3Cjb5hM9Upp0QcrC/PFc1pGyeCDcfD2
OTs4HYvoRvj+WAFCKOETerpA4iA0abQbSlcaE9czMXCEb0zez9a2IllPUDbJPa61
sCj83nZRAKHMEAZdT5hCkn+z2e68XXjgj16B9HRyGgnvzul54RoFr4PBLb+kDqT9
RD3dVdZryNoSR3LlVQ72Ws1liF9y5SVpKS0Y4kKcfQIDAQABo28wbTAdBgNVHQ4E
FgQUnE33f7ZbwWhhopzqNRG8Ot8g6TMwHwYDVR0jBBgwFoAUnE33f7ZbwWhhopzq
NRG8Ot8g6TMwDwYDVR0TAQH/BAUwAwEB/zAaBgNVHREEEzARhwR/AAABgglsb2Nh
bGhvc3QwDQYJKoZIhvcNAQELBQADggEBAEAxRAPOTiAF17CmQIDK1xqECIFHvVeY
7I2GDXkPJZJHsvOYErybljlkLqUTwwy7imi5qehuGClNtKVwYX5yZHWZeQaoW2PR
jFBN/89SEWrnccXn1zCmFt50n4s744jVUhsREwTfpj9rnotTOzanzRCYyIssnI6d
qoqpSb0Bvr5UUni7awlxhvPvfJOXLj+WvXYonVoqCq6chYhbwBbiaQYtIvbpA4A0
MKSojv26JjrRibkmWn+B7ZifbQH0FNE6OD02M0o32fnEyh2NAFbj27gCQfLp/3Ct
2ZBefkYBCGSi0v/VfuFbsbk3Tf5b+GbUtsnI9qLBi6hhlIL8+kbonic=
-----END CERTIFICATE-----
"""
LOCAL_KEY = """
-----BEGIN PRIVATE KEY-----
MIIEvwIBADANBgkqhkiG9w0BAQEFAASCBKkwggSlAgEAAoIBAQDdFc5mjoCDiFpx
+6sVU7rECYkDIXoI8xusFGJQMDeRPeqeci1I+cjBXxhmL5cl50Tx7U954QbI0u7w
obWCGqOH98eIG6Qm1gFdo3SMvpF1Y6uFrh88uJHdN1A58q9LHTBVTAf0GmvH8tYT
cKNvmEz1SmnRBysL88VzWkbJ4INx8PY5Ozgdi+hG+P5YAUIo4RN6ukDiIDRptBtK
VxoT1zMxcIRvTN7P1rYiWU9QNsk9rrWwKPzedlEAocwQBl1PmEKSf7PZ7rxdeOCP
XoH0dHIaCe/O6XnhGgWvg8Etv6QOpP1EPd1V1mvI2hJHcuVVDvZazWWIX3LlJWkp
LRjiQpx9AgMBAAECggEAMTPVbc8YjE1X/aaKDnLGLbNGjg8Q+vVpyuv1bk2wzC7o
rG8SI3vNoTVx92nvfETCPAo5phD9wsto2F5QyB34F34+Jo0qROdbQfTq7xjJRAQU
y+kys/+KnN4eyWq4duHN3CnR2lJX+tWRLZ3jjaYqOGvhbV7oRl5v6spkVzDTaBOT
wA6gmRwfBmGz9gwct3+ETW4G228BjbYAKiz3MQi/DYDS9V8adNDgv+F2X1V23js6
OGoAT+SIBG/hbfy5tpSSS+kJ4uAyB0UHW6+TTsfooZeyP/np3fG+UG56/aO9lCik
/9ftdZj4BNhRpleAcgvEPAY9Xy8j62U32ecwVdRj8QKBgQDu4TFBq/b5FgCIBSxA
OqBP7rZ8mEX7Ro4OZjrwfu0zCZTt1vHlL6xsuNeSKiV1kjZen42ePL9INuU9TGhd
S6ovBuHOO4ugxoxA23Gk7vskxXBj2pUBsTnTdZghcCmsfKpx0wc4u9LoDdrMwmaG
X3CUGAn1tSefNFMZv7YzV4EVkQKBgQDs7iHmnczVxGc2q9q6r20L7qarn8+u9t0x
u+RJvKcgRF1FkCB1txULF/ufx29GTy86acV+rLkKjXTBPvYD7JA0xYct8pCjqFE7
4qZYEVJvTEQASTDfV61lb3q/ooIAk39V90kX8+luJ1Ax7utQxbB1G0R9VAlF2kAk
SxyqoOOyLQKBgQDWZJAzs6Y2SjPx4Eql3rgw5TstOfFdIyat77yoShKTQt9CUy7J
Fm93KLJ5QZBbI/3eEO8mfLjklDhMOr5UNWupR1D0KmcXxfrs3sbxU3ddukIzrGMd
oLUYfyspn6QXZdAH1nFdztzsXjromPUxVokQsT6HIq5L6cdHjdN14uw8sQKBgQDM
lqihahupb2os1GMQl1DTX+V+B4afr727J2LupT+vZjkgS18sJsa+CJyYEO+uR8wh
ZZpLUzyJtzJdeE+ZfdncJ8Ed1Po+x6Y1zvYS0Apd3v5NPOY9xYkOMSBOgDY/5x2q
jtkIHO+x1bKzG3sJCVvhE4Wlrz4+mkKO1GlRkZJslQKBgQCcPJxv1fCX2i0WBxUe
hCPyzr2DYYH3mHAtvjNoiuv02Edll+fo5yKR/VryL+1hHlHltO+gWorM+7klgbQf
OoWkxvYEKYiFZYASt83FgfvzrYB31oDZaw3zFE3A+DtWyYH2+2bsP7COmoZL0fHg
/3dlxfJELqmV4gF03McjyXLvmw==
-----END PRIVATE KEY-----
"""
STATUS_MODES = {"online": "Online", "offline": "Offline", "mobile": "Mobile"}


def rewrite_presence(stanza, mode):
    if mode == "online":
        return stanza
    gt = stanza.find(">")
    head = stanza[:gt + 1] if gt >= 0 else stanza
    if re.search(r"\s(to|type)=", head) or head.rstrip().endswith("/>"):
        return stanza  # directed (lobby/party) presence or a probe: leave it alone
    s = re.sub(r"<games>.*?</games>|<games\s*/>", "", stanza, flags=re.S)
    s = re.sub(r"<status>.*?</status>", "<status/>", s, flags=re.S)
    show = "offline" if mode == "offline" else "mobile"
    if re.search(r"<show>.*?</show>", s, flags=re.S):
        s = re.sub(r"<show>.*?</show>", f"<show>{show}</show>", s, flags=re.S)
    else:
        s = s.replace("</presence>", f"<show>{show}</show></presence>")
    return s


def split_presence_stream(buf, tag="<presence"):
    """Split an XMPP text stream into raw chunks and complete <presence> stanzas."""
    out = []
    while True:
        i = buf.find(tag)
        if i == -1:
            keep = 0
            for n in range(min(len(buf), len(tag) - 1), 0, -1):
                if tag.startswith(buf[-n:]):
                    keep = n
                    break
            if len(buf) - keep:
                out.append(("raw", buf[:len(buf) - keep]))
            return out, buf[len(buf) - keep:]
        if i:
            out.append(("raw", buf[:i]))
            buf = buf[i:]
        gt = buf.find(">")
        if gt == -1:
            return out, buf
        close = "</" + tag[1:] + ">"
        if buf[gt - 1] == "/":
            end = gt + 1
        else:
            e = buf.find(close)
            if e == -1:
                return out, buf
            end = e + len(close)
        out.append((tag[1:], buf[:end]))
        buf = buf[end:]


class StatusProxy:
    def __init__(self, on_event=None):
        self.mode = "online"
        self.on_event = on_event or (lambda kind, info: None)
        self.started = False
        self.cfg_port = self.chat_port = None
        self.real_host, self.real_port = None, 5223
        self.conns = []
        self.lock = threading.Lock()
        self.control = False
        self.jid = self.domain = None

    def start(self):
        if self.started:
            return
        APP_DIR.mkdir(parents=True, exist_ok=True)
        cert, key = APP_DIR / "local_chat_cert.pem", APP_DIR / "local_chat_key.pem"
        cert.write_text(LOCAL_CERT.strip() + "\n", encoding="ascii")
        key.write_text(LOCAL_KEY.strip() + "\n", encoding="ascii")
        self.srv_ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.srv_ctx.load_cert_chain(str(cert), str(key))
        self.chat_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.chat_sock.bind(("127.0.0.1", 0))
        self.chat_sock.listen(8)
        self.chat_port = self.chat_sock.getsockname()[1]
        threading.Thread(target=self._accept_loop, daemon=True).start()
        proxy = self

        class Handler(BaseHTTPRequestHandler):
            def do_GET(h):
                proxy._config_request(h)

            def log_message(h, *a):
                pass

        self.httpd = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.cfg_port = self.httpd.server_address[1]
        threading.Thread(target=self.httpd.serve_forever, daemon=True).start()
        self.started = True

    def config_url(self):
        return f"http://127.0.0.1:{self.cfg_port}"

    @property
    def connected(self):
        return bool(self.conns)

    # ---- config proxy
    def _config_request(self, h):
        url = "https://clientconfig.rpg.riotgames.com" + h.path
        fwd = {}
        for k in ("User-Agent", "Authorization", "X-Riot-Entitlements-JWT",
                  "X-Riot-RSO-Identity-JWT", "Accept"):
            v = h.headers.get(k)
            if v:
                fwd[k] = v
        status, body, ctype = 502, b"{}", "application/json"
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=fwd),
                                        timeout=20) as r:
                status, body = r.status, r.read()
                ctype = r.headers.get("Content-Type", ctype)
        except urllib.error.HTTPError as e:
            status, body = e.code, e.read() or b""
        except Exception as e:
            self.on_event("error", f"config: {e}")
        if status == 200:
            try:
                cfg = json.loads(body)
                if isinstance(cfg, dict) and self.patch_config(cfg, h.headers.get("Authorization")):
                    body = json.dumps(cfg).encode()
            except Exception:
                pass
        try:
            h.send_response(status)
            h.send_header("Content-Type", ctype)
            h.send_header("Content-Length", str(len(body)))
            h.end_headers()
            h.wfile.write(body)
        except Exception:
            pass

    def patch_config(self, cfg, auth=None):
        touched = False
        if isinstance(cfg.get("chat.host"), str):
            if cfg["chat.host"] != "127.0.0.1":
                self.real_host = cfg["chat.host"]
            cfg["chat.host"] = "127.0.0.1"
            touched = True
        if "chat.port" in cfg:
            try:
                if int(cfg["chat.port"]) != self.chat_port:
                    self.real_port = int(cfg["chat.port"])
            except (TypeError, ValueError):
                pass
            cfg["chat.port"] = self.chat_port
            touched = True
        aff = cfg.get("chat.affinities")
        if isinstance(aff, dict) and aff:
            real = {k: v for k, v in aff.items() if v != "127.0.0.1"}
            if real:
                picked = None
                if cfg.get("chat.affinity.enabled") and auth:
                    try:
                        tok = http("https://riot-geo.pas.si.riotgames.com/pas/v1/service/chat",
                                   {"Authorization": auth}, raw=True).decode().strip().strip('"')
                        a = jwt_payload(tok).get("affinity")
                        picked = real.get(a)
                    except Exception:
                        pass
                if picked:
                    self.real_host = picked
                elif not self.real_host:
                    self.real_host = next(iter(real.values()))
            cfg["chat.affinities"] = {k: "127.0.0.1" for k in aff}
            touched = True
        if touched:
            cfg["chat.allow_bad_cert.enabled"] = True
        return touched

    # ---- chat proxy
    def _accept_loop(self):
        while True:
            try:
                c, _ = self.chat_sock.accept()
            except OSError:
                return
            threading.Thread(target=self._handle, args=(c,), daemon=True).start()

    def _handle(self, raw):
        client = up = None
        try:
            client = self.srv_ctx.wrap_socket(raw, server_side=True)
            host = self.real_host
            if not host:
                raise RuntimeError("chat server unknown (config wasn't intercepted)")
            up_raw = socket.create_connection((host, self.real_port), timeout=15)
            up = WEB_CTX.wrap_socket(up_raw, server_hostname=host)
            up.settimeout(None)
            client.settimeout(None)
        except Exception as e:
            self.on_event("error", f"chat: {e}")
            for s in (client, up, raw):
                try:
                    s and s.close()
                except Exception:
                    pass
            return
        conn = {"up": up, "client": client, "last": None, "lock": threading.Lock(),
                "clock": threading.Lock(), "roster": False, "injected": False}
        with self.lock:
            self.conns.append(conn)
        self.on_event("connected", host)
        threading.Thread(target=self._pump_down, args=(conn,), daemon=True).start()
        self._pump_up(conn)

    def _close(self, conn):
        for k in ("up", "client"):
            try:
                conn[k].close()
            except Exception:
                pass
        with self.lock:
            if conn in self.conns:
                self.conns.remove(conn)
                self.on_event("disconnected", None)

    def _send_up(self, conn, text):
        with conn["lock"]:
            conn["up"].sendall(text.encode("utf-8"))

    CONTROL = "rasw-control"

    def _send_down(self, conn, text):
        with conn["clock"]:
            conn["client"].sendall(text.encode("utf-8"))

    def _pump_down(self, conn):
        import codecs
        dec = codecs.getincrementaldecoder("utf-8")("replace")
        try:
            while True:
                data = conn["up"].recv(65536)
                if not data:
                    break
                text = dec.decode(data)
                if not self.jid:
                    m = re.search(r"<jid>([^<@]+@([^</]+)[^<]*)</jid>", text)
                    if m:
                        self.jid, self.domain = m.group(1), m.group(2)
                if self.control and self.domain and not conn["injected"]:
                    if "roster" in text and "<query" in text:
                        conn["roster"] = True
                    if conn["roster"] and "</query>" in text:
                        item = (f"<item jid='{self.CONTROL}@{self.domain}' name='RiotHub' "
                                f"subscription='both' puuid='{self.CONTROL}'>"
                                "<group priority='9999'>RiotHub</group>"
                                "<id name='RiotHub' tagline='CTRL'/></item>")
                        text = text.replace("</query>", item + "</query>", 1)
                        conn["injected"] = True
                        self._send_down(conn, text)
                        self._control_presence(conn)
                        continue
                self._send_down(conn, text)
        except Exception:
            pass
        self._close(conn)

    def _control_presence(self, conn):
        ms = int(time.time() * 1000)
        self._send_down(conn, (
            f"<presence from='{self.CONTROL}@{self.domain}/RC-switcher' to='{self.jid}'>"
            f"<games><keystone><st>chat</st><s.t>{ms}</s.t>"
            "<m>Message me: online, offline or mobile</m><s.p>keystone</s.p></keystone></games>"
            "<show>chat</show><status/></presence>"))

    def _reply(self, conn, msg):
        from xml.sax.saxutils import escape
        mid = secrets.token_hex(6)
        stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S.000")
        self._send_down(conn, (
            f"<message from='{self.CONTROL}@{self.domain}/RC-switcher' to='{self.jid}' "
            f"stamp='{stamp}' id='{mid}' type='chat'><body>{escape(msg)}</body></message>"))

    def _handle_control(self, conn, stanza):
        from html import unescape
        m = re.search(r"<body>(.*?)</body>", stanza, re.S)
        cmd = unescape(m.group(1)).strip().lower() if m else ""
        if cmd in STATUS_MODES:
            self.set_mode(cmd)
            self.on_event("mode", cmd)
            self._reply(conn, f"You now appear {STATUS_MODES[cmd].lower()}.")
        elif cmd in ("status", "?"):
            self._reply(conn, f"You appear {STATUS_MODES.get(self.mode, self.mode).lower()}.")
        else:
            self._reply(conn, "Commands: online, offline, mobile, status")

    def _pump_up(self, conn):
        import codecs
        dec = codecs.getincrementaldecoder("utf-8")("replace")
        buf = ""
        try:
            while True:
                data = conn["client"].recv(65536)
                if not data:
                    break
                buf += dec.decode(data)
                segs, buf = split_presence_stream(buf)
                if self.control and self.domain:
                    expanded = []
                    for kind, text in segs:
                        if kind == "raw" and "<message" in text:
                            sub, rest = split_presence_stream(text, "<message")
                            expanded += sub
                            if rest:
                                expanded.append(("raw", rest))
                        else:
                            expanded.append((kind, text))
                    segs = []
                    for kind, text in expanded:
                        if kind == "message" and re.search(
                                r"\sto=['\"]" + self.CONTROL + "@", text[:text.find(">") + 1]):
                            self._handle_control(conn, text)
                        else:
                            segs.append((kind, text))
                out = []
                for kind, text in segs:
                    if kind == "presence":
                        head = text[:text.find(">") + 1]
                        if not re.search(r"\s(to|type)=", head) and not head.endswith("/>"):
                            conn["last"] = text
                        text = rewrite_presence(text, self.mode)
                    out.append(text)
                if out:
                    self._send_up(conn, "".join(out))
        except Exception:
            pass
        self._close(conn)

    def set_mode(self, mode):
        self.mode = mode
        with self.lock:
            conns = list(self.conns)
        for c in conns:
            if c["last"]:
                try:
                    self._send_up(c, rewrite_presence(c["last"], mode))
                except Exception:
                    pass


GAME_LOOK = {   # colour + art for the launcher cards
    "VALORANT": {"color": "#ff4655", "tag": "Tactical shooter"},
    "League / TFT": {"color": "#c8aa6e", "tag": "League of Legends · Teamfight Tactics",
                     "art": "https://ddragon.leagueoflegends.com/cdn/img/champion/splash/"
                            "Jinx_0.jpg"},
    "Runeterra": {"color": "#2ad1c9", "tag": "Legends of Runeterra",
                  "art": "https://ddragon.leagueoflegends.com/cdn/img/champion/splash/"
                         "Viego_0.jpg"},
    "2XKO": {"color": "#e04fd0", "tag": "Tag-team fighter",
             "art": "https://ddragon.leagueoflegends.com/cdn/img/champion/splash/Ekko_0.jpg"},
}


def fetch_news(key=None, lang="en-us"):
    """Latest VALORANT news/patch notes (HenrikDev mirrors playvalorant.com)."""
    d = henrik_get(f"/valorant/v1/website/{lang}", key) or {}
    out = []
    for a in (d.get("data") or [])[:8]:
        t = _parse_time(a.get("date"))
        out.append({"title": a.get("title") or "", "url": a.get("external_link") or a.get("url"),
                    "img": a.get("banner_url"), "cat": (a.get("category") or "").replace("_", " "),
                    "date": t.timestamp() if t else None})
    return out


def capture_folders():
    """Where Riot games and Windows keep screenshots / clips on this PC."""
    home = Path.home()
    la = Path(os.environ.get("LOCALAPPDATA", home / "AppData" / "Local"))
    cands = [("VALORANT", la / "VALORANT" / "Saved" / "Screenshots"),
             ("VALORANT", home / "Documents" / "VALORANT" / "Screenshots"),
             ("League", Path(r"C:\Riot Games\League of Legends\Screenshots")),
             ("League highlights", home / "Documents" / "League of Legends" / "Highlights"),
             ("Game Bar clips", home / "Videos" / "Captures")]
    lol = league_install_dir() if "league_install_dir" in globals() else None
    if lol:
        cands.insert(2, ("League", Path(lol) / "Screenshots"))
    seen, out = set(), []
    for lab, p in cands:
        try:
            if p.is_dir() and str(p).lower() not in seen:
                seen.add(str(p).lower())
                out.append((lab, p))
        except OSError:
            pass
    return out


def latest_captures(folders, n=4):
    files = []
    for lab, p in folders:
        try:
            for f in p.iterdir():
                if f.suffix.lower() in (".png", ".jpg", ".jpeg", ".bmp"):
                    files.append((f.stat().st_mtime, f, lab))
        except OSError:
            continue
    files.sort(reverse=True)
    return files[:n]


def version_tuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", str(v))[:4]) or (0,)


def check_for_update(repo):
    r = http(f"https://api.github.com/repos/{repo}/releases/latest",
             {"Accept": "application/vnd.github+json"}, timeout=10) or {}
    tag = r.get("tag_name") or ""
    if version_tuple(tag) <= version_tuple(VERSION):
        return None
    exes = [a for a in r.get("assets") or [] if a.get("name", "").lower().endswith(".exe")]
    # the app itself, not the "Setup" installer that sits next to it in each release
    exe = (next((a for a in exes if a["name"].lower() == f"{APP_TITLE}.exe".lower()), None)
           or next((a for a in exes if "setup" not in a["name"].lower()), None))
    setup = next((a for a in exes if "setup" in a["name"].lower()), None)
    return {"version": tag.lstrip("vV"), "notes": (r.get("body") or "").strip(),
            "page": r.get("html_url"), "exe": exe and exe.get("browser_download_url"),
            "size": exe and exe.get("size"),
            "setup": setup and setup.get("browser_download_url"),
            "setup_size": setup and setup.get("size")}


def is_installed_copy(exe=None):
    """True when this is the installed RiotHub (Setup.exe), not the portable single file.
    Installed copies update by re-running the new installer silently, which keeps the
    fast-starting folder layout and the Start menu entries."""
    if not getattr(sys, "frozen", False) and exe is None:
        return False
    d = Path(exe or sys.executable).parent
    return (d / "unins000.exe").exists() or (d / "_internal").is_dir()


def launch_via_client(product, lf=None):
    """Ask an already-running, signed-in Riot Client to start a game. This is what makes Play
    instant: no new process, no restart."""
    lf = lf or read_lockfile()
    if not lf:
        return False
    try:
        local_get(lf, f"/product-launcher/v1/products/{product}/patchlines/live", "POST",
                  timeout=6)
        return True
    except Exception:
        return False


def riot_client_windows():
    """Top-level windows that belong to the Riot Client UI."""
    out = []
    try:
        u = ctypes.windll.user32
        from ctypes import wintypes
        proto = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)

        def cb(hwnd, _):
            if u.IsWindowVisible(hwnd):
                buf = ctypes.create_unicode_buffer(128)
                u.GetWindowTextW(hwnd, buf, 128)
                if buf.value.strip() == "Riot Client":
                    out.append(hwnd)
            return True
        u.EnumWindows(proto(cb), 0)
    except Exception:
        pass
    return out


def tuck_riot_client(wait=25, only_if_signed_in=True):
    """Minimise the Riot Client window once it's up (but never hide a login screen)."""
    end = time.time() + wait
    while time.time() < end:
        wins = riot_client_windows()
        if wins:
            if only_if_signed_in:
                lf = read_lockfile()
                try:
                    if not lf:
                        raise ClientDown("")
                    local_tokens(lf)
                except Exception:
                    time.sleep(0.8)
                    continue
            for hwnd in wins:
                try:
                    ctypes.windll.user32.ShowWindow(hwnd, 6)   # SW_MINIMIZE
                except Exception:
                    pass
            return True
        time.sleep(0.5)
    return False


def game_running(product):
    exe = GAME_EXE.get(product or "")
    return bool(exe) and exe.lower() in running_processes()


def launch_client(product, status=None):
    """Start the Riot Client (optionally through the status proxy or Deceive)."""
    status = status or {}
    mode = status.get("mode", "online")
    engine = status.get("engine", "builtin")
    dpath = status.get("deceive_path") or ""
    if mode != "online" and engine == "deceive":
        if not dpath or not Path(dpath).exists():
            raise RuntimeError("Deceive.exe not found. Set its location in Settings > Status.")
        args = [dpath] + ([DECEIVE_ARG[product]] if product in DECEIVE_ARG else [])
        start_process(args, cwd=str(Path(dpath).parent))
        return "deceive"
    exe = client_exe()
    if not exe:
        raise RuntimeError("Riot Client not found. Is it installed?")
    args = [exe]
    proxy = status.get("proxy")
    if proxy is not None and engine == "builtin" and status.get("enabled"):
        proxy.start()
        args.append(f"--client-config-url={proxy.config_url()}")
    if product:
        args += [f"--launch-product={product}", "--launch-patchline=live"]
    start_process(args, flags=NO_WINDOW)
    return "proxy" if len(args) > 1 and "--client-config-url" in args[1] else "plain"


# ================================================================ encrypted backups
BACKUP_MAGIC = b"RASB1"


def _keystream(key, nonce, n):
    out = bytearray()
    ctr = 0
    while len(out) < n:
        out += hmac.new(key, nonce + ctr.to_bytes(8, "big"), hashlib.sha256).digest()
        ctr += 1
    return bytes(out[:n])


def _xor(a, b):
    if not a:
        return b""
    return (int.from_bytes(a, "big") ^ int.from_bytes(b, "big")).to_bytes(len(a), "big")


def _keys(password, salt):
    km = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 300_000, dklen=64)
    return km[:32], km[32:]


def encrypt_blob(data, password):
    salt, nonce = secrets.token_bytes(16), secrets.token_bytes(16)
    ek, mk = _keys(password, salt)
    ct = _xor(data, _keystream(ek, nonce, len(data)))
    tag = hmac.new(mk, BACKUP_MAGIC + salt + nonce + ct, hashlib.sha256).digest()
    return BACKUP_MAGIC + salt + nonce + tag + ct


def decrypt_blob(blob, password):
    if not blob.startswith(BACKUP_MAGIC) or len(blob) < 5 + 16 + 16 + 32:
        raise ValueError("That isn't a RiotHub backup.")
    p = len(BACKUP_MAGIC)
    salt, nonce, tag, ct = blob[p:p + 16], blob[p + 16:p + 32], blob[p + 32:p + 64], blob[p + 64:]
    ek, mk = _keys(password, salt)
    want = hmac.new(mk, BACKUP_MAGIC + salt + nonce + ct, hashlib.sha256).digest()
    if not hmac.compare_digest(want, tag):
        raise ValueError("Wrong password, or the file is damaged.")
    return _xor(ct, _keystream(ek, nonce, len(ct)))


def make_backup(password):
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        for sub in ("accounts", "meta", "prefs", "prefs_backups"):
            root = APP_DIR / sub
            if root.exists():
                for f in root.rglob("*"):
                    if f.is_file():
                        z.write(f, f.relative_to(APP_DIR).as_posix())
        if STATE.exists():
            z.write(STATE, "state.json")
    return encrypt_blob(buf.getvalue(), password)


def restore_backup(blob, password):
    data = decrypt_blob(blob, password)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for info in z.infolist():
            name = info.filename
            parts = Path(name).parts
            if name.startswith(("/", "\\")) or ".." in parts or ":" in name:
                continue
            if parts[0] not in ("accounts", "meta", "prefs", "prefs_backups", "state.json"):
                continue
            dst = APP_DIR / name
            dst.parent.mkdir(parents=True, exist_ok=True)
            with z.open(info) as src, open(dst, "wb") as out:
                shutil.copyfileobj(src, out)


# ================================================================ windows integration
def launch_target():
    if getattr(sys, "frozen", False):
        return sys.executable, ""
    exe = Path(sys.executable)
    pyw = exe.with_name("pythonw.exe")
    return str(pyw if pyw.exists() else exe), f'"{Path(__file__).resolve()}"'


def set_autostart(on):
    import winreg
    key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                         r"Software\Microsoft\Windows\CurrentVersion\Run", 0,
                         winreg.KEY_SET_VALUE)
    for old in OLD_APP_NAMES:
        try:
            winreg.DeleteValue(key, old)
        except OSError:
            pass
    try:
        if on:
            target, args = launch_target()
            winreg.SetValueEx(key, APP_NAME, 0, winreg.REG_SZ,
                              " ".join(x for x in (f'"{target}"', args, "--tray") if x))
        else:
            try:
                winreg.DeleteValue(key, APP_NAME)
            except FileNotFoundError:
                pass
    finally:
        winreg.CloseKey(key)


def create_shortcut(name, icon_path=None, game=None):
    target, args = launch_target()
    args = f'{args} --login "{name}"'.strip()
    if game and game in GAMES:
        args += f' --game "{game}"'
    ps = ("$d=[Environment]::GetFolderPath('Desktop');"
          "$s=(New-Object -ComObject WScript.Shell).CreateShortcut("
          "(Join-Path $d ($env:SC_TITLE + '.lnk')));"
          "$s.TargetPath=$env:SC_TARGET;$s.Arguments=$env:SC_ARGS;"
          "$s.WorkingDirectory=$env:SC_WD;"
          "if($env:SC_ICON){$s.IconLocation=$env:SC_ICON};"
          "$s.Description='RiotHub';$s.Save()")
    title = f"{game} - {name}" if game and GAMES.get(game) else f"Log in as {name}"
    title = re.sub(r'[\\/:*?"<>|]', "", title)
    env = dict(os.environ, SC_TITLE=title, SC_TARGET=target, SC_ARGS=args,
               SC_WD=str(Path(target).parent), SC_ICON=str(icon_path or ""))
    r = subprocess.run(["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass",
                        "-Command", ps], env=env, capture_output=True, text=True,
                       creationflags=NO_WINDOW)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip() or "PowerShell couldn't create the shortcut.")


def ipc_send(msg):
    try:
        with socket.create_connection(("127.0.0.1", IPC_PORT), timeout=1) as s:
            s.sendall(json.dumps(msg).encode())
        return True
    except OSError:
        return False


if os.name == "nt":
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32


class Hotkeys(threading.Thread):
    """Ctrl+Alt+1..9 -> log into account 1..9 (tile order)."""

    def __init__(self, on_hotkey):
        super().__init__(daemon=True)
        self.on_hotkey = on_hotkey
        self.tid = None
        self.failed = []

    def run(self):
        self.tid = kernel32.GetCurrentThreadId()
        ok = []
        for i in range(10):
            vk = 0x31 + i if i < 9 else 0x30  # 1..9, then 0 = switch back
            if user32.RegisterHotKey(None, i + 1, 0x0001 | 0x0002 | 0x4000, vk):
                ok.append(i + 1)
            else:
                self.failed.append(i + 1 if i < 9 else 0)
        if user32.RegisterHotKey(None, 11, 0x0001 | 0x0002 | 0x4000, 0x50):   # Ctrl+Alt+P
            ok.append(11)
        msg = wintypes.MSG()
        while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
            if msg.message == 0x0312:
                self.on_hotkey(int(msg.wParam) - 1)
        for i in ok:
            user32.UnregisterHotKey(None, i)

    def stop(self):
        if self.tid:
            user32.PostThreadMessageW(self.tid, 0x0012, 0, 0)


def dark_titlebar(win):
    try:
        win.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(win.winfo_id())
        on = ctypes.c_int(1)
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(on), 4)
        r, g, b = (int(BG[i:i + 2], 16) for i in (1, 3, 5))
        color = ctypes.c_int(r | (g << 8) | (b << 16))
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 35, ctypes.byref(color), 4)
    except Exception:
        pass


def _rgb(hx):
    hx = hx.lstrip("#")
    return tuple(int(hx[i:i + 2], 16) for i in (0, 2, 4))


_LOGO_CACHE = {}


def make_app_icon(size=256, accent=None, accent_hi=None, tray=None):
    """App mark: a glowing diamond ring around a solid diamond with a centred play button,
    on a dark tile. Small/tray sizes drop the tile (and below 20px the ring) so it stays
    crisp. Follows the theme colour."""
    from PIL import ImageFilter, ImageChops
    accent, accent_hi = accent or ACCENT, accent_hi or ACCENT_HI
    tray = size <= 24 if tray is None else tray
    key = (size, accent, accent_hi, tray)
    if key in _LOGO_CACHE:
        return _LOGO_CACHE[key].copy()
    S = int(min(1024, max(256, size * 4)))
    c = S / 2
    P1, P2 = _rgb(accent_hi), _rgb(accent)
    P3 = tuple(int(v * 0.55) for v in P2)

    def grad(a, b):
        g = Image.new("RGB", (64, 64))
        g.putdata([tuple(int(a[k] + (b[k] - a[k]) * (x + y) / 126) for k in range(3))
                   for y in range(64) for x in range(64)])
        return g.resize((S, S), Image.BICUBIC).convert("RGBA")

    def rdiamond(r, rnd, width=None):
        side = r * math.sqrt(2)
        box = Image.new("L", (S, S), 0)
        bd = ImageDraw.Draw(box)
        bd.rounded_rectangle((c - side / 2, c - side / 2, c + side / 2, c + side / 2),
                             int(side * rnd), fill=255)
        if width:
            w2 = side - 2 * width
            bd.rounded_rectangle((c - w2 / 2, c - w2 / 2, c + w2 / 2, c + w2 / 2),
                                 int(w2 * rnd * .8), fill=0)
        return box.rotate(45, resample=Image.BICUBIC, center=(c, c))

    def play(r):
        cx = c + r * 0.12            # optical centre of a play triangle
        m = Image.new("L", (S, S), 0)
        ImageDraw.Draw(m).polygon([(cx + r * math.cos(math.radians(a)),
                                    c + r * math.sin(math.radians(a))) for a in (0, 120, 240)],
                                  fill=255)
        return m.filter(ImageFilter.GaussianBlur(r * .11)).point(lambda v: 255 if v > 128 else 0)

    def paint(im, mask, fill, glow=0):
        if glow:
            gl = Image.new("RGBA", (S, S), P2 + (0,))
            gl.putalpha(mask.point(lambda v: v * glow // 255))
            im.alpha_composite(gl.filter(ImageFilter.GaussianBlur(S * .045)))
        lay = fill.copy() if isinstance(fill, Image.Image) else Image.new("RGBA", (S, S), fill)
        lay.putalpha(ImageChops.multiply(lay.getchannel("A"), mask))
        im.alpha_composite(lay)

    im = Image.new("RGBA", (S, S), (0, 0, 0, 0))
    tile = None
    k = 1.32 if tray else 1.0
    if not tray:
        top, bot = (32, 26, 46), (12, 10, 18)
        g = Image.new("RGB", (1, 64))
        g.putdata([tuple(int(top[j] + (bot[j] - top[j]) * y / 63) for j in range(3))
                   for y in range(64)])
        tile = Image.new("L", (S, S), 0)
        ImageDraw.Draw(tile).rounded_rectangle((0, 0, S - 1, S - 1), int(S * .24), fill=255)
        im.paste(g.resize((S, S), Image.BICUBIC), (0, 0), tile)
        hl = Image.new("L", (S, S), 0)
        ImageDraw.Draw(hl).rounded_rectangle((0, 0, S - 1, S - 1), int(S * .24), outline=55,
                                             width=max(2, S // 170))
        fade = Image.linear_gradient("L").resize((S, S)).point(lambda v: 255 - v)
        im.alpha_composite(Image.merge("RGBA", (Image.new("L", (S, S), 255),) * 3
                                       + (ImageChops.multiply(hl, fade),)))
    if tray and size <= 20:
        paint(im, rdiamond(S * .5, .12), grad(P1, P3))
        paint(im, play(S * .2), (255, 255, 255, 255))
    else:
        paint(im, rdiamond(S * .37 * k, .14, width=S * (.04 if not tray else .07) * k),
              grad(P1, P2), glow=0 if tray else 120)
        paint(im, rdiamond(S * .22 * k, .14), grad(P1, P3))
        paint(im, play(S * .075 * k), (255, 255, 255, 255))
    if tile is not None:
        im.putalpha(ImageChops.multiply(im.getchannel("A"), tile))
    out = im.resize((size, size), Image.LANCZOS)
    if len(_LOGO_CACHE) > 40:
        _LOGO_CACHE.clear()
    _LOGO_CACHE[key] = out
    return out.copy()


def make_ico(path):
    """Multi-size .ico: tiled logo for big sizes, the bold tray version for tiny ones."""
    sizes = [16, 20, 24, 32, 40, 48, 64, 128, 256]
    imgs = [make_app_icon(sz) for sz in sizes]
    imgs[-1].save(path, sizes=[(x, x) for x in sizes], append_images=imgs[:-1])


ICON_CODES_EXTRA = {"volume": "\ue767", "mute": "\ue74f", "stop": "\ue71a",
                    "fullscreen": "\ue740", "pause": "\ue769"}
ICON_CODES = {"home": "", "add": "", "save": "", "play": "",
              "edit": "", "delete": "", "sync": "", "folder": "",
              "game": "", "person": "", "bolt": "", "rocket": "",
              "settings": "", "link": "", "refresh": "", "search": "",
              "warning": "", "grid": "", "list": "", "shop": "",
              "star": "", "star_on": "", "compare": "", "copy": "",
              "shield": "", "history": "", "eye": "", "eye_off": "",
              "close": "", "check": "", "clock": "", "trophy": "",
              "lock": "", "upload": "", "download": "",
              "palette": "", "chat": "", "phone": "", "moon": "",
              "chevron": "", "film": "", "info": "", "tag": ""}
ICON_FALLBACK_EXTRA = {"volume": "♪", "mute": "×", "stop": "■", "fullscreen": "⛶",
                       "pause": "‖"}
ICON_FALLBACK = {"home": "⌂", "add": "+", "save": "↓", "play": "▶", "edit": "✎",
                 "delete": "✕", "sync": "⟳", "folder": "▤", "game": "◆", "person": "●",
                 "bolt": "⚡", "rocket": "➚", "settings": "⚙", "link": "↗", "refresh": "↻",
                 "search": "⌕", "warning": "!", "grid": "▦", "list": "≡", "shop": "$",
                 "star": "☆", "star_on": "★", "compare": "⇄", "copy": "⧉", "shield": "⛨",
                 "history": "↺", "eye": "◉", "eye_off": "◌", "close": "✕", "check": "✓",
                 "clock": "◷", "trophy": "♛", "lock": "🔒", "upload": "↑", "download": "↓",
                 "palette": "◐", "chat": "✉", "phone": "▯", "moon": "☾", "chevron": "›",
                 "film": "▶", "info": "i", "tag": "#"}
ICON_CODES.update(ICON_CODES_EXTRA)
ICON_FALLBACK.update(ICON_FALLBACK_EXTRA)


# ================================================================ images
class Images:
    def __init__(self, app):
        self.app = app
        self.photos = {}
        self.pending, self.failed = set(), set()
        self.listeners = set()
        self.pool = ThreadPoolExecutor(max_workers=8)
        IMG_DIR.mkdir(parents=True, exist_ok=True)

    @staticmethod
    def path(url):
        return IMG_DIR / (hashlib.sha1(url.encode()).hexdigest() + ".png")

    def get(self, url, w, h, mode="contain", radius=0, fade=False, gray=False):
        if not url:
            return None
        w, h = max(1, int(w)), max(1, int(h))
        key = (url, w, h, mode, radius, fade, gray)
        if key in self.photos:
            return self.photos[key]
        p = self.path(url)
        if p.exists():
            try:
                self.photos[key] = self._build(p, w, h, mode, radius, fade, gray)
                if len(self.photos) > 1500:
                    for k in list(self.photos)[:300]:
                        self.photos.pop(k, None)
                return self.photos[key]
            except Exception:
                p.unlink(missing_ok=True)
        if url not in self.pending and url not in self.failed:
            self.pending.add(url)
            self.pool.submit(self._download, url, p)
        return None

    def _download(self, url, p):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=20) as r:
                data = r.read()
            tmp = p.with_suffix(".part")
            tmp.write_bytes(data)
            tmp.replace(p)
        except Exception:
            self.failed.add(url)
        finally:
            self.pending.discard(url)
            self.app.call_ui(self._notify)

    def _notify(self):
        self.app.redraw()
        for fn in list(self.listeners):
            try:
                fn()
            except Exception:
                self.listeners.discard(fn)

    @staticmethod
    def _build(path, w, h, mode, radius, fade, gray):
        im = Image.open(path).convert("RGBA")
        if mode == "cover":
            im = ImageOps.fit(im, (w, h), Image.LANCZOS)
        else:
            im.thumbnail((w, h), Image.LANCZOS)
            bg = Image.new("RGBA", (w, h), (0, 0, 0, 0))
            bg.paste(im, ((w - im.width) // 2, (h - im.height) // 2), im)
            im = bg
        if gray:
            a = im.getchannel("A")
            im = ImageOps.grayscale(im).convert("RGBA")
            im.putalpha(a.point(lambda v: int(v * 0.35)))
        if fade:
            mask = Image.new("L", (w, 1))
            mask.putdata([int(215 * (1 - x / w) ** 1.15) + 40 for x in range(w)])
            ov = Image.new("RGBA", (w, h), (9, 6, 16, 0))
            ov.putalpha(mask.resize((w, h)))
            im = Image.alpha_composite(im, ov)
        if radius:
            m = Image.new("L", (w, h), 0)
            ImageDraw.Draw(m).rounded_rectangle((0, 0, w - 1, h - 1), radius, fill=255)
            im.putalpha(ImageChops.multiply(im.getchannel("A"), m))
        return ImageTk.PhotoImage(im)

    def file(self, url):
        p = self.path(url) if url else None
        return p if p and p.exists() else None


# ================================================================ dialogs
# ================================================================ in-app sheets
KEY_SEQ = re.compile(r"^<(Key|Return|Escape|Up|Down|Left|Right|Tab|Delete|BackSpace|Control-"
                     r"|Prior|Next|Home|End)")


def ease_out(t):
    t = max(0.0, min(1.0, t))
    return 1 - (1 - t) ** 3


def ease_out_quint(t):
    t = max(0.0, min(1.0, t))
    return 1 - (1 - t) ** 5


def ease_in_out(t):
    t = max(0.0, min(1.0, t))
    return 4 * t * t * t if t < 0.5 else 1 - (-2 * t + 2) ** 3 / 2


def ease_out_back(t, s=1.15):
    """Ease out with a small, quick overshoot (about 3%) - feels physical, not bouncy."""
    t = max(0.0, min(1.0, t)) - 1
    return 1 + t * t * ((s + 1) * t + s)


EASES = {"out": ease_out, "quint": ease_out_quint, "inout": ease_in_out, "back": ease_out_back}


def _vgrad(w, h, top, bottom, stop=1.0):
    """Vertical gradient image from `top` to `bottom` (reaching it at `stop` of the height)."""
    a, b = _rgb(top), _rgb(bottom)
    col = Image.new("RGBA", (1, 256))
    col.putdata([tuple(int(x + (y - x) * min(1.0, (i / 255) / max(0.01, stop)))
                       for x, y in zip(a, b)) + (255,) for i in range(256)])
    return col.resize((w, h), Image.BILINEAR)


def _vgrad_l(w, h, top, bottom, stop=1.0):
    col = Image.new("L", (1, 256))
    col.putdata([int(top + (bottom - top) * min(1.0, (i / 255) / max(0.01, stop)))
                 for i in range(256)])
    return col.resize((w, h), Image.BILINEAR)


class OrderedDictLRU(dict):
    """Tiny size-capped cache (oldest entries drop out first)."""

    def __init__(self, cap):
        super().__init__()
        self.cap = cap

    def __setitem__(self, k, v):
        if k in self:
            super().__delitem__(k)
        super().__setitem__(k, v)
        while len(self) > self.cap:
            super().__delitem__(next(iter(self)))


def grab_window(win):
    """Screenshot of the app window (Windows), used as the blurred backdrop behind sheets."""
    if not HAS_PIL:
        return None
    try:
        from PIL import ImageGrab
        x, y = win.winfo_rootx(), win.winfo_rooty()
        w, h = win.winfo_width(), win.winfo_height()
        if w < 50 or h < 50:
            return None
        try:
            im = ImageGrab.grab((x, y, x + w, y + h), all_screens=True)
        except TypeError:
            im = ImageGrab.grab((x, y, x + w, y + h))
        im = im.convert("RGB")
        if im.size != (w, h):
            im = im.resize((w, h))
        return im
    except Exception:
        return None


class RoundButton(tk.Canvas):
    """Smooth rounded button for the pop-ups: eased hover, a pressed state, and the click
    fires on release (drag off to cancel). Behaves like the old Label buttons
    (pack/grid/config(text=..., fg=...))."""
    H, R = 38, 12

    def __init__(self, app, parent, text, color, cmd):
        try:
            pbg = parent.cget("bg")
        except Exception:
            pbg = SURFACE
        super().__init__(parent, height=self.H, bg=pbg, highlightthickness=0, bd=0,
                         cursor="hand2", takefocus=1)
        self.app, self.cmd, self.color, self.label, self.fg = app, cmd, color, text, TEXT
        self.font = (app.UI, 10, "bold")
        self.f = 0.0          # hover
        self.p = 0.0          # press
        self.k = 0.0          # keyboard focus
        self._target = self._ptarget = self._ktarget = 0.0
        self._inside = False
        self._job = None
        self.bind("<ButtonPress-1>", self._down)
        self.bind("<ButtonRelease-1>", self._up)
        self.bind("<Enter>", lambda e: self._hover(True))
        self.bind("<Leave>", lambda e: self._hover(False))
        self.bind("<FocusIn>", lambda e: self._focus(True))
        self.bind("<FocusOut>", lambda e: self._focus(False))
        self.bind("<KeyPress-space>", lambda e: self._fire())
        self.render()

    def _hover(self, on):
        self._inside = on
        self._target = 1.0 if on else 0.0
        if not on:
            self._ptarget = 0.0
        self.animate()

    def _focus(self, on):
        self._ktarget = 1.0 if on else 0.0
        self.animate()

    def _down(self, e):
        self._ptarget = 1.0
        self.animate()

    def _up(self, e):
        was = self._ptarget
        self._ptarget = 0.0
        self.animate()
        inside = 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height()
        if was and inside:
            self._fire()

    def _fire(self):
        if self.cmd:
            self.app.play_ui("tap")
            self.cmd()

    def width_for(self):
        return int(self.app.measure(self.label or " ", 10, "bold") + 40)

    def _bright(self):
        """Accent-coloured buttons are 'primary': they get a sheen and a glow."""
        try:
            r, g, b = _rgb(self.color)
            return max(r, g, b) - min(r, g, b) > 60
        except Exception:
            return False

    def render(self):
        w = self.width_for()
        super().configure(width=w)
        self.delete("all")
        f, p, k = round(self.f * 8) / 8, round(self.p * 4) / 4, round(self.k * 4) / 4
        col = mix(self.color, "#ffffff", 0.12 * f)
        if p:
            col = mix(col, mix(self.color, "#000000", 0.3), 0.6 * p)
        ins = round(1.5 * p)
        bw, bh = w - 2 * ins, self.H - 2 * ins
        img = self.app.shape_img(bw, bh, self.R, col,
                                 mix(col, ACCENT_HI, k) if k else "",
                                 1.5 if k else 0, 1.0 - 0.5 * p) if HAS_PIL else None
        if img:
            self.create_image(ins, ins, image=img, anchor="nw")
            self._img = img
        else:
            self.create_rectangle(0, 0, w, self.H, fill=col, outline="")
        self.create_text(w / 2, self.H / 2 + 0.5 * p, text=self.label, fill=self.fg,
                         font=self.font)

    def animate(self, target=None):
        if target is not None:
            self._target = target
        if self._job is None:
            self._step()

    def _step(self):
        self._job = None
        try:
            if not self.winfo_exists():
                return
        except tk.TclError:
            return
        if not self.app.settings.get("animations", True):
            self.f, self.p, self.k = self._target, self._ptarget, self._ktarget
            self.render()
            return
        moving = False
        for attr, tgt, rate in (("f", self._target, 0.32), ("p", self._ptarget, 0.55),
                                ("k", self._ktarget, 0.35)):
            cur = getattr(self, attr)
            d = tgt - cur
            if abs(d) < 0.04:
                setattr(self, attr, tgt)
            else:
                setattr(self, attr, cur + d * rate)
                moving = True
        self.render()
        if moving:
            self._job = self.after(16, self._step)

    def config(self, **kw):
        changed = False
        if "text" in kw:
            self.label = kw.pop("text")
            changed = True
        if "fg" in kw:
            self.fg = kw.pop("fg")
            changed = True
        if "bg" in kw:
            self.color = kw.pop("bg")
            changed = True
        if "font" in kw:
            self.font = kw.pop("font")
            changed = True
        for k in ("padx", "pady", "relief", "bd"):
            kw.pop(k, None)
        if kw:
            super().configure(**kw)
        if changed:
            self.render()

    configure = config


class RoundField(tk.Canvas):
    """Rounded text field container; the Entry inside is what callers get back. The border
    eases to the accent colour on focus."""

    def __init__(self, app, parent, var, show=""):
        try:
            pbg = parent.cget("bg")
        except Exception:
            pbg = SURFACE
        super().__init__(parent, height=42, bg=pbg, highlightthickness=0, bd=0)
        self.app = app
        self.focused = False
        self.f = 0.0
        self._job = None
        self._hov = False
        self.entry = tk.Entry(self, textvariable=var, bg=CARD, fg=TEXT, insertbackground=TEXT,
                              relief="flat", bd=0, font=(app.UI, 11), highlightthickness=0,
                              show=show, selectbackground=ACCENT, insertwidth=2)
        self.win = self.create_window(14, 21, window=self.entry, anchor="w")
        self.bind("<Configure>", lambda e: self.render())
        self.entry.bind("<FocusIn>", lambda e: self.set_focus(True), add="+")
        self.entry.bind("<FocusOut>", lambda e: self.set_focus(False), add="+")
        self.bind("<Enter>", lambda e: self._hover(True))
        self.bind("<Leave>", lambda e: self._hover(False))
        self.bind("<Button-1>", lambda e: self.entry.focus_set())

    def _hover(self, on):
        self._hov = on
        self.render()

    def set_focus(self, on):
        self.focused = on
        if self._job is None:
            self._step()

    def _step(self):
        self._job = None
        try:
            if not self.winfo_exists():
                return
        except tk.TclError:
            return
        tgt = 1.0 if self.focused else 0.0
        if not self.app.settings.get("animations", True) or abs(tgt - self.f) < 0.05:
            self.f = tgt
            self.render()
            return
        self.f += (tgt - self.f) * 0.3
        self.render()
        self._job = self.after(16, self._step)

    def render(self):
        w = max(40, self.winfo_width())
        self.delete("bg")
        f = round(self.f * 6) / 6
        fill = mix(CARD, mix(CARD, "#ffffff", 0.03), f)
        rest = mix(LINE, mix(LINE, "#ffffff", 0.08), 1.0 if self._hov else 0.0)
        if HAS_PIL:
            img = self.app.shape_img(w, 42, 12, fill, mix(rest, ACCENT, f), 1 + 0.6 * f, 0)
            self._img = img
            self.create_image(0, 0, image=img, anchor="nw", tags="bg")
        else:
            self.create_rectangle(0, 0, w, 42, fill=CARD, outline=LINE, tags="bg")
        try:
            self.entry.configure(bg=fill)
        except tk.TclError:
            pass
        self.tag_lower("bg")
        self.itemconfigure(self.win, width=max(20, w - 28))


class Sheet(tk.Frame):
    """A pop-up that lives inside the main window: it slides up over a blurred, dimmed copy
    of the app instead of opening a separate window. Behaves enough like a Toplevel
    (title/transient/wait_window/...) that the dialogs below just inherit from it."""
    PAD, SH, RAD = 7, 26, 18

    def __init__(self, app, where="center", dismiss=True):
        super().__init__(app, bg=SURFACE)
        self.app = app
        self._where, self._dismiss = where, dismiss
        self._keys = {}
        self._vis, self._from, self._to, self._t0, self._dur = 0.0, 0.0, 0.0, 0.0, 0.2
        self._closing = self._shown = False
        self._card = self._card_item = self._card_size = None
        self._pos = (0, 0)
        self._title = ""
        app.sheet_push(self)
        super().bind("<Configure>", lambda e: self.app.after_idle(self._resized), add="+")

    # -- Toplevel look-alike API
    def title(self, text=None):
        if text is not None:
            self._title = text
        return self._title

    def resizable(self, *a):
        pass

    def transient(self, *a):
        pass

    def protocol(self, *a):
        pass

    def overrideredirect(self, *a):
        pass

    def attributes(self, *a):
        pass

    def geometry(self, spec=None):
        return ""

    def grab_set(self):
        pass

    def focus_force(self):
        self.focus_set()

    def bind(self, seq=None, func=None, add=None):
        if seq and func and KEY_SEQ.match(seq):
            self._keys[seq] = func
            self.app.route_key(seq)
            return seq
        return super().bind(seq, func, add)

    # -- life cycle
    def present(self):
        self.app.update_idletasks()
        self._shown = True
        self._layout()
        self._anim(1.0, 0.34)
        for wdg in self._walk(self):
            if isinstance(wdg, tk.Entry):
                wdg.focus_set()
                break
        else:
            self.focus_set()

    def _walk(self, w):
        for c in w.winfo_children():
            yield c
            yield from self._walk(c)

    def destroy(self):
        if self._closing:
            return
        self._closing = True
        self.app.sheet_pop(self)
        if not self._shown or getattr(self.app, "_quitting", False) or not \
                self.app.settings.get("animations", True):
            self._final()
            return
        self._anim(0.0, 0.17)

    def _final(self):
        if getattr(self, "_done", False):
            return
        self._done = True
        try:
            if self._card_item and self.app._bd:
                self.app._bd.delete(self._card_item)
        except Exception:
            pass
        self._card_item = None
        tk.Frame.destroy(self)

    def _anim(self, to, dur):
        if not self.app.settings.get("animations", True):
            self._vis = to
            self._apply()
            if to == 0 and self._closing:
                self._final()
            return
        self._from, self._to, self._t0, self._dur = self._vis, to, time.time(), dur
        self.app.sheet_anim()

    def step(self, now):
        """Advance the slide; returns True while still moving."""
        if self._to == self._vis:
            if self._closing and self._vis == 0 and self._card_item is not False:
                self._final()
            return False
        raw = (now - self._t0) / self._dur
        k = ease_out_back(raw, 0.7) if self._to > self._from else ease_in_out(raw)
        self._vis = self._from + (self._to - self._from) * k
        if raw >= 1:
            self._vis = self._to
        self._apply()
        if self._vis == 0 and self._closing:
            self._final()
            return False
        return self._vis != self._to

    def hide(self):
        self.place_forget()
        if self._card_item and self.app._bd:
            self.app._bd.itemconfigure(self._card_item, state="hidden")

    def unhide(self):
        if self._card_item and self.app._bd:
            self.app._bd.itemconfigure(self._card_item, state="normal")
        self._apply()

    # -- geometry
    def _layout(self):
        if not self._shown:
            return
        w, h = self.winfo_reqwidth(), self.winfo_reqheight()
        W, H = self.app.winfo_width(), self.app.winfo_height()
        x = max(10, (W - w) // 2)
        if self._where == "top":
            y = 70
        else:
            y = max(14, min((H - h) // 2 - 10, int(H * 0.42 - h / 2)))
        self._pos = (x, y)
        if (w, h) != self._card_size:
            self._card_size = (w, h)
            self._card = self.app.sheet_card(w, h)
            if self.app._bd:
                if self._card_item:
                    self.app._bd.delete(self._card_item)
                self._card_item = self.app._bd.create_image(0, 0, anchor="nw",
                                                            image=self._card) if self._card \
                    else None
        self._apply()

    def _resized(self):
        try:
            if self._shown and not self._closing and self.winfo_exists():
                if (self.winfo_reqwidth(), self.winfo_reqheight()) != self._card_size:
                    self._layout()
        except tk.TclError:
            pass

    def _apply(self):
        if not self._shown:
            return
        x, y = self._pos
        off = round((1 - self._vis) * (34 if not self._closing else 22))
        try:
            if self.app.sheets and self.app.sheets[-1] is not self and not self._closing:
                return  # covered by another sheet
            self.place(x=x, y=y + off)
            self.lift()
            if self._card_item and self.app._bd:
                self.app._bd.coords(self._card_item, x - self.PAD - self.SH,
                                    y + off - self.PAD - self.SH)
        except tk.TclError:
            pass

    def contains(self, ex, ey):
        x, y = self._pos
        w, h = self._card_size or (0, 0)
        return x - self.PAD <= ex <= x + w + self.PAD and y - self.PAD <= ey <= y + h + self.PAD


class Layer:
    """A dialog drawn on the main canvas, above the page and below toasts/menus.

    Why not a Tk window or frame: those are separate native widgets, so every open/close
    needed a screenshot of the app, a blur and several full-window blends, and Tk painted
    them in idle time - under load they showed up half drawn. A Layer is just canvas items:
    it redraws on its own (the page underneath is frozen and never re-rendered while it's
    open), it can't end up half painted, and closing it can't leave widgets behind.

    Subclasses implement draw(x0, y0, x1, y1). Use self.k("name") for hit keys so clicks
    are routed to the top layer only."""
    W, H = 560, 420
    dismiss = True          # click outside / Esc closes it
    _ids = itertools.count(1)

    def __init__(self, app):
        self.app = app
        self.kp = f"L{next(Layer._ids)}:"
        self.t0 = time.time()
        self.tc = None              # closing since
        self.closed = False
        self.box = (0, 0, 0, 0)
        self.scroll = self.scroll_t = 0.0
        self.max_scroll = 0.0
        self.entries = {}           # name -> (tk.Entry, canvas window id)
        app.push_layer(self)

    def k(self, name):
        return self.kp + name

    def size(self, w, h):
        return min(self.W, w - 48), min(self.H, h - 48)

    def draw(self, x0, y0, x1, y1):
        pass

    def on_key(self, seq, e):
        if seq == "<Escape>" and self.dismiss:
            self.close()
            return True
        return False

    def on_wheel(self, delta):
        if self.max_scroll > 0:
            self.scroll_t = max(0.0, min(self.max_scroll, self.scroll_t - delta / 120 * 80))
            self.app.layer_redraw()

    def close(self):
        if self.tc is None:
            self.tc = time.time()
            self.on_closing()
            self.app.layer_closing(self)

    def on_closing(self):
        """Stop timers, audio, video... (runs once, as soon as close starts)."""

    def cleanup(self):
        for ent, wid in self.entries.values():
            try:
                self.app.cv.delete(wid)
                ent.destroy()
            except tk.TclError:
                pass
        self.entries = {}

    # -- helpers for subclasses
    def glide_scroll(self):
        """Ease the body scroll towards its target; True while it's still moving."""
        d = self.scroll_t - self.scroll
        if abs(d) < 0.5 or not self.app.settings.get("animations", True):
            self.scroll = self.scroll_t
            return False
        self.scroll += d * 0.32
        self.app._more = True
        return True

    def entry(self, name, var, x, y, w, h=36, show="", on_return=None, hint=""):
        """A rounded text field with a real Entry inside (kept alive between frames).
        Empty and unfocused, it shows its hint instead; clicking the field focuses it."""
        app = self.app
        cv = app.cv
        got = self.entries.get(name)
        if got is None:
            ent = tk.Entry(cv, textvariable=var, bg=CARD, fg=TEXT, insertbackground=TEXT,
                           relief="flat", bd=0, font=(app.UI, 11), highlightthickness=0,
                           show=show, selectbackground=ACCENT, insertwidth=2)
            if on_return:
                ent.bind("<Return>", lambda e: (on_return(), "break")[1])
            ent.bind("<FocusIn>", lambda e: app.layer_redraw(), add="+")
            ent.bind("<FocusOut>", lambda e: app.layer_redraw(), add="+")
            got = (ent, None)
            self.entries[name] = got
        ent, wid = got
        try:
            focused = app.focus_get() is ent
        except Exception:
            focused = False
        f = app.tween(self.kp + "foc:" + name, 1.0 if focused else 0.0, 0.18)
        key = self.k("field:" + name)
        tags = app.hit(key, click=lambda: self.focus(name), box=(x, y, x + w, y + h))
        app.rrect(x, y, x + w, y + h, 11, fill=CARD, depth=0, tags=tags,
                  outline=mix(mix(LINE, "#ffffff", 0.06 + 0.06 * app.hv(key)), ACCENT, f),
                  width=1 + 0.5 * f)
        geom = (x + 13, y + h / 2, w - 26, h - 12)
        self._geom = getattr(self, "_geom", {})
        self._geom[name] = geom
        show_ent = focused or bool(var.get()) or getattr(self, "_want_focus", None) == name
        if show_ent:
            self._place(name)
        else:
            if wid:
                try:
                    cv.itemconfigure(wid, state="hidden")
                except tk.TclError:
                    pass
            if hint:
                app.text(x + 14, y + h / 2, hint, 10, fill=DIM, tags=tags)
        if getattr(self, "_want_focus", None) == name:
            app.after_idle(lambda: self.focus(name))
        return ent

    def _place(self, name):
        cv = self.app.cv
        ent, wid = self.entries[name]
        ex, ey, ew, eh = self._geom.get(name, (0, 0, 10, 10))
        try:
            if wid is None or not cv.type(wid):
                wid = cv.create_window(ex, ey, window=ent, anchor="w", width=ew, height=eh,
                                       tags=("lyrwin",))
                self.entries[name] = (ent, wid)
            else:
                cv.coords(wid, ex, ey)
                cv.itemconfigure(wid, width=ew, height=eh, state="normal")
        except tk.TclError:
            pass

    def hide_entries(self):
        for ent, wid in self.entries.values():
            try:
                if wid:
                    self.app.cv.itemconfigure(wid, state="hidden")
            except tk.TclError:
                pass

    def focus(self, name):
        got = self.entries.get(name)
        if not got:
            self._want_focus = name         # not drawn yet: focus on first draw
            return
        self._want_focus = None
        if name in getattr(self, "_geom", {}):
            self._place(name)
        try:
            got[0].focus_set()
            got[0].icursor("end")
        except tk.TclError:
            pass
        self.app.layer_redraw()

    def close_btn(self, x, y):
        app = self.app
        key = self.k("close")
        f = app.hv(key)
        tags = app.hit(key, click=self.close, tip="Close  (Esc)")
        app.circle(x, y, 15 - app.pressed(key), fill=mix(mix(SURFACE, CARD, 0.5), CARD_HI, f),
                   tags=tags, depth=0.6)
        app.icon(x, y, "close", 9, app.hcol(key, MUTED, TEXT), tags=tags)

    def button(self, x, y, label, fn, name, icon=None, primary=True, anchor="w", h=36,
               disabled=False, danger=False, tip=None):
        app = self.app
        key = self.k(name)
        w = app.measure(label, 10, "bold") + (50 if icon else 34)
        if anchor == "e":
            x -= w
        elif anchor == "center":
            x -= w / 2
        tags = app.hit(key, click=None if disabled else fn, tip=tip)
        f = 0 if disabled else app.hv(key)
        pr = 0 if disabled else app.pressed(key)
        if disabled:
            fill = mix(CARD, SURFACE, 0.4)
        elif primary:
            base, hot = (DANGER, mix(DANGER, "#ffffff", 0.14)) if danger else (ACCENT, ACCENT_HI)
            fill = app.hcol(key, base, hot)
            if f > 0 and not pr:
                app.soft(x, y, x + w, y + h, h / 2, base, alpha=int(100 * f), spread=10, dy=3,
                         tags=tags)
        else:
            fill = app.hcol(key, CARD, CARD_HI)
        ins = 1.5 * pr
        app.rrect(x + ins, y + ins, x + w - ins, y + h - ins, h / 2, fill=fill, tags=tags,
                  depth=0 if disabled else 1.0 - 0.5 * pr,
                  outline="" if primary or disabled else mix(LINE, CARD_HI, f))
        fg = DIM if disabled else (TEXT if primary else app.hcol(key, SOFT, TEXT))
        tx = x + 17
        if icon:
            app.icon(tx + 6, y + h / 2 + 0.5 * pr, icon, 10, fg, tags=tags)
            tx += 21
        app.text(tx, y + h / 2 + 0.5 * pr, label, 10, "bold", fg, tags=tags)
        return w

    def tabs(self, x, y, options, current, pick, name):
        """Underlined tabs: the accent bar glides to the selected tab."""
        app = self.app
        pos = []
        cx = x
        for val, lab in options:
            tw = app.measure(lab, 10, "bold")
            pos.append((val, lab, cx, tw))
            cx += tw + 30
        for val, lab, px, tw in pos:
            key = self.k(f"{name}:{val}")
            on = val == current
            tags = app.hit(key, click=(lambda v=val: pick(v)) if not on else None,
                           box=(px - 8, y - 14, px + tw + 8, y + 18))
            app.text(px, y, lab, 10, "bold", TEXT if on else app.hcol(key, MUTED, TEXT),
                     tags=tags)
        sel = next(((px, tw) for v, _, px, tw in pos if v == current), None)
        if sel:
            sx = app.tween(self.kp + name + ":x", sel[0], 0.3, "back")
            sw = app.tween(self.kp + name + ":w", sel[1], 0.3, "back")
            app.rrect(sx, y + 14, sx + sw, y + 17, 1.5, fill=ACCENT_HI, depth=0)
        return cx


class ScrollBody:
    """Mixin: a scrolling body inside a Layer. Content is drawn shifted by the scroll, then
    the panel's own colour is laid over everything outside the viewport (canvas items can't
    be clipped), and the header/footer are drawn on top of that."""

    def mask(self, x0, y0, x1, y1, top, bottom):
        app = self.app
        app.rrect(x0 + 1, y0 + 1, x1 - 1, top, 19, fill=SURFACE, depth=0)
        if top - 22 > y0 + 20:
            app.cv.create_rectangle(x0 + 1, top - 22, x1 - 1, top, fill=SURFACE, outline="")
        app.rrect(x0 + 1, bottom, x1 - 1, y1 - 1, 19, fill=SURFACE, depth=0)
        if bottom + 22 < y1 - 20:
            app.cv.create_rectangle(x0 + 1, bottom, x1 - 1, bottom + 22, fill=SURFACE,
                                    outline="")
        if self.max_scroll > 0:             # slim scroll indicator
            track = bottom - top - 16
            th = max(30, track * (bottom - top) / (bottom - top + self.max_scroll))
            ty = top + 8 + (track - th) * (self.scroll / max(1, self.max_scroll))
            app.rrect(x1 - 9, ty, x1 - 5, ty + th, 2, fill=mix(SURFACE, SOFT, 0.3), depth=0)

    def vis(self, ya, yb, top, bottom):
        """Draw a block of scrolled content? Only if it shows in the viewport *and* sits
        wholly inside the panel - canvas items can't be clipped, so anything poking past the
        panel's edge would be visible over the dimmed page."""
        _, py0, _, py1 = self.box
        return yb > top and ya < bottom and ya >= py0 + 2 and yb <= py1 - 2

    def row_box(self, key, x0, y0, x1, y1, top, bottom, click, tip=None):
        """Register a click area only for the part of a row that's actually visible."""
        vy0, vy1 = max(y0, top), min(y1, bottom)
        if vy1 - vy0 < 6:
            return ()
        return self.app.hit(key, click=click, tip=tip, box=(x0, vy0, x1, vy1))


def _stat_label(app, x, y, label, value, col=None, size=13):
    app.text(x, y, label, 8, "bold", DIM)
    app.text(x, y + 20, value, size, "bold", col or TEXT)


class FriendLayer(Layer, ScrollBody):
    """A friend's player profile (rank, acts, RR movement, recent competitive games) plus
    messaging, in one place. Everything shown comes from Riot; when Riot doesn't give
    something, the panel says so instead of guessing."""
    W, H = 820, 700
    CACHE_S = 300

    def __init__(self, app, friend, tab="profile"):
        self.f = friend
        self.puuid = friend.get("puuid")
        self.tab = "chat" if tab == "chat" and friend.get("pid") else (
            tab if tab in ("profile", "matches") else "profile")
        cache = app.__dict__.setdefault("friend_profiles", {})
        got = cache.get(self.puuid)
        self.data = got if got and time.time() - got.get("t", 0) < self.CACHE_S else None
        self.loading = False
        self.var = tk.StringVar(app)
        self.chat = {"msgs": None, "err": None, "me": None, "sending": False}
        self.chat_scroll = 0.0
        self._chat_gen = 0
        super().__init__(app)
        if self.data is None:
            self.load()
        if self.tab == "chat":
            self.start_chat()

    # ---- data
    def load(self, force=False):
        if self.loading or not self.puuid:
            return
        self.loading = True
        if force:
            self.data = None
        app = self.app

        def work():
            try:
                vc, _ = app.get_vc()
                d = fetch_player_profile(vc, self.puuid, stop=lambda: self.tc is not None)
            except Exception as e:
                d = {"t": time.time(), "fatal": describe_err(e), "errors": {}, "matches": []}

            def done():
                self.loading = False
                if not d.get("fatal"):
                    app.friend_profiles[self.puuid] = d
                if not self.closed:
                    self.data = d
                    app.layer_redraw()
            app.call_ui(done)
        threading.Thread(target=work, daemon=True).start()
        app.layer_redraw()

    def set_tab(self, t):
        if t == self.tab:
            return
        self.tab = t
        self.scroll = self.scroll_t = 0
        if t == "chat":
            self.start_chat()
            self.focus("msg")
        else:
            self._chat_gen += 1          # stops the chat poll loop
            self.app.cv.focus_set()
        self.app.layer_redraw()

    def on_closing(self):
        self._chat_gen += 1

    # ---- chat
    def start_chat(self):
        self._chat_gen += 1
        gen = self._chat_gen
        app = self.app

        def poll():
            if gen != self._chat_gen or self.tc is not None or self.closed:
                return

            def work():
                lf = read_lockfile()
                try:
                    if not lf:
                        raise ClientDown("")
                    if not self.chat["me"]:
                        self.chat["me"] = local_tokens(lf)[2]
                    msgs = chat_history(lf, self.f["pid"])
                    err = None
                except Exception as e:
                    msgs, err = None, describe_err(e)

                def done():
                    if gen != self._chat_gen:
                        return
                    if msgs is not None:
                        sig = [(m.get("id"), m.get("body")) for m in msgs[-40:]]
                        changed = sig != self.chat.get("sig")
                        self.chat.update(msgs=msgs[-40:], err=None, sig=sig)
                    else:
                        changed = self.chat.get("err") != err
                        self.chat["err"] = err
                    if changed:
                        app.layer_redraw()
                app.call_ui(done)
            threading.Thread(target=work, daemon=True).start()
            app.after(2500, poll)
        poll()

    def send(self):
        text = self.var.get().strip()
        if not text or self.chat["sending"]:
            return
        self.var.set("")
        self.chat["sending"] = True
        self.chat["pending"] = text
        app = self.app
        self.chat_scroll = 0
        app.layer_redraw()

        def work():
            try:
                lf = read_lockfile()
                if not lf:
                    raise ClientDown("")
                chat_send(lf, self.f["pid"], text)
                msgs = chat_history(lf, self.f["pid"])
                err = None
            except Exception as e:
                msgs, err = None, describe_err(e)

            def done():
                self.chat["sending"] = False
                self.chat["pending"] = None
                if msgs is not None:
                    self.chat.update(msgs=msgs[-40:], err=None,
                                     sig=[(m.get("id"), m.get("body")) for m in msgs[-40:]])
                else:
                    if not self.var.get():
                        self.var.set(text)
                    app.toast(f"Didn't send: {err}", "bad", tray=False)
                app.layer_redraw()
            app.call_ui(done)
        threading.Thread(target=work, daemon=True).start()

    # ---- input
    def on_wheel(self, delta):
        if self.tab == "chat":
            self.chat_scroll = max(0.0, self.chat_scroll + delta / 120 * 60)
            self.app.layer_redraw()
        else:
            super().on_wheel(delta)

    # ---- drawing
    def status_line(self):
        f, pr = self.f, self.f.get("pres") or {}
        if not f.get("online"):
            return "Offline", DIM
        prod = f.get("product")
        if prod and prod != "valorant":
            return {"league_of_legends": "Playing League of Legends",
                    "bacon": "Playing Legends of Runeterra",
                    "keystone": "Online in the Riot Client"}.get(prod, "Online"), GOLD
        loop = pr.get("loop")
        bits = []
        if loop == "INGAME":
            bits.append("In a match")
        elif loop == "PREGAME":
            bits.append("In agent select")
        elif loop == "MENUS":
            bits.append("In menus")
        else:
            bits.append("Online")
        q = pr.get("queue")
        if q and loop in ("INGAME", "PREGAME"):
            bits.append(QUEUES.get(q, str(q).title()))
        mp = ASSETS.maps.get(pr.get("map") or "", {}).get("name")
        if mp and loop == "INGAME":
            bits.append(mp)
        if loop == "INGAME" and pr.get("ally") is not None and pr.get("enemy") is not None:
            bits.append(f"{pr['ally']}–{pr['enemy']}")
        elif loop == "MENUS" and (pr.get("party_size") or 0) > 1:
            bits.append(f"party of {pr['party_size']}")
        col = GOOD if f.get("state") in ("chat", "dnd") or loop else GOLD
        return "  ·  ".join(bits), col

    def draw(self, x0, y0, x1, y1):
        app = self.app
        f = self.f
        pres = f.get("pres") or {}
        d = self.data or {}
        name, _, tag = (f.get("name") or "?").partition("#")
        if app.streamer():
            name, tag = "Hidden", "•••"
        body_top = y0 + 226
        body_bot = y1 - (14 if self.tab == "chat" else 72)
        bx0, bx1 = x0 + 26, x1 - 26
        # body first (it scrolls), then masks, then the fixed header/footer on top
        if self.tab == "chat":
            self.draw_chat(bx0, body_top + 6, bx1, body_bot, name)
        else:
            self.hide_entries()
            self.glide_scroll()
            if self.tab == "matches":
                self.draw_matches(bx0, body_top, bx1, body_bot)
            else:
                self.draw_profile(bx0, body_top, bx1, body_bot)
        self.mask(x0, y0, x1, y1, body_top, body_bot)
        if self.tab != "chat":
            app.cv.create_line(x0 + 20, body_bot + 2, x1 - 20, body_bot + 2, fill=LINE)
            note = ("From Riot's game services, read with your signed-in client. Other players "
                    "in each match stay anonymous, like the in-game scoreboard.")
            for i, ln in enumerate(app.wrap(note, 8, bx1 - bx0, max_lines=2)):
                app.text(bx0, body_bot + 24 + 15 * i, ln, 8, fill=DIM)

        # header: banner, avatar, name, live status
        card = ASSETS.cards.get(pres.get("card") or d.get("card") or "", {})
        ban = (x0 + 8, y0 + 8, x1 - 8, y0 + 120)
        if not app.image(card.get("wide"), ban[0], ban[1], ban[2] - ban[0], ban[3] - ban[1],
                         mode="cover", radius=14, fade=True):
            app.rrect(*ban, 14, fill=mix(SURFACE, ACCENT, 0.16), depth=0)
            app.soft(ban[0] + 60, ban[1] + 10, ban[0] + 360, ban[3] - 10, 40, ACCENT, alpha=60,
                     spread=30, dy=0)
        self.close_btn(x1 - 34, y0 + 34)
        A = 82
        ax, ay = x0 + 30, y0 + 78
        app.rrect(ax - 5, ay - 5, ax + A + 5, ay + A + 5, 22, fill=SURFACE, depth=0)
        if not app.image(card.get("small"), ax, ay, A, A, mode="cover", radius=18):
            app.letter_avatar(ax, ay, A, name or "?", radius=18)
        stxt, scol = self.status_line()
        app.circle(ax + A - 4, ay + A - 4, 10, fill=SURFACE, depth=0)
        app.circle(ax + A - 4, ay + A - 4, 6.5, fill=scol if f.get("online") else DIM, depth=0)
        nx = ax + A + 20
        app.text(nx, y0 + 140, name, 18, "bold", maxw=x1 - nx - 200)
        nw = min(app.measure(name, 18, "bold"), x1 - nx - 200)
        app.text(nx + nw + 6, y0 + 143, f"#{tag}", 11, fill=MUTED)
        app.text(nx, y0 + 168, stxt, 10, "bold", scol if f.get("online") else DIM,
                 maxw=x1 - nx - 40)
        # badges on the right: level and the rank they're showing
        rx = x1 - 30
        lvl = pres.get("level") or d.get("level")
        tier = pres.get("tier")
        if tier is None and d.get("mmr"):
            tier = d["mmr"].get("tier")
        chips = []
        if lvl:
            chips.append(f"Level {lvl}")
        if pres.get("lb"):
            chips.append(f"Leaderboard #{pres['lb']}")
        for c in chips:
            rx -= app.pill(rx, y0 + 141, c, fill=CARD_HI, fg=SOFT, size=8, anchor="e") + 6
        if tier and tier >= 3:
            app.rank_icon(tier, rx - 16, y0 + 141, 26)
        # tabs
        ty = y0 + 204
        nm = len((d.get("matches") or []))
        opts = [("profile", "Overview"), ("matches", f"Matches  {nm}" if nm else "Matches")] + \
            ([("chat", "Messages")] if f.get("pid") else [])
        self.tabs(bx0, ty, opts, self.tab, self.set_tab, "tab")
        app.cv.create_line(x0 + 20, ty + 18, x1 - 20, ty + 18, fill=LINE)
        if self.tab != "chat":
            lab = "Refreshing…" if self.loading else "Refresh"
            when = ago(d.get("t"), "Updated") if d.get("t") and not self.loading else ""
            w_ = self.button(bx1, ty - 15, lab, lambda: self.load(force=True), "refresh",
                             "refresh", primary=False, anchor="e", h=30, disabled=self.loading)
            if when:
                app.text(bx1 - w_ - 12, ty, when, 8, fill=DIM, anchor="e")

    def loading_blocks(self, x0, x1, y, rows=False):
        app = self.app
        bw = x1 - x0
        if not rows:
            cw = (bw - 24) / 3
            for i in range(3):
                cx = x0 + i * (cw + 12)
                app.rrect(cx, y, cx + cw, y + 96, 16, fill=mix(SURFACE, CARD, 0.35), depth=0)
                app.skel(cx + 16, y + 16, cx + 80, y + 26, 5, i)
                app.skel(cx + 16, y + 42, cx + 60, y + 82, 10, i)
                app.skel(cx + 72, y + 50, cx + cw - 30, y + 64, 6, i)
            y += 112
        for i in range(3 if not rows else 5):
            app.rrect(x0, y, x1, y + 60, 14, fill=mix(SURFACE, CARD, 0.3), depth=0)
            app.skel(x0 + 16, y + 8, x0 + 106, y + 52, 8, i)
            app.skel(x0 + 120, y + 18, x0 + 300, y + 30, 6, i)
            app.skel(x1 - 160, y + 22, x1 - 20, y + 36, 6, i)
            y += 68

    def draw_profile(self, x0, top, x1, bot):
        app = self.app
        d = self.data
        y = top + 14 - self.scroll
        bw = x1 - x0
        V = lambda a, b: self.vis(a, b, top, bot)       # noqa: E731
        if d is None:
            self.loading_blocks(x0, x1, y)
            self.max_scroll = 0
            return
        if d.get("fatal"):
            self.empty(x0, x1, top + 10, "warning", "Couldn't load this profile", d["fatal"],
                       ("Try again", lambda: self.load(force=True), "retry"))
            self.max_scroll = 0
            return
        mmr = d.get("mmr")
        err = d.get("errors") or {}
        cw = (bw - 24) / 3
        if mmr:
            if V(y, y + 96):
                tier, rr = mmr.get("tier") or 0, mmr.get("rr") or 0
                cards = [("Current rank", tier,
                          f"{rr} RR" if tier >= 3 else "Not ranked this act"),
                         ("Peak rank", mmr.get("peak_tier") or 0,
                          f"Reached in {mmr['peak_act']}" if mmr.get("peak_act")
                          else "Highest tier with a win")]
                for i, (lab, t, sub) in enumerate(cards):
                    cx = x0 + i * (cw + 12)
                    app.rrect(cx, y, cx + cw, y + 96, 16, fill=mix(SURFACE, CARD, 0.35),
                              outline=LINE)
                    app.text(cx + 16, y + 20, lab, 8, "bold", DIM)
                    if not app.rank_icon(t, cx + 42, y + 60, 46, large=True):
                        app.circle(cx + 42, y + 60, 18, fill=CARD, depth=0)
                    col = ASSETS.tier_color(t) or MUTED
                    app.text(cx + 76, y + 53, ASSETS.tier_name(t), 13, "bold",
                             mix(col, "#ffffff", 0.4) if t >= 3 else MUTED, maxw=cw - 90)
                    app.text(cx + 76, y + 74, sub, 9, fill=MUTED, maxw=cw - 90)
                cx = x0 + 2 * (cw + 12)
                app.rrect(cx, y, cx + cw, y + 96, 16, fill=mix(SURFACE, CARD, 0.35),
                          outline=LINE)
                app.text(cx + 16, y + 20, ASSETS.current_act_label or "This act", 8, "bold",
                         DIM, maxw=cw - 30)
                g, wins = mmr.get("games"), mmr.get("wins")
                if g:
                    losses = max(0, g - (wins or 0))
                    app.text(cx + 16, y + 53, f"{wins or 0}W  {losses}L", 15, "bold")
                    app.text(cx + 16, y + 76, f"{round(100 * (wins or 0) / g)}% win rate  ·  "
                                              f"{g} games", 9, fill=MUTED)
                else:
                    app.text(cx + 16, y + 53, "No ranked games", 12, "bold", MUTED)
                    app.text(cx + 16, y + 76, "this act yet", 9, fill=DIM)
            y += 112
            acts = [a for a in (mmr.get("acts") or []) if a["id"] != ASSETS.current_act][-6:]
            if acts:
                if V(y, y + 80):
                    app.text(x0 + 2, y + 6, "Previous acts", 9, "bold", DIM)
                    aw = min(150, (bw - 10 * (len(acts) - 1)) / len(acts))
                    for i, a in enumerate(reversed(acts)):
                        ax = x0 + i * (aw + 10)
                        ay = y + 22
                        app.rrect(ax, ay, ax + aw, ay + 58, 12, fill=mix(SURFACE, CARD, 0.3),
                                  outline=LINE)
                        app.rank_icon(a["tier"], ax + 24, ay + 29, 30)
                        app.text(ax + 46, ay + 20, ASSETS.act_label.get(a["id"], "") or "Act",
                                 8, "bold", DIM, maxw=aw - 52)
                        col = ASSETS.tier_color(a["tier"]) or MUTED
                        app.text(ax + 46, ay + 38, ASSETS.tier_name(a["tier"]), 9, "bold",
                                 mix(col, "#ffffff", 0.4), maxw=aw - 52)
                y += 96
        else:
            reason = err.get("rank") or "Riot didn't return a rank for this player."
            hint = ("RiotHub can only read stats for players on your own region "
                    "(EU, NA, AP, KR...)." if err.get("rank_code") in (400, 403, 404) else "")
            if V(y, y + 78):
                self.unavailable(x0, x1, y, "Rank isn't available", reason, hint)
            y += 92
        ups = [u for u in d.get("updates") or [] if u.get("tier", 0) >= 3]
        if len(ups) >= 2:
            gh = 110
            if V(y, y + gh + 46):
                app.rrect(x0, y, x1, y + gh + 46, 16, fill=mix(SURFACE, CARD, 0.3),
                          outline=LINE)
                app.text(x0 + 16, y + 20, f"RR over the last {len(ups)} ranked games", 8,
                         "bold", DIM)
                last = ups[-1]
                app.text(x1 - 16, y + 20, f"{ASSETS.tier_name(last['tier'])}  ·  "
                                          f"{last['rr']} RR", 9, "bold", SOFT, anchor="e")
                vals = [u["tier"] * 100 + u["rr"] for u in ups]
                lo, hi = min(vals), max(vals)
                if hi - lo < 60:
                    hi, lo = hi + 30, lo - 30
                gx, gy, gw = int(x0 + 20), int(y + 36), int(bw - 40)
                coords = []
                for i, v in enumerate(vals):
                    coords += [gx + gw * i / (len(vals) - 1), gy + gh - (v - lo) / (hi - lo) * gh]
                app.graph_image(coords, gx, gy, gw, gh)
                for i, u in enumerate(ups):
                    col = GOOD if u["delta"] > 0 else (DANGER if u["delta"] < 0 else MUTED)
                    app.circle(coords[2 * i], coords[2 * i + 1], 3.5, fill=col, depth=0)
            y += gh + 62
        elif err.get("history") and mmr:
            if V(y, y + 78):
                self.unavailable(x0, x1, y, "RR history isn't available", err["history"])
            y += 92
        ms = d.get("matches") or []
        if ms and V(y, y + 60):
            w_ = sum(1 for m in ms if m.get("won") is True)
            l_ = sum(1 for m in ms if m.get("won") is False)
            k_ = sum(m["k"] for m in ms)
            dd = max(1, sum(m["d"] for m in ms))
            app.rrect(x0, y, x1, y + 60, 14, fill=mix(SURFACE, CARD, 0.3), outline=LINE)
            app.text(x0 + 16, y + 20, f"Last {len(ms)} competitive matches", 8, "bold", DIM)
            bx = x0 + 16
            for lab, val, col in (("Record", f"{w_}W {l_}L", TEXT),
                                  ("K/D", f"{k_ / dd:.2f}", TEXT),
                                  ("Avg ACS", str(round(sum(m['acs'] for m in ms) / len(ms))),
                                   TEXT)):
                app.text(bx, y + 42, val, 12, "bold", col)
                app.text(bx + app.measure(val, 12, "bold") + 6, y + 43, lab, 8, fill=DIM)
                bx += 150
            key = self.k("seeall")
            self.row_box(key, x1 - 150, y + 14, x1 - 10, y + 46, top, bot,
                         lambda: self.set_tab("matches"))
            app.text(x1 - 16, y + 30, "See matches  ›", 9, "bold", app.hcol(key, SOFT, TEXT),
                     anchor="e")
        y += 76
        self.max_scroll = max(0.0, (y + self.scroll) - bot + 4)
        self.scroll_t = min(self.scroll_t, self.max_scroll)

    def draw_matches(self, x0, top, x1, bot):
        app = self.app
        d = self.data
        y = top + 14 - self.scroll
        if d is None:
            self.loading_blocks(x0, x1, y, rows=True)
            self.max_scroll = 0
            return
        if d.get("fatal"):
            self.empty(x0, x1, top + 10, "warning", "Couldn't load this profile", d["fatal"],
                       ("Try again", lambda: self.load(force=True), "retry"))
            self.max_scroll = 0
            return
        err = d.get("errors") or {}
        ms = d.get("matches") or []
        if not ms:
            if err.get("matches"):
                self.unavailable(x0, x1, y, "Couldn't load their matches", err["matches"])
            elif err.get("history"):
                hint = ("RiotHub can only read stats for players on your own region."
                        if "404" in err["history"] else "")
                self.unavailable(x0, x1, y, "Match history isn't available", err["history"],
                                 hint)
            else:
                self.unavailable(x0, x1, y, "No recent competitive games",
                                 "Riot only lists their latest ranked matches - unrated, "
                                 "Swiftplay and other modes don't show up here.")
            self.max_scroll = 0
            return
        for i, mt in enumerate(ms):
            if self.vis(y, y + 60, top, bot):
                self.match_row(x0, x1, y, i, mt, top, bot)
            y += 68
        if d.get("failed_matches") and self.vis(y, y + 20, top, bot):
            app.text(x0 + 2, y + 6, f"{d['failed_matches']} more match(es) couldn't be loaded "
                     "right now - try Refresh in a minute.", 8, fill=DIM)
        y += 24
        self.max_scroll = max(0.0, (y + self.scroll) - bot + 4)
        self.scroll_t = min(self.scroll_t, self.max_scroll)

    def match_row(self, x0, x1, y, i, mt, top, bot):
        app = self.app
        key = self.k(f"m:{i}")
        f = app.hv(key)
        if y > bot or y + 60 < top:
            return
        self.row_box(key, x0, y, x1, y + 60, top, bot, lambda mt=mt: self.open_match(mt),
                     tip="See the full scoreboard")
        won = mt.get("won")
        col = GOOD if won is True else (DANGER if won is False else MUTED)
        app.rrect(x0, y, x1, y + 60, 14, fill=mix(mix(SURFACE, CARD, 0.3), CARD_HI, 0.55 * f),
                  outline=mix(LINE, mix(LINE, col, 0.5), f))
        app.rrect(x0 + 1, y + 12, x0 + 4, y + 48, 1.5, fill=col, depth=0)
        mp = ASSETS.maps.get(mt.get("map") or "", {})
        if not app.image(mp.get("icon") or mp.get("splash"), x0 + 14, y + 8, 88, 44,
                         mode="cover", radius=8):
            app.rrect(x0 + 14, y + 8, x0 + 102, y + 52, 8, fill=CARD, depth=0)
        ag = ASSETS.agents.get(mt.get("agent") or "", {})
        if not app.image(ag.get("icon"), x0 + 112, y + 12, 36, 36, radius=9):
            app.rrect(x0 + 112, y + 12, x0 + 148, y + 48, 9, fill=CARD, depth=0)
        res = "Victory" if won is True else ("Defeat" if won is False else "Draw")
        app.text(x0 + 162, y + 22, res, 11, "bold", col)
        if mt.get("score"):
            app.text(x0 + 162 + app.measure(res, 11, "bold") + 10, y + 22,
                     mt["score"].replace("-", "–"), 11, "bold")
        app.text(x0 + 162, y + 41, "  ·  ".join(b for b in (mp.get("name"), ag.get("name"),
                                                             ago(mt.get("start"), "").strip())
                                               if b), 9, fill=MUTED, maxw=240)
        cx = x1 - 330
        _stat_label(app, cx, y + 16, "K / D / A", f"{mt['k']} / {mt['d']} / {mt['a']}", size=11)
        _stat_label(app, cx + 104, y + 16, "ACS", str(mt["acs"]), size=11)
        rr = mt.get("rr")
        if rr is not None:
            rc = GOOD if rr > 0 else (DANGER if rr < 0 else MUTED)
            _stat_label(app, cx + 166, y + 16, "RR", f"{rr:+d}", rc, size=11)
        if mt.get("tier_after"):
            app.rank_icon(mt["tier_after"], x1 - 64, y + 30, 26)
        app.icon(x1 - 22, y + 30, "chevron", 9, app.hcol(key, DIM, SOFT))

    def unavailable(self, x0, x1, y, title, reason, hint=""):
        app = self.app
        app.rrect(x0, y, x1, y + 78, 14, fill=mix(SURFACE, BG, 0.25), outline=LINE)
        app.circle(x0 + 34, y + 39, 16, fill=mix(SURFACE, GOLD, 0.14), depth=0)
        app.icon(x0 + 34, y + 39, "info", 10, GOLD)
        app.text(x0 + 62, y + 24, title, 10, "bold")
        app.text(x0 + 62, y + 44, reason, 9, fill=MUTED, maxw=x1 - x0 - 80)
        if hint:
            app.text(x0 + 62, y + 61, hint, 8, fill=DIM, maxw=x1 - x0 - 80)

    def empty(self, x0, x1, y, icon, title, sub, action=None):
        app = self.app
        cx = (x0 + x1) / 2
        app.soft(cx - 26, y + 34, cx + 26, y + 86, 26, GOLD, alpha=60, spread=12, dy=0)
        app.circle(cx, y + 60, 26, fill=mix(SURFACE, GOLD, 0.16), depth=1.0)
        app.icon(cx, y + 60, icon, 13, GOLD)
        app.text(cx, y + 112, title, 13, "bold", anchor="center")
        for i, ln in enumerate(app.wrap(sub, 10, min(520, x1 - x0 - 60), max_lines=3)):
            app.text(cx, y + 136 + 18 * i, ln, 10, fill=MUTED, anchor="center")
        if action:
            lab, fn, name = action
            self.button(cx, y + 200, lab, fn, name, "refresh", anchor="center")

    def open_match(self, mt):
        app = self.app
        f = MATCH_DIR / f"{mt.get('id')}.json"
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
            det = match_detail(d, self.puuid, {self.puuid: self.f.get("name")})
        except Exception as e:
            app.toast(f"Couldn't open that match: {describe_err(e)}", "bad", tray=False)
            return
        if app.streamer():
            for t in det["teams"]:
                for r in t["rows"]:
                    r["name"] = (ASSETS.agents.get(r["agent"]) or {}).get("name") or "Player"
        MatchLayer(app, det, who=self.f.get("name"))

    def draw_chat(self, x0, top, x1, bot, name):
        app = self.app
        ch = self.chat
        log_bot = bot - 58
        app.rrect(x0, top, x1, log_bot, 16, fill=mix(SURFACE, BG, 0.3), outline=LINE, depth=0)
        msgs = list(ch.get("msgs") or [])
        if ch.get("pending"):
            msgs.append({"body": ch["pending"], "puuid": ch.get("me"), "_pending": True})
        maxw = int((x1 - x0) * 0.62)
        if ch.get("msgs") is None and not ch.get("err"):
            for i in range(4):
                yy = log_bot - 20 - 46 * (i + 1)
                mine = i % 2 == 0
                wv = 120 + 60 * (i % 3)
                bx = x1 - 20 - wv if mine else x0 + 20
                app.skel(bx, yy, bx + wv, yy + 34, 14, i)
        elif ch.get("err") and not ch.get("msgs"):
            cx = (x0 + x1) / 2
            cy = (top + log_bot) / 2
            app.circle(cx, cy - 30, 22, fill=mix(SURFACE, GOLD, 0.15), depth=0)
            app.icon(cx, cy - 30, "chat", 11, GOLD)
            app.text(cx, cy + 8, "Chat isn't reachable right now", 11, "bold", anchor="center")
            for i, ln in enumerate(app.wrap(ch["err"], 9, x1 - x0 - 80, max_lines=2)):
                app.text(cx, cy + 30 + 16 * i, ln, 9, fill=MUTED, anchor="center")
        elif not msgs:
            cx, cy = (x0 + x1) / 2, (top + log_bot) / 2
            app.text(cx, cy - 6, f"No messages with {name} yet", 11, "bold", anchor="center")
            app.text(cx, cy + 16, "Say hi - it goes through your Riot Client's chat.", 9,
                     fill=MUTED, anchor="center")
        else:
            # bubbles, newest at the bottom; the wheel scrolls back
            y = log_bot - 14 + self.chat_scroll
            total = 0
            me = ch.get("me")
            prev_mine = None
            for m in reversed(msgs):
                mine = m.get("puuid") == me
                lines = app.wrap(m.get("body") or "", 10, maxw - 28)
                bh = 16 + 18 * len(lines)
                bw = min(maxw, max(app.measure(ln, 10) for ln in lines) + 28)
                gap = 4 if prev_mine == mine else 10
                y -= bh
                bx = x1 - 16 - bw if mine else x0 + 16
                if top + 4 < y + bh and y < log_bot:
                    fill = (mix(ACCENT, SURFACE, 0.35) if m.get("_pending") else ACCENT) \
                        if mine else CARD_HI
                    app.rrect(bx, y, bx + bw, y + bh, 14, fill=fill, depth=0)
                    for i, ln in enumerate(lines):
                        app.text(bx + 14, y + 17 + 18 * i, ln, 10, fill=TEXT)
                y -= gap
                total += bh + gap
                prev_mine = mine
            span = log_bot - top - 28
            self.chat_scroll = min(self.chat_scroll, max(0.0, total - span))
            # fade-out edge at the top of the log so cut-off bubbles don't look broken
            app.rrect(x0 + 1, top + 1, x1 - 1, top + 14, 15, fill=mix(SURFACE, BG, 0.3), depth=0)
        app.cv.create_rectangle(x0, log_bot + 1, x1, bot + 4, fill=SURFACE, outline="")
        iy = log_bot + 12
        self.entry("msg", self.var, x0, iy, x1 - x0 - 104, 40, on_return=self.send,
                   hint=f"Message {name}…")
        self.button(x1, iy + 2, "Sending…" if ch.get("sending") else "Send", self.send, "send",
                    "chat", anchor="e", h=36, disabled=ch.get("sending") or not self.var.get().strip())
        self.max_scroll = 0


class MatchLayer(Layer, ScrollBody):
    """One match: result header, the round-by-round strip and both scoreboards."""
    W, H = 900, 720
    COLS = [("ACS", 54), ("K / D / A", 90), ("+/-", 46), ("HS%", 52), ("ADR", 52),
            ("DD", 52), ("FB", 38)]

    def __init__(self, app, det, who=None):
        self.det, self.who = det, who
        super().__init__(app)

    def draw(self, x0, y0, x1, y1):
        app = self.app
        det = self.det
        top, bot = y0 + 150, y1 - 46
        self.glide_scroll()
        self.draw_body(x0 + 26, top, x1 - 26, bot)
        self.mask(x0, y0, x1, y1, top, bot)
        app.text(x0 + 26, y1 - 24, "Names show for the highlighted player, their party and "
                 "your saved accounts; everyone else is shown by agent.", 8, fill=DIM,
                 maxw=x1 - x0 - 52)
        mp = ASSETS.maps.get(det["map"], {})
        ban = (x0 + 8, y0 + 8, x1 - 8, y0 + 132)
        if not app.image(mp.get("splash") or mp.get("icon"), ban[0], ban[1], ban[2] - ban[0],
                         ban[3] - ban[1], mode="cover", radius=14, fade=True):
            app.rrect(*ban, 14, fill=mix(SURFACE, ACCENT, 0.15), depth=0)
        won = det["won"]
        col = GOOD if won is True else (DANGER if won is False else MUTED)
        res = "Victory" if won is True else ("Defeat" if won is False else "Draw")
        a, b = det["score"]
        app.text(x0 + 34, y0 + 48, res, 22, "bold", col)
        if a is not None:
            app.text(x0 + 46 + app.measure(res, 22, "bold"), y0 + 48, f"{a} – {b}", 22, "bold")
        mins = int(det["length"] // 60)
        meta = "  ·  ".join(x for x in (mp.get("name"), det["queue"], ago(det["start"], "").strip(),
                                        f"{mins} min" if mins else "") if x)
        app.text(x0 + 34, y0 + 82, meta, 10, "bold", SOFT)
        if self.who:
            app.text(x0 + 34, y0 + 106, f"Highlighted: {self.who.split('#')[0]}", 9,
                     fill=MUTED)
        self.close_btn(x1 - 34, y0 + 34)

    def draw_body(self, x0, top, x1, bot):
        app = self.app
        det = self.det
        y = top + 10 - self.scroll
        rounds = det.get("rounds") or []
        V = lambda a, b: self.vis(a, b, top, bot)       # noqa: E731
        if rounds and not V(y, y + 60):
            y += 68
            rounds = []
            skip_rounds = True
        else:
            skip_rounds = False
        if rounds:
            app.text(x0, y + 6, "Rounds", 9, "bold", DIM)
            app.text(x1, y + 6, "E eliminated · B spike detonated · D defused · T time ran out",
                     8, fill=DIM, anchor="e")
            y += 22
            cw = min(26, (x1 - x0 - 12) / max(1, len(rounds)) - 3)
            rx = x0
            for i, r in enumerate(rounds):
                if i == 12:
                    rx += 10
                c = GOOD if r["won"] else DANGER
                key = self.k(f"r:{i}")
                tip = (f"Round {r['n']}: {'won' if r['won'] else 'lost'} · {r['long']}"
                       + (f" · spike planted on {r['site']}" if r['site'] else ""))
                tags = self.row_box(key, rx, y, rx + cw, y + 30, top, bot, None, tip=tip)
                app.rrect(rx, y, rx + cw, y + 30, 7,
                          fill=mix(SURFACE, c, 0.32 + 0.25 * app.hv(key)), depth=0, tags=tags)
                app.text(rx + cw / 2, y + 15, r["short"], 8, "bold", TEXT, anchor="center",
                         tags=tags)
                rx += cw + 3
            y += 46
        elif not skip_rounds and det.get("rounds"):
            y += 68
        for tab in det["teams"]:
            tcol = GOOD if tab["won"] is True else (DANGER if tab["won"] is False else MUTED)
            cx = x1 - sum(w for _, w in self.COLS)
            if V(y, y + 44):
                app.text(x0, y + 8, tab["label"], 11, "bold", tcol)
                if tab["rounds"] is not None:
                    app.text(x0 + app.measure(tab["label"], 11, "bold") + 10, y + 9,
                             f"{tab['rounds']} rounds", 9, fill=DIM)
                hx = cx
                for lab, w in self.COLS:
                    app.text(hx + w / 2, y + 32, lab, 8, "bold", DIM, anchor="center")
                    hx += w
            y += 44
            for ri, r in enumerate(tab["rows"]):
                rh = 36
                if V(y, y + rh - 3):
                    bg = mix(SURFACE, ACCENT, 0.2) if r["me"] else (
                        mix(SURFACE, CARD, 0.55) if ri % 2 == 0 else mix(SURFACE, CARD, 0.25))
                    app.rrect(x0, y, x1, y + rh - 3, 9, fill=bg, depth=0,
                              outline=ACCENT if r["me"] else "")
                    ag = ASSETS.agents.get(r["agent"], {})
                    app.image(ag.get("icon"), x0 + 8, y + 5, 26, 26, radius=7)
                    if r["tier"] >= 3 and not (app.settings.get("focus_mode") and not r["me"]):
                        app.rank_icon(r["tier"], x0 + 52, y + 17, 22)
                    app.text(x0 + 70, y + 17, r["name"], 10, "bold" if r["me"] or r["party"]
                             else "normal", TEXT if r["named"] else MUTED, maxw=cx - x0 - 80)
                    diff = r["k"] - r["d"]
                    vals = [(str(r["acs"]), TEXT), (f"{r['k']} / {r['d']} / {r['a']}", TEXT),
                            (f"{diff:+d}", GOOD if diff > 0 else (DANGER if diff < 0 else MUTED)),
                            (f"{r['hs']:.0f}%" if r["hs"] is not None else "—", SOFT),
                            (str(r["adr"]) if r["adr"] is not None else "—", SOFT),
                            (f"{r['dd']:+d}" if r.get("dd") is not None else "—",
                             GOOD if (r.get("dd") or 0) > 0 else (
                                 DANGER if (r.get("dd") or 0) < 0 else SOFT)),
                            (str(r["fb"]), SOFT)]
                    hx = cx
                    for (txt, fg), (_, w) in zip(vals, self.COLS):
                        app.text(hx + w / 2, y + 17, txt, 9, "bold", fg, anchor="center")
                        hx += w
                y += rh
            y += 16
        self.max_scroll = max(0.0, (y + self.scroll) - bot + 8)
        self.scroll_t = min(self.scroll_t, self.max_scroll)


def set_app_volume(frac):
    """Set this app's own volume (its slider in the Windows volume mixer), 0..1.
    Returns False if Windows refused, so callers can fall back."""
    if sys.platform != "win32":
        return False
    try:
        v = max(0, min(0xFFFF, int(frac * 0xFFFF)))
        return ctypes.windll.winmm.waveOutSetVolume(None, ctypes.c_uint32(v | (v << 16))) == 0
    except Exception:
        return False


_TIMER_FINE = [0]


def timer_resolution(fine):
    """Ask Windows for 1 ms timers while a video plays (its default ~16 ms tick makes 30/60 fps
    frames land unevenly). Reference-counted; released when playback stops."""
    if sys.platform != "win32":
        return
    try:
        w = ctypes.windll.winmm
        if fine:
            if _TIMER_FINE[0] == 0:
                w.timeBeginPeriod(1)
            _TIMER_FINE[0] += 1
        elif _TIMER_FINE[0] > 0:
            _TIMER_FINE[0] -= 1
            if _TIMER_FINE[0] == 0:
                w.timeEndPeriod(1)
    except Exception:
        pass


def extract_audio_wav(src, dst, gain=1.0):
    """Decode a preview video's soundtrack to a 44.1 kHz stereo WAV with PyAV.
    Returns False when the video has no audio track."""
    import av
    import wave
    from array import array
    tmp = dst.with_suffix(f".{threading.get_ident()}.part")
    n = 0
    with av.open(str(src)) as box:
        if not box.streams.audio:
            return False
        st = box.streams.audio[0]
        rs = av.AudioResampler(format="s16", layout="stereo", rate=44100)
        with wave.open(str(tmp), "wb") as w:
            w.setnchannels(2)
            w.setsampwidth(2)
            w.setframerate(44100)

            def write(frames):
                nonlocal n
                if frames is None:
                    return
                for fr in (frames if isinstance(frames, list) else [frames]):
                    data = bytes(fr.planes[0])[: fr.samples * 4]
                    if gain != 1.0:
                        a = array("h", data)
                        a = array("h", (max(-32768, min(32767, int(x * gain))) for x in a))
                        data = a.tobytes()
                    w.writeframes(data)
                    n += fr.samples
            for fr in box.decode(st):
                write(rs.resample(fr))
            try:
                write(rs.resample(None))       # flush
            except Exception:
                pass
    if not n:
        tmp.unlink(missing_ok=True)
        return False
    tmp.replace(dst)
    return True


class WaveOut:
    """Plays 16-bit PCM straight through the Windows audio device (winmm waveOut) from memory.
    Unlike PlaySound it starts at once (nothing to load from disk) and it can say exactly how
    far playback has got, which the video uses as its clock so picture and sound stay in step."""

    class _FMT(ctypes.Structure):
        _pack_ = 1                              # mmreg.h packs WAVEFORMATEX to 18 bytes
        _fields_ = [("wFormatTag", ctypes.c_ushort), ("nChannels", ctypes.c_ushort),
                    ("nSamplesPerSec", ctypes.c_uint32), ("nAvgBytesPerSec", ctypes.c_uint32),
                    ("nBlockAlign", ctypes.c_ushort), ("wBitsPerSample", ctypes.c_ushort),
                    ("cbSize", ctypes.c_ushort)]

    class _HDR(ctypes.Structure):
        pass

    _HDR._fields_ = [("lpData", ctypes.c_void_p), ("dwBufferLength", ctypes.c_uint32),
                     ("dwBytesRecorded", ctypes.c_uint32), ("dwUser", ctypes.c_size_t),
                     ("dwFlags", ctypes.c_uint32), ("dwLoops", ctypes.c_uint32),
                     ("lpNext", ctypes.c_void_p), ("reserved", ctypes.c_size_t)]

    class _MMTIME(ctypes.Structure):
        _fields_ = [("wType", ctypes.c_uint32), ("value", ctypes.c_uint32),
                    ("pad", ctypes.c_uint32)]

    _api = None

    @classmethod
    def api(cls):
        if cls._api is None:
            w = ctypes.windll.winmm
            H, P, U = ctypes.c_void_p, ctypes.c_void_p, ctypes.c_uint32
            w.waveOutOpen.argtypes = [ctypes.POINTER(H), U, P, ctypes.c_size_t,
                                      ctypes.c_size_t, U]
            for f in ("waveOutPrepareHeader", "waveOutUnprepareHeader", "waveOutWrite",
                      "waveOutGetPosition"):
                getattr(w, f).argtypes = [H, P, U]
            for f in ("waveOutReset", "waveOutClose"):
                getattr(w, f).argtypes = [H]
            w.waveOutSetVolume.argtypes = [H, U]
            for f in ("waveOutOpen", "waveOutPrepareHeader", "waveOutUnprepareHeader",
                      "waveOutWrite", "waveOutGetPosition", "waveOutReset", "waveOutClose",
                      "waveOutSetVolume"):
                getattr(w, f).restype = U
            cls._api = w
        return cls._api

    def __init__(self, pcm, rate=44100, channels=2):
        w = self.api()
        self.rate, self.block = rate, channels * 2
        self.duration = len(pcm) / (rate * self.block)
        self.buf = ctypes.create_string_buffer(pcm, len(pcm))     # must outlive playback
        fmt = self._FMT(1, channels, rate, rate * self.block, self.block, 16, 0)
        self.h = ctypes.c_void_p()
        if w.waveOutOpen(ctypes.byref(self.h), 0xFFFFFFFF, ctypes.byref(fmt), 0, 0, 0):
            raise RuntimeError("no audio output device")
        self.hdr = self._HDR()
        self.hdr.lpData = ctypes.cast(self.buf, ctypes.c_void_p)
        self.hdr.dwBufferLength = len(pcm)
        if w.waveOutPrepareHeader(self.h, ctypes.byref(self.hdr), ctypes.sizeof(self.hdr)):
            w.waveOutClose(self.h)
            raise RuntimeError("audio device refused the sound")
        self.playing = False

    def play(self):
        """(Re)start from the beginning."""
        w = self.api()
        w.waveOutReset(self.h)
        self.hdr.dwFlags &= 0x00000002          # keep only WHDR_PREPARED
        if w.waveOutWrite(self.h, ctypes.byref(self.hdr), ctypes.sizeof(self.hdr)):
            raise RuntimeError("audio device refused the sound")
        self.playing = True

    def position(self):
        """Seconds actually played so far (0 until the device really starts)."""
        t = self._MMTIME(4, 0, 0)               # TIME_BYTES
        if self.api().waveOutGetPosition(self.h, ctypes.byref(t), ctypes.sizeof(t)):
            return None
        if t.wType == 4:
            return t.value / (self.rate * self.block)
        if t.wType == 2:                        # TIME_SAMPLES
            return t.value / self.rate
        if t.wType == 1:                        # TIME_MS
            return t.value / 1000
        return None

    def volume(self, frac):
        v = max(0, min(0xFFFF, int(frac * 0xFFFF)))
        self.api().waveOutSetVolume(self.h, v | (v << 16))

    def stop(self):
        if self.playing:
            self.api().waveOutReset(self.h)
            self.playing = False

    def close(self):
        try:
            w = self.api()
            w.waveOutReset(self.h)
            w.waveOutUnprepareHeader(self.h, ctypes.byref(self.hdr), ctypes.sizeof(self.hdr))
            w.waveOutClose(self.h)
        except Exception:
            pass
        self.playing = False


class PreviewAudio:
    """The soundtrack of a skin preview, restarted with every loop of the video so the two
    stay in step. Only one preview can make sound at a time, app-wide; volume and mute are
    remembered (Settings: preview_volume / preview_muted)."""
    current = None

    def __init__(self, app):
        self.app = app
        self.wav = None
        self.status = "idle"          # idle | loading | ready | none | error | unsupported
        self.err = ""
        self.stopped = False
        self._fallback_gain = None
        self.out = None               # WaveOut, when the device opened
        self.started_at = None        # wall clock of the last (re)start, for the fallback

    @staticmethod
    def supported():
        if sys.platform != "win32":
            return False
        try:
            import winsound  # noqa
        except ImportError:
            return False
        return VideoPlayer.backend() == "av"

    def level(self):
        st = self.app.settings
        if st.get("preview_muted"):
            return 0.0
        v = max(0, min(100, int(st.get("preview_volume", 60)))) / 100
        return v * v                   # perceptual curve: the slider feels even

    def prepare(self, src):
        """Background thread: make the WAV next to the cached video."""
        if not self.supported():
            self.status = "unsupported"
            return
        self.status = "loading"
        dst = VIDEO_DIR / (Path(str(src)).stem + ".wav")
        try:
            if not (dst.exists() and dst.stat().st_size > 44):
                if not extract_audio_wav(src, dst):
                    self.status = "none"
                    return
            self.wav = dst
            try:
                import wave
                with wave.open(str(dst)) as r:
                    pcm = r.readframes(r.getnframes())
                    rate, ch = r.getframerate(), r.getnchannels()
                if not self.stopped:
                    self.out = WaveOut(pcm, rate, ch)
            except Exception:
                self.out = None       # PlaySound below still works, just less precisely
            self.status = "ready"
        except Exception as e:
            self.status, self.err = "error", describe_err(e)

    def start(self):
        """UI thread, on the first frame of every loop."""
        if self.stopped or not self.wav:
            return
        try:
            import winsound
        except ImportError:
            return
        if PreviewAudio.current not in (None, self):
            PreviewAudio.current.stop()
        PreviewAudio.current = self
        wav = self.wav
        self.started_at = time.time()
        if self.out:
            try:
                # muted = volume 0 but still playing, so unmuting is instant and in sync
                self.out.volume(self.level())
                self.out.play()
                return
            except Exception:
                self.out.close()
                self.out = None
        try:
            if set_app_volume(self.level()):
                # muted = volume 0 but still playing, so unmuting is instant and in sync
                winsound.PlaySound(str(wav), winsound.SND_FILENAME | winsound.SND_ASYNC
                                   | winsound.SND_NODEFAULT)
            elif self.level() <= 0:
                winsound.PlaySound(None, 0)
            else:
                # Windows wouldn't set our volume: play a copy with the volume baked in
                winsound.PlaySound(str(self._scaled()), winsound.SND_FILENAME
                                   | winsound.SND_ASYNC | winsound.SND_NODEFAULT)
        except Exception as e:
            self.status, self.err = "error", describe_err(e)

    def _scaled(self):
        g = round(self.level(), 1)
        p = self.wav.with_name(self.wav.stem + f".g{int(g * 10)}.wav")
        if not p.exists():
            try:
                import wave
                from array import array
                with wave.open(str(self.wav)) as r:
                    params, data = r.getparams(), r.readframes(r.getnframes())
                a = array("h", data)
                a = array("h", (int(x * g) for x in a))
                with wave.open(str(p), "wb") as w:
                    w.setparams(params)
                    w.writeframes(a.tobytes())
            except Exception:
                return self.wav
        return p

    def clock(self):
        """How far into the soundtrack playback really is, or None if unknown."""
        if self.out and self.out.playing and PreviewAudio.current is self:
            try:
                return self.out.position()
            except Exception:
                return None
        return None

    def apply(self):
        """Volume or mute changed while playing."""
        if PreviewAudio.current is self and not self.stopped:
            if self.out:
                try:
                    self.out.volume(self.level())
                    return
                except Exception:
                    pass
            if not set_app_volume(self.level()):
                self.start()           # fallback path re-renders at the new level

    def stop(self):
        self.stopped = True
        out, self.out = self.out, None
        if out:
            out.close()
        if PreviewAudio.current is self:
            PreviewAudio.current = None
            try:
                import winsound
                winsound.PlaySound(None, 0)
            except Exception:
                pass
            set_app_volume(1.0)


class VideoPlayer:
    """Plays a skin preview video inside a Label. Decodes with PyAV (pip install av) or
    OpenCV in a background thread; frames are scaled there so the UI thread only pastes."""

    def __init__(self, app, label, url, w, h, on_text=None, audio=None):
        self.app, self.label, self.url, self.w, self.h = app, label, url, w, h
        self.audio = audio
        self.on_text = on_text or (lambda t: None)
        self.q = queue.Queue(maxsize=24)
        self.stop_flag = False
        self.fps = 30.0
        self.photo = None
        self.last = 0.0
        self.pending = None           # next (image, time, first) waiting for its moment
        self.t0 = None                # wall clock when the current loop started
        self.shown_t = -1.0           # timestamp of the frame on screen
        self._fine = False            # holding Windows' 1 ms timer
        self.status = "Loading video…"
        self.on_text(self.status)
        threading.Thread(target=self._work, daemon=True).start()
        self.app.after(30, self._tick)

    @staticmethod
    def backend():
        try:
            import av  # noqa
            return "av"
        except Exception:
            pass
        try:
            import cv2  # noqa
            return "cv2"
        except Exception:
            return None

    def stop(self):
        self.stop_flag = True
        if self.audio:
            self.audio.stop()
        if self._fine:
            self._fine = False
            timer_resolution(False)

    _fetching = set()

    @staticmethod
    def cache_path(url):
        return VIDEO_DIR / (hashlib.sha1(url.encode()).hexdigest() + ".mp4")

    @classmethod
    def prefetch(cls, url):
        """Download a preview in the background so pressing Play is instant."""
        if not url or url in cls._fetching:
            return
        p = cls.cache_path(url)
        if p.exists() and p.stat().st_size > 1000:
            return
        cls._fetching.add(url)

        def work():
            try:
                VIDEO_DIR.mkdir(parents=True, exist_ok=True)
                tmp = p.with_suffix(f".{threading.get_ident()}.part")
                req = urllib.request.Request(url, headers={"User-Agent": UA})
                with urllib.request.urlopen(req, timeout=40) as r, open(tmp, "wb") as f:
                    shutil.copyfileobj(r, f, 512 * 1024)
                tmp.replace(p)
            except Exception:
                pass
            finally:
                cls._fetching.discard(url)
        threading.Thread(target=work, daemon=True).start()

    def _say(self, t):
        self.status = t
        self.app.call_ui(lambda: self.on_text(t))

    def _download(self):
        VIDEO_DIR.mkdir(parents=True, exist_ok=True)
        path = VIDEO_DIR / (hashlib.sha1(self.url.encode()).hexdigest() + ".mp4")
        if path.exists() and path.stat().st_size > 1000:
            return path
        tmp = path.with_suffix(".part")
        req = urllib.request.Request(self.url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=30) as r, open(tmp, "wb") as f:
            total = int(r.headers.get("Content-Length") or 0)
            got = 0
            while not self.stop_flag:
                chunk = r.read(256 * 1024)
                if not chunk:
                    break
                f.write(chunk)
                got += len(chunk)
                if total:
                    self._say(f"Loading video… {got * 100 // total}%")
        if self.stop_flag:
            tmp.unlink(missing_ok=True)
            return None
        tmp.replace(path)
        return path

    def _fit(self, iw, ih):
        k = min(self.w / iw, self.h / ih)
        return max(2, int(iw * k) // 2 * 2), max(2, int(ih * k) // 2 * 2)

    def _work(self):
        try:
            cached = self.cache_path(self.url)
            be = self.backend()
            if self.audio and be == "av" and self.audio.supported():
                # sound needs the whole file: finish the download, pull out the track, then
                # start picture and sound together
                waited = 0.0
                while self.url in VideoPlayer._fetching and not self.stop_flag and waited < 90:
                    if not waited:
                        self._say("Loading video…")
                    time.sleep(0.2)                 # the prefetch is already on it
                    waited += 0.2
                src = self._download()
                if not src or self.stop_flag:
                    return
                self._say("Loading sound…")
                self.audio.prepare(src)
            elif cached.exists() and cached.stat().st_size > 1000:
                src = cached
            else:
                # start playing straight from the web while the file caches for next time
                src = self.url
                self.prefetch(self.url)
            while not self.stop_flag:
                n = 0
                if src == self.url and cached.exists() and cached.stat().st_size > 1000:
                    src = cached
                for im, t in (self._frames_av(src) if be == "av" else self._frames_cv(src)):
                    if n == 0:
                        self._say("")
                    if self.stop_flag:
                        return
                    while not self.stop_flag:          # bounded wait so stop() is prompt
                        try:
                            self.q.put((im, t, n == 0), timeout=0.25)
                            break
                        except queue.Full:
                            continue
                    n += 1
                if not n:
                    raise RuntimeError("no frames")
        except Exception as e:
            self._say(f"Couldn't play this video ({describe_err(e)})")

    def _frames_av(self, path):
        import av
        kw = {"timeout": 15} if str(path).startswith("http") else {}
        with av.open(str(path), **kw) as box:
            st = box.streams.video[0]
            st.thread_type = "AUTO"
            try:
                self.fps = float(st.average_rate or 30) or 30.0
            except Exception:
                self.fps = 30.0
            size = None
            start = None
            n = 0
            for fr in box.decode(st):
                if self.stop_flag:
                    return
                if size is None:
                    size = self._fit(fr.width, fr.height)
                t = fr.time
                if t is None:
                    t = n / self.fps
                if start is None:
                    start = t
                n += 1
                yield fr.to_image(width=size[0], height=size[1]), max(0.0, t - start)

    def _frames_cv(self, path):
        import cv2
        cap = cv2.VideoCapture(str(path))
        try:
            self.fps = cap.get(cv2.CAP_PROP_FPS) or 30.0
            size = None
            n = 0
            while not self.stop_flag:
                ok, fr = cap.read()
                if not ok:
                    return
                if size is None:
                    size = self._fit(fr.shape[1], fr.shape[0])
                fr = cv2.resize(fr, size, interpolation=cv2.INTER_AREA)
                yield Image.fromarray(cv2.cvtColor(fr, cv2.COLOR_BGR2RGB)), n / self.fps
                n += 1
        finally:
            cap.release()

    def _tick(self):
        if self.stop_flag:
            if self._fine:
                self.stop()
            return
        try:
            if not self.label.winfo_exists():
                self.stop()
                return
        except tk.TclError:
            self.stop()
            return
        im = self._due(time.time())
        if im is not None:
            self.last = time.time()
            if self.photo is None or (self.photo.width(), self.photo.height()) != im.size:
                self.photo = ImageTk.PhotoImage(im)
                self.label.config(image=self.photo, text="")
                self.label.image = self.photo
            else:
                self.photo.paste(im)
        self.app.after(5, self._tick)

    def _clock(self, now):
        """Position in the current loop. Follows the sound's real playback position when
        there is one, so the picture can never drift away from what you hear."""
        if self.t0 is None:
            return -1.0
        a = self.audio.clock() if self.audio else None
        wall = now - self.t0
        if a is None:
            return wall
        if a <= 0 and wall < 1.0:
            return 0.0                    # device hasn't started yet: hold the first frame
        out = self.audio.out
        if out and a >= out.duration - 0.03 and wall > a:
            return wall                   # soundtrack shorter than the video: carry on
        return a

    def _due(self, now):
        """The newest frame whose time has come (late frames are skipped, not queued up)."""
        show = None
        while True:
            if self.pending is None:
                try:
                    self.pending = self.q.get_nowait()
                except queue.Empty:
                    return show
            im, t, first = self.pending
            if first:
                # a new loop: start it once the previous one has run its course
                if self.t0 is not None and self._clock(now) < self.shown_t + 1 / max(1.0, self.fps):
                    return show
                if not self._fine:
                    self._fine = True
                    timer_resolution(True)
                if self.audio:
                    self.audio.start()    # restart the sound together with the picture
                self.t0 = now
                self.shown_t = t
                self.pending = None
                show = im
                continue
            if t > self._clock(now):
                return show
            self.shown_t = t
            self.pending = None
            show = im


class SheetModal(Sheet):
    def __init__(self, app, title, message, entry=None, ok="OK", cancel="Cancel",
                 danger=False, password=False, confirm_password=False):
        super().__init__(app)
        self.app, self.result = app, None
        self.title(title)
        self.configure(bg=SURFACE)
        self.resizable(False, False)
        if app.winfo_viewable():
            self.transient(app)
        f = tk.Frame(self, bg=SURFACE, padx=26, pady=22)
        f.pack(fill="both")
        tk.Label(f, text=title, bg=SURFACE, fg=TEXT, font=(app.UI, 14, "bold"),
                 anchor="w").pack(fill="x")
        tk.Label(f, text=message, bg=SURFACE, fg=MUTED, font=(app.UI, 10), justify="left",
                 wraplength=380, anchor="w").pack(fill="x", pady=(6, 12))
        self.var = self.var2 = None
        if entry is not None or password:
            self.var = tk.StringVar(value=entry or "")
            e = app.entry(f, self.var, show="•" if password else "")
            e.pack(fill="x", ipady=7, pady=(0, 8 if confirm_password else 14))
            e.focus_set()
            e.select_range(0, "end")
            if confirm_password:
                self.var2 = tk.StringVar()
                tk.Label(f, text="Repeat password", bg=SURFACE, fg=DIM, font=(app.UI, 8, "bold"),
                         anchor="w").pack(fill="x")
                app.entry(f, self.var2, show="•").pack(fill="x", ipady=7, pady=(2, 14))
        self.err = tk.Label(f, text="", bg=SURFACE, fg=DANGER, font=(app.UI, 9), anchor="w")
        self.err.pack(fill="x")
        row = tk.Frame(f, bg=SURFACE)
        row.pack(fill="x", pady=(4, 0))
        app.button(row, ok, DANGER if danger else ACCENT, self.ok).pack(side="right")
        if cancel:
            app.button(row, cancel, CARD, self.destroy).pack(side="right", padx=8)
        self.bind("<Return>", lambda e: self.ok())
        self.bind("<Escape>", lambda e: self.destroy())
        app.center(self)
        self.wait_window()

    def ok(self):
        if self.var2 is not None and self.var.get() != self.var2.get():
            self.err.config(text="Passwords don't match.")
            return
        self.result = self.var.get() if self.var is not None else True
        self.destroy()


class ConfirmLayer(Layer):
    """Confirmations, notices and one-line prompts. Same API as before:
    Modal(app, title, message, ...).result blocks until the user answers."""
    W = 480

    def __init__(self, app, title, message, entry=None, ok="OK", cancel="Cancel",
                 danger=False, password=False, confirm_password=False, block=True,
                 opaque=False):
        self.opaque = opaque
        self.title, self.message = title, message
        self.ok_label, self.cancel_label, self.danger = ok, cancel, danger
        self.result = None
        self.err = ""
        self.var = tk.StringVar(app, value=entry or "") if (entry is not None or password) else None
        self.var2 = tk.StringVar(app) if confirm_password else None
        self.password = password
        self.dismiss = bool(cancel)
        self._done = tk.IntVar(app, value=0)
        super().__init__(app)
        if self.var is not None:
            self.focus("e1")
        if block:
            try:
                app.wait_variable(self._done)
            except tk.TclError:
                pass

    def size(self, w, h):
        lines = self.app.wrap(self.message, 10, self.W - 64)
        hgt = 96 + 20 * len(lines) + (54 if self.var is not None else 0) + \
            (70 if self.var2 is not None else 0) + (22 if self.err else 0) + 66
        return min(self.W, w - 48), min(hgt, h - 48)

    def draw(self, x0, y0, x1, y1):
        app = self.app
        px = x0 + 30
        y = y0 + 34
        if self.danger:
            app.circle(x1 - 40, y0 + 40, 16, fill=mix(SURFACE, DANGER, 0.2), depth=0)
            app.icon(x1 - 40, y0 + 40, "warning", 10, DANGER)
        app.text(px, y, self.title, 15, "bold", maxw=x1 - x0 - 110)
        y += 30
        for ln in app.wrap(self.message, 10, self.W - 64):
            app.text(px, y, ln, 10, fill=MUTED)
            y += 20
        y += 8
        if self.var is not None:
            self.entry("e1", self.var, px, y, x1 - x0 - 60, 40, show="•" if self.password else "",
                       on_return=self.ok)
            y += 54
        if self.var2 is not None:
            app.text(px, y + 6, "Repeat password", 8, "bold", DIM)
            self.entry("e2", self.var2, px, y + 20, x1 - x0 - 60, 40, show="•",
                       on_return=self.ok)
            y += 70
        if self.err:
            app.text(px, y + 4, self.err, 9, fill=DANGER)
        bx = x1 - 30
        by = y1 - 30 - 38
        bx -= self.button(bx, by, self.ok_label, self.ok, "ok", danger=self.danger,
                          anchor="e", h=38) + 10
        if self.cancel_label:
            self.button(bx, by, self.cancel_label, self.close, "cancel", primary=False,
                        anchor="e", h=38)

    def on_key(self, seq, e):
        if seq == "<Return>":
            self.ok()
            return True
        return super().on_key(seq, e)

    def ok(self):
        if self.var2 is not None and self.var.get() != self.var2.get():
            self.err = "Passwords don't match."
            self.app.layer_redraw()
            return
        self.result = self.var.get() if self.var is not None else True
        self.close()

    def on_closing(self):
        try:
            self._done.set(1)
        except tk.TclError:
            pass


def Modal(app, title, message, entry=None, ok="OK", cancel="Cancel", danger=False,
          password=False, confirm_password=False, opaque=False):
    """Ask or tell the user something. Drawn on the canvas, unless one of the classic
    Tk dialogs is already open (it would cover a canvas dialog), then it stacks on that."""
    kw = dict(entry=entry, ok=ok, cancel=cancel, danger=danger, password=password,
              confirm_password=confirm_password)
    if getattr(app, "sheets", None):
        return SheetModal(app, title, message, **kw)
    return ConfirmLayer(app, title, message, opaque=opaque, **kw)


class AccountEditor(Sheet):
    def __init__(self, app, name, meta):
        super().__init__(app)
        self.app, self.result = app, None
        self.title("Edit account")
        self.configure(bg=SURFACE)
        self.resizable(False, False)
        self.transient(app)
        f = tk.Frame(self, bg=SURFACE, padx=26, pady=22)
        f.pack(fill="both")
        tk.Label(f, text="Edit account", bg=SURFACE, fg=TEXT, font=(app.UI, 14, "bold"),
                 anchor="w").pack(fill="x", pady=(0, 10))

        def field(label, var, hint=None):
            tk.Label(f, text=label, bg=SURFACE, fg=MUTED, font=(app.UI, 9, "bold"),
                     anchor="w").pack(fill="x")
            e = app.entry(f, var)
            e.pack(fill="x", ipady=6, pady=(3, 2 if hint else 12))
            if hint:
                tk.Label(f, text=hint, bg=SURFACE, fg=DIM, font=(app.UI, 8),
                         anchor="w").pack(fill="x", pady=(0, 10))
            return e

        self.name = tk.StringVar(value=name)
        self.tags = tk.StringVar(value=", ".join(meta.get("tags") or []))
        self.note = tk.StringVar(value=meta.get("note", ""))
        self.region = tk.StringVar(value=meta.get("region_override") or "Auto")
        field("Name", self.name).focus_set()
        field("Tags", self.tags, "Comma separated, e.g. EUW, Ranked, Smurf")
        field("Note", self.note)
        tk.Label(f, text="VALORANT region", bg=SURFACE, fg=MUTED, font=(app.UI, 9, "bold"),
                 anchor="w").pack(fill="x")
        row = tk.Frame(f, bg=SURFACE)
        row.pack(fill="x", pady=(4, 16))
        self.region_btns = {}
        for r in REGIONS:
            b = tk.Label(row, text=r.upper() if r != "Auto" else "Auto", padx=9, pady=4,
                         font=(app.UI, 9, "bold"), cursor="hand2")
            b.pack(side="left", padx=(0, 4))
            b.bind("<Button-1>", lambda e, r=r: self.pick_region(r))
            self.region_btns[r] = b
        self.pick_region(self.region.get())

        tk.Label(f, text="Status when switching to this account", bg=SURFACE, fg=MUTED,
                 font=(app.UI, 9, "bold"), anchor="w").pack(fill="x")
        row2 = tk.Frame(f, bg=SURFACE)
        row2.pack(fill="x", pady=(4, 16))
        self.dstatus = meta.get("default_status") or "keep"
        self.status_btns = {}
        for k, lab in [("keep", "Don't change")] + list(STATUS_MODES.items()):
            b = tk.Label(row2, text=lab, padx=9, pady=4, font=(app.UI, 9, "bold"),
                         cursor="hand2")
            b.pack(side="left", padx=(0, 4))
            b.bind("<Button-1>", lambda e, k=k: self.pick_status(k))
            self.status_btns[k] = b
        self.pick_status(self.dstatus)

        tk.Label(f, text="Colour label", bg=SURFACE, fg=MUTED, font=(app.UI, 9, "bold"),
                 anchor="w").pack(fill="x")
        crow = tk.Frame(f, bg=SURFACE)
        crow.pack(fill="x", pady=(4, 14))
        self.color = meta.get("color")
        self.color_btns = {}
        for col in [None] + LABEL_COLORS:
            b = tk.Label(crow, text="✕" if col is None else "  ", bg=col or CARD, fg=MUTED,
                         width=3, cursor="hand2", font=(app.UI, 9, "bold"))
            b.pack(side="left", padx=(0, 5))
            b.bind("<Button-1>", lambda e, c=col: self.pick_color(c))
            self.color_btns[col] = b
        self.pick_color(self.color)

        tk.Label(f, text="Game to open for this account", bg=SURFACE, fg=MUTED,
                 font=(app.UI, 9, "bold"), anchor="w").pack(fill="x")
        grow = tk.Frame(f, bg=SURFACE)
        grow.pack(fill="x", pady=(4, 14))
        self.dgame = meta.get("default_game") or "global"
        self.game_btns = {}
        for i, (k, lab) in enumerate([("global", "Use the main setting")] + [(g, g) for g in GAMES]):
            b = tk.Label(grow, text=lab, padx=9, pady=4, font=(app.UI, 9, "bold"), cursor="hand2")
            b.grid(row=i // 4, column=i % 4, padx=(0, 4), pady=(0, 4), sticky="w")
            b.bind("<Button-1>", lambda e, k=k: self.pick_game(k))
            self.game_btns[k] = b
        self.pick_game(self.dgame)

        self.flags = {"archived": bool(meta.get("archived")),
                      "startup": app.settings.get("startup_account") == name}
        self.flag_btns = {}
        for k, lab in (("startup", "Log into this account when RiotHub starts"),
                       ("archived", "Archive (hide from the Accounts page)")):
            b = tk.Label(f, padx=10, pady=6, font=(app.UI, 9, "bold"), cursor="hand2",
                         anchor="w")
            b.pack(fill="x", pady=(0, 6))
            b.bind("<Button-1>", lambda e, k=k, lab=lab: self.flip_flag(k, lab))
            self.flag_btns[k] = (b, lab)
            self.flip_flag(k, lab, init=True)

        self.roulette = bool(meta.get("roulette"))
        self.rbtn = tk.Label(f, padx=10, pady=6, font=(app.UI, 9, "bold"), cursor="hand2",
                             anchor="w")
        self.rbtn.pack(fill="x", pady=(0, 16))
        self.rbtn.bind("<Button-1>", lambda e: self.flip_roulette())
        self.flip_roulette(init=True)
        bar = tk.Frame(f, bg=SURFACE)
        bar.pack(fill="x")
        app.button(bar, "Save", ACCENT, self.ok).pack(side="right")
        app.button(bar, "Cancel", CARD, self.destroy).pack(side="right", padx=8)
        self.bind("<Return>", lambda e: self.ok())
        self.bind("<Escape>", lambda e: self.destroy())
        app.center(self)
        self.wait_window()

    def pick_color(self, c):
        self.color = c
        for k, b in self.color_btns.items():
            b.config(relief="solid" if k == c else "flat", bd=2 if k == c else 0)

    def pick_game(self, k):
        self.dgame = k
        for kk, b in self.game_btns.items():
            b.config(bg=ACCENT if kk == k else CARD, fg=TEXT if kk == k else MUTED)

    def flip_flag(self, k, lab, init=False):
        if not init:
            self.flags[k] = not self.flags[k]
        b, _ = self.flag_btns[k]
        on = self.flags[k]
        b.config(text=("☑  " if on else "☐  ") + lab, bg=ACCENT if on else CARD,
                 fg=TEXT if on else MUTED)

    def pick_status(self, k):
        self.dstatus = k
        for kk, b in self.status_btns.items():
            b.config(bg=ACCENT if kk == k else CARD, fg=TEXT if kk == k else MUTED)

    def flip_roulette(self, init=False):
        if not init:
            self.roulette = not self.roulette
        self.rbtn.config(text=("☑" if self.roulette else "☐") + "  Skin roulette: equip random "
                              "owned skins every time I switch to this account",
                         bg=ACCENT if self.roulette else CARD,
                         fg=TEXT if self.roulette else MUTED)

    def pick_region(self, r):
        self.region.set(r)
        for k, b in self.region_btns.items():
            b.config(bg=ACCENT if k == r else CARD, fg=TEXT if k == r else MUTED)

    def ok(self):
        name = clean_name(self.name.get())
        if not name:
            return
        tags = [t.strip()[:14] for t in self.tags.get().split(",") if t.strip()][:5]
        self.result = {"name": name, "tags": tags, "note": self.note.get().strip()[:140],
                       "region_override": None if self.region.get() == "Auto"
                       else self.region.get(),
                       "default_status": None if self.dstatus == "keep" else self.dstatus,
                       "roulette": self.roulette, "color": self.color,
                       "default_game": None if self.dgame == "global" else self.dgame,
                       "archived": self.flags["archived"], "_startup": self.flags["startup"]}
        self.destroy()


class WelcomeSheet(Sheet):
    """First run: three quick steps, then straight into the app."""

    def __init__(self, app):
        super().__init__(app)
        self.app, self.stage = app, 0
        self.f = tk.Frame(self, bg=SURFACE, padx=34, pady=28, width=520, height=430)
        self.f.pack(fill="both")
        self.f.pack_propagate(False)
        self.bind("<Escape>", lambda e: self.finish())
        self.show()
        app.center(self)

    def clear(self):
        for w in self.f.winfo_children():
            w.destroy()

    def dots(self):
        row = tk.Frame(self.f, bg=SURFACE)
        row.pack(side="bottom", fill="x")
        d = tk.Frame(row, bg=SURFACE)
        d.pack(side="left")
        for i in range(3):
            tk.Label(d, text="●", bg=SURFACE, fg=ACCENT if i == self.stage else CARD_HI,
                     font=(self.app.UI, 8)).pack(side="left", padx=2)
        return row

    def show(self):
        app = self.app
        self.clear()
        if self.stage == 0:
            logo = app.logo_photo(84)
            if logo:
                tk.Label(self.f, image=logo, bg=SURFACE).pack(pady=(18, 14))
            tk.Label(self.f, text=f"Welcome to {APP_TITLE}", bg=SURFACE, fg=TEXT,
                     font=(app.UI, 18, "bold")).pack()
            tk.Label(self.f, text="Save your Riot accounts once, then switch between them and "
                     "launch any Riot game in one click - no passwords, no logging out.",
                     bg=SURFACE, fg=MUTED, font=(app.UI, 10), wraplength=420,
                     justify="center").pack(pady=(10, 0))
            row = self.dots()
            app.button(row, "Get started", ACCENT, self.next).pack(side="right")
            app.button(row, "Skip", CARD, self.finish).pack(side="right", padx=(0, 8))
        elif self.stage == 1:
            tk.Label(self.f, text="Pick a look", bg=SURFACE, fg=TEXT, font=(app.UI, 16, "bold"),
                     anchor="w").pack(fill="x", pady=(8, 2))
            tk.Label(self.f, text="You can change this or choose any colour later in Settings.",
                     bg=SURFACE, fg=MUTED, font=(app.UI, 9), anchor="w").pack(fill="x")
            grid = tk.Frame(self.f, bg=SURFACE)
            grid.pack(fill="x", pady=22)
            for i, (name, pal) in enumerate([(k, v) for k, v in THEMES.items()
                                             if k != "Custom"][:8]):
                on = app.settings.get("theme") == name
                cell = tk.Frame(grid, bg=ACCENT if on else SURFACE, padx=2, pady=2)
                cell.grid(row=i // 4, column=i % 4, padx=8, pady=8)
                sw = tk.Label(cell, bg=pal[0], width=10, height=3, cursor="hand2",
                              text=name, fg="#ffffff", font=(app.UI, 9, "bold"))
                sw.pack()
                sw.bind("<Button-1>", lambda e, n=name: (app.set_theme(n), self.show()))
            row = self.dots()
            app.button(row, "Next", ACCENT, self.next).pack(side="right")
            app.button(row, "Back", CARD, self.back).pack(side="right", padx=(0, 8))
        else:
            tk.Label(self.f, text="Add your first account", bg=SURFACE, fg=TEXT,
                     font=(app.UI, 16, "bold"), anchor="w").pack(fill="x", pady=(8, 2))
            for t in ("1.  The Riot Client opens on its login screen.",
                      "2.  Sign in with 'Stay signed in' ticked.",
                      "3.  RiotHub saves it automatically. Repeat for each account."):
                tk.Label(self.f, text=t, bg=SURFACE, fg=TEXT, font=(app.UI, 10), anchor="w"
                         ).pack(fill="x", pady=(10, 0))
            tk.Label(self.f, text="Your passwords are never seen or stored - only Riot's own "
                     "saved sign-in, kept on this PC.", bg=SURFACE, fg=MUTED, font=(app.UI, 9),
                     anchor="w", wraplength=440, justify="left").pack(fill="x", pady=(18, 0))
            k = tk.Label(self.f, text="Optional: add a free HenrikDev key for the leaderboard "
                         "and always-fresh ranks ›", bg=SURFACE, fg=SOFT, cursor="hand2",
                         font=(app.UI, 9, "bold"), anchor="w")
            k.pack(fill="x", pady=(14, 0))
            k.bind("<Button-1>", lambda e: (self.finish(), app.set_henrik_key()))
            row = self.dots()
            app.button(row, "Add account", ACCENT, lambda: (self.finish(), app.add_new())
                       ).pack(side="right")
            app.button(row, "Later", CARD, self.finish).pack(side="right", padx=(0, 8))

    def next(self):
        self.stage = min(2, self.stage + 1)
        self.show()

    def back(self):
        self.stage = max(0, self.stage - 1)
        self.show()

    def finish(self):
        self.app.state_["onboarded"] = True
        save_state(self.app.state_)
        self.destroy()


class UpdateSheet(Sheet):
    def __init__(self, app, info):
        super().__init__(app)
        self.app, self.upd = app, info
        f = tk.Frame(self, bg=SURFACE, padx=28, pady=24)
        f.pack(fill="both")
        tk.Label(f, text=f"Version {info['version']} is out", bg=SURFACE, fg=TEXT,
                 font=(app.UI, 16, "bold"), anchor="w").pack(fill="x")
        tk.Label(f, text=f"You have {VERSION}.", bg=SURFACE, fg=MUTED, font=(app.UI, 9),
                 anchor="w").pack(fill="x", pady=(2, 12))
        notes = info.get("notes") or "Bug fixes and improvements."
        if len(notes) > 700:
            notes = notes[:700].rsplit("\n", 1)[0] + "\n…"
        tk.Label(f, text=notes, bg=CARD, fg=TEXT, font=(app.UI, 9), anchor="w",
                 justify="left", wraplength=460, padx=14, pady=12).pack(fill="x")
        self.status = tk.Label(f, text="", bg=SURFACE, fg=MUTED, font=(app.UI, 9), anchor="w")
        self.status.pack(fill="x", pady=(10, 0))
        bar = tk.Frame(f, bg=SURFACE)
        bar.pack(fill="x", pady=(12, 0))
        can = getattr(sys, "frozen", False) and bool(
            info.get("setup") if is_installed_copy() else info.get("exe"))
        app.button(bar, "Install and restart" if can else "Download", ACCENT,
                   self.install if can else lambda: webbrowser.open(info.get("page") or "")
                   ).pack(side="right")
        app.button(bar, "Skip this version", CARD, self.skip).pack(side="right", padx=(0, 8))
        app.button(bar, "Later", CARD, self.destroy).pack(side="right", padx=(0, 8))
        self.bind("<Escape>", lambda e: self.destroy())
        app.center(self)

    def skip(self):
        self.app.state_["skip_version"] = self.upd["version"]
        save_state(self.app.state_)
        self.destroy()

    def install(self):
        self.status.config(text="Downloading…")
        info = self.upd

        installed = is_installed_copy()
        url = info["setup"] if installed else info["exe"]
        size = info.get("setup_size") if installed else info.get("size")

        def work():
            try:
                cur = Path(sys.executable)
                if installed:
                    new = Path(os.environ.get("TEMP") or APP_DIR) / f"RiotHub-Setup-{info['version']}.exe"
                else:
                    new = cur.with_name(cur.stem + ".new.exe")
                req = urllib.request.Request(url, headers={"User-Agent": UA})
                got = 0
                try:
                    with urllib.request.urlopen(req, timeout=60) as r, open(new, "wb") as fh:
                        while True:
                            chunk = r.read(256 * 1024)
                            if not chunk:
                                break
                            fh.write(chunk)
                            got += len(chunk)
                            if size:
                                pct = int(100 * got / size)
                                self.app.call_ui(lambda p=pct: self.status.config(
                                    text=f"Downloading… {p}%"))
                except urllib.error.URLError as e:
                    if not is_cert_error(e):
                        raise
                    self.app.call_ui(lambda: self.status.config(text="Downloading…"))
                    curl_fetch(url, out=new, timeout=600)
                    got = Path(new).stat().st_size
                if size and got != size:
                    raise RuntimeError("the download was incomplete")
                wait = (f"for /l %%i in (1,1,40) do (tasklist /fi \"PID eq {os.getpid()}\" "
                        f"| find \"{os.getpid()}\" >nul && timeout /t 1 /nobreak >nul)\r\n")
                if installed:
                    bat = Path(new).with_suffix(".bat")
                    body = (f"start \"\" /wait \"{new}\" /VERYSILENT /SUPPRESSMSGBOXES /NORESTART "
                            f"/DIR=\"{cur.parent}\"\r\n"
                            f"del \"{new}\" >nul 2>&1\r\n")
                else:
                    bat = cur.with_name("finish_update.bat")
                    body = f"move /y \"{new}\" \"{cur}\" >nul\r\n"
                bat.write_text("@echo off\r\n" + wait + body + f"start \"\" \"{cur}\"\r\n"
                               "del \"%~f0\"\r\n", encoding="utf-8")
                subprocess.Popen(["cmd", "/c", str(bat)], creationflags=NO_WINDOW)
                self.app.call_ui(self.app.quit_app)
            except Exception as e:
                err = describe_err(e)
                self.app.call_ui(lambda: self.status.config(text=f"Update failed: {err}",
                                                            fg=DANGER))
        threading.Thread(target=work, daemon=True).start()


class PenaltySheet(Sheet):
    """Everything Riot tells us about an account's penalties, in plain words."""

    def __init__(self, app, name):
        super().__init__(app)
        self.app = app
        m = app.m(name)
        pens = (m.get("penalties") or {}).get("items") or []
        f = tk.Frame(self, bg=SURFACE, padx=26, pady=22)
        f.pack(fill="both")
        tk.Label(f, text=f"{name}'s penalties", bg=SURFACE, fg=TEXT, font=(app.UI, 16, "bold"),
                 anchor="w").pack(fill="x")
        chk = (m.get("penalties") or {}).get("checked")
        tk.Label(f, text=f"Checked {ago(chk, '').strip() or 'just now'}" if chk else "",
                 bg=SURFACE, fg=MUTED, font=(app.UI, 9), anchor="w").pack(fill="x", pady=(2, 12))
        if not pens:
            tk.Label(f, text="No active penalties. ✓", bg=SURFACE, fg=GOOD,
                     font=(app.UI, 12, "bold"), anchor="w").pack(fill="x", pady=8)
        for p in pens:
            card = tk.Frame(f, bg=CARD, padx=16, pady=12)
            card.pack(fill="x", pady=(0, 10))
            top = tk.Frame(card, bg=CARD)
            top.pack(fill="x")
            tk.Label(top, text=p["label"], bg=CARD, fg=DANGER, font=(app.UI, 12, "bold"),
                     anchor="w").pack(side="left")
            left = []
            if p.get("expires"):
                left.append(f"ends in {dur(p['expires'] - time.time())}")
            if p.get("games"):
                left.append(f"{p['games']} game{'s' if p['games'] != 1 else ''} left")
            tk.Label(top, text="  ·  ".join(left) or "no end date given", bg=CARD, fg=TEXT,
                     font=(app.UI, 9, "bold")).pack(side="right")
            for lab, why in p.get("kinds") or []:
                if why:
                    tk.Label(card, text=f"{lab}: {why}", bg=CARD, fg=MUTED, font=(app.UI, 9),
                             anchor="w", justify="left", wraplength=470).pack(fill="x",
                                                                              pady=(6, 0))
            meta = []
            if p.get("started"):
                meta.append("Started " + datetime.fromtimestamp(p["started"]).strftime(
                    "%d %b, %H:%M"))
            if p.get("expires"):
                meta.append("Ends " + datetime.fromtimestamp(p["expires"]).strftime(
                    "%d %b, %H:%M"))
            if p.get("reason"):
                meta.append(f"Reason: {p['reason']}")
            for k, v in list((p.get("detail") or {}).items())[:4]:
                meta.append(f"{k}: {v}")
            if meta:
                tk.Label(card, text="   ·   ".join(meta), bg=CARD, fg=DIM, font=(app.UI, 8),
                         anchor="w", justify="left", wraplength=470).pack(fill="x", pady=(8, 0))
            mid = p.get("match")
            if mid and (MATCH_DIR / f"{mid}.json").exists():
                row = tk.Frame(card, bg=CARD)
                row.pack(fill="x", pady=(10, 0))
                app.button(row, "Open the match it came from", CARD_HI,
                           lambda mid=mid: (self.destroy(), app.open_match(m, {"id": mid}))
                           ).pack(side="left")
        tk.Label(f, text="Riot shows the exact reason (with the chat log for chat penalties) on "
                 "the penalty card that pops up in the Riot Client or game when you next log "
                 "into this account. Logging in with RiotHub shows it too.",
                 bg=SURFACE, fg=MUTED, font=(app.UI, 9), anchor="w", justify="left",
                 wraplength=500).pack(fill="x", pady=(6, 0))
        bar = tk.Frame(f, bg=SURFACE)
        bar.pack(fill="x", pady=(16, 0))
        app.button(bar, "Close", CARD, self.destroy).pack(side="right")
        app.button(bar, "Appeal", CARD_HI, lambda: webbrowser.open(PENALTY_APPEAL_URL)
                   ).pack(side="right", padx=(0, 8))
        app.button(bar, "What penalties mean", CARD_HI,
                   lambda: webbrowser.open(PENALTY_HELP_URL)).pack(side="right", padx=(0, 8))
        self.bind("<Escape>", lambda e: self.destroy())
        app.center(self)


class FullscreenVideo(tk.Toplevel):
    """Black fullscreen viewer for a skin preview. Esc, click or double-click closes it."""

    def __init__(self, app, url, title="", sound=False):
        super().__init__(app)
        self.app = app
        self.overrideredirect(True)
        self.configure(bg="#000000")
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        self.geometry(f"{sw}x{sh}+0+0")
        self.attributes("-topmost", True)
        self.label = tk.Label(self, bg="#000000", fg=MUTED, text="Loading video…",
                              font=(app.UI, 12))
        self.label.place(relx=0.5, rely=0.5, anchor="center")
        cap = tk.Label(self, bg="#000000", fg=DIM, font=(app.UI, 10),
                       text=f"{title}   ·   Esc or click to close")
        cap.place(relx=0.5, rely=0.97, anchor="s")
        self.player = VideoPlayer(app, self.label, url, sw, int(sh * 0.94),
                                  on_text=lambda t: self.label.winfo_exists() and t and
                                  self.label.config(text=t),
                                  audio=PreviewAudio(app) if sound else None)
        for w in (self, self.label, cap):
            w.bind("<Button-1>", lambda e: self.close())
        self.bind("<Escape>", lambda e: self.close())
        self.focus_force()

    def close(self):
        try:
            self.player.stop()
            self.destroy()
        except tk.TclError:
            pass


class CanvasSink:
    """What VideoPlayer draws into when the video lives on the canvas: it just holds the
    current PhotoImage (frames are pasted into it in place, so no redraw per frame)."""

    def __init__(self, app):
        self.app, self.photo, self.alive, self.image = app, None, True, None

    def config(self, image=None, text=None, **kw):
        if image not in (None, ""):
            if image is not self.photo:
                self.photo = image
                self.app.layer_redraw()

    configure = config

    def winfo_exists(self):
        return self.alive


class SkinDialog(Layer):
    """Skin details: a 16:9 stage that plays the preview videos in place - with sound,
    a mute button and a volume slider that are remembered - plus chromas, levels, wishlist
    and equip."""
    W, H = 880, 720

    def __init__(self, app, skin_uuid, owner=None):
        self.skin = ASSETS.skins[skin_uuid]
        self.uuid, self.owner = skin_uuid, owner
        meta = app.m(owner) if owner else {}
        self.owned_levels = owned_ids(meta, "skins")
        self.owned_chromas = owned_ids(meta, "chromas")
        self.owns = skin_uuid in owned_skin_set(meta) if owner else False
        self.chroma_i = 0
        eq = (meta.get("loadout") or {}).get(self.skin["weapon_id"]) or {}
        if eq.get("skin") == skin_uuid:
            for n, c in enumerate(self.skin["chromas"]):
                if c["uuid"] == eq.get("chroma"):
                    self.chroma_i = n
        ct = ASSETS.ctiers.get(self.skin.get("tier") or "", {})
        self.edition = (ct.get("display") or ct.get("name") or "").replace("_EDITION", "") \
            .replace("_Edition", "").title()
        self.tcol = ct.get("color") or ACCENT
        self.player = None
        self.audio = None
        self.sink = None
        self.playing_url = None
        self.vstatus = ""
        super().__init__(app)
        for lv in reversed(self.skin["levels"]):      # warm the cache so Play is instant
            if lv.get("video"):
                VideoPlayer.prefetch(lv["video"])
                break

    # ---- video
    def best_video(self):
        s = self.skin
        ch = s["chromas"][self.chroma_i] if s["chromas"] else {}
        if self.chroma_i and ch.get("video"):
            return ch["video"]
        for lv in reversed(s["levels"]):
            if lv.get("video"):
                return lv["video"]
        return None

    def play(self, url):
        app = self.app
        if not url:
            return
        if not VideoPlayer.backend():
            webbrowser.open(url)
            app.toast("Opened in your browser. In-app previews need the video add-on "
                      "(py -m pip install av).", tray=False)
            return
        self.stop_video()
        self.playing_url = url
        self.sink = CanvasSink(app)
        self.audio = PreviewAudio(app) if PreviewAudio.supported() else None
        self.vstatus = "Loading…"

        def say(t):
            self.vstatus = t or ""
            app.layer_redraw()
        sw, sh = self.stage_size()
        self.player = VideoPlayer(app, self.sink, url, sw, sh, on_text=say, audio=self.audio)
        app.layer_redraw()

    def stop_video(self):
        if self.player:
            self.player.stop()            # stops its sound too
            self.player = None
        if self.sink:
            self.sink.alive = False
            self.sink = None
        self.audio = None
        self.playing_url = None
        self.vstatus = ""

    def fullscreen(self):
        url = self.playing_url or self.best_video()
        if not url:
            return
        if not VideoPlayer.backend():
            return self.play(url)
        self.stop_video()
        FullscreenVideo(self.app, url, self.skin["name"], sound=PreviewAudio.supported())
        self.app.layer_redraw()

    def on_closing(self):
        self.stop_video()

    # ---- sound
    def toggle_mute(self):
        st = self.app.settings
        st["preview_muted"] = not st.get("preview_muted")
        if not st["preview_muted"] and int(st.get("preview_volume", 60)) <= 0:
            st["preview_volume"] = 40
        save_state(self.app.state_)
        if self.audio:
            self.audio.apply()
        self.app.layer_redraw()

    def set_volume_at(self, x):
        sx0, sx1 = getattr(self, "_vol_track", (0, 1))
        v = int(round(max(0.0, min(1.0, (x - sx0) / max(1, sx1 - sx0))) * 100))
        st = self.app.settings
        st["preview_volume"] = v
        st["preview_muted"] = v == 0
        if self.audio:
            self.audio.apply()
        self.app.save_soon()

    # ---- actions
    def pick(self, i):
        self.chroma_i = i
        self.stop_video()
        v = self.best_video()
        if v:
            VideoPlayer.prefetch(v)
        self.app.layer_redraw()

    def toggle_wish(self):
        self.app.toggle_wish(self.uuid)
        self.app.layer_redraw()

    def equip(self):
        ch = self.skin["chromas"][self.chroma_i]["uuid"] if self.skin["chromas"] else None
        if self.chroma_i and ch not in self.owned_chromas:
            self.app.toast("You don't own that chroma - equipped the base one.", tray=False)
            ch = self.skin["chromas"][0]["uuid"]
        self.close()
        self.app.equip_skin(self.uuid, ch)

    def on_key(self, seq, e):
        return super().on_key(seq, e)

    # ---- drawing
    def stage_size(self):
        x0, y0, x1, y1 = self.box
        sw = int((x1 - x0) - 56)
        sh = int(sw * 9 / 16)
        avail = int((y1 - y0) - 300)
        if sh > avail:
            sh = max(180, avail)
            sw = int(sh * 16 / 9)
        return sw, sh

    def size(self, w, h):
        pw = min(self.W, w - 48)
        sh = int((pw - 56) * 9 / 16)
        return pw, min(h - 40, sh + 318)

    def draw(self, x0, y0, x1, y1):
        app, s = self.app, self.skin
        px = x0 + 28
        # header
        app.text(px, y0 + 36, s["name"], 18, "bold", maxw=x1 - x0 - 140)
        y = y0 + 64
        cx = px
        if self.edition:
            cx += app.pill(cx, y, self.edition, fill=mix(SURFACE, self.tcol, 0.35), fg=TEXT) + 10
        price = ASSETS.skin_price(self.uuid)
        sub = "  ·  ".join(b for b in (s["weapon"], f"{price:,} VP" if price else None,
                                       ASSETS.themes.get(s.get("theme") or "")) if b)
        app.text(cx, y, sub, 10, fill=MUTED)
        if self.owns:
            app.pill(x1 - 64, y0 + 36, "✓ Owned", fill=mix(SURFACE, GOOD, 0.2), fg=GOOD,
                     anchor="e")
        self.close_btn(x1 - 34, y0 + 36)
        # stage
        sw, sh = self.stage_size()
        sx0 = x0 + (x1 - x0 - sw) / 2
        sy0 = y0 + 86
        sx1, sy1 = sx0 + sw, sy0 + sh
        stage_bg = mix(BG, self.tcol, 0.08)
        app.rrect(sx0, sy0, sx1, sy1, 14, fill=stage_bg, depth=0,
                  outline=mix(LINE, self.tcol, 0.25))
        playing = self.player is not None
        if playing and self.sink and self.sink.photo:
            app.cv.create_image((sx0 + sx1) / 2, (sy0 + sy1) / 2, image=self.sink.photo)
        elif not playing:
            ch = s["chromas"][self.chroma_i] if s["chromas"] else {}
            url = ch.get("render") or s["icon"]
            if not app.image(url, (sx0 + sx1) / 2, (sy0 + sy1) / 2, sw - 80, sh - 80,
                             anchor="center"):
                if not (app.images and url in app.images.pending):
                    app.text((sx0 + sx1) / 2, (sy0 + sy1) / 2, "No picture for this skin",
                             10, fill=DIM, anchor="center")
        if self.vstatus:
            app.rrect((sx0 + sx1) / 2 - 110, (sy0 + sy1) / 2 - 18, (sx0 + sx1) / 2 + 110,
                      (sy0 + sy1) / 2 + 18, 18, fill="#000000", alpha=0.55, depth=0)
            app.text((sx0 + sx1) / 2, (sy0 + sy1) / 2, self.vstatus, 10, "bold", TEXT,
                     anchor="center", maxw=210)
        self.draw_controls(sx0, sy1, sx1, playing)
        # chromas + levels
        y = sy1 + 26
        if len(s["chromas"]) > 1:
            app.text(px, y, "Chromas", 8, "bold", DIM)
            cx = px + 76
            for i, c in enumerate(s["chromas"]):
                own = (i == 0 and self.owns) or c["uuid"] in self.owned_chromas
                key = self.k(f"ch:{i}")
                on = i == self.chroma_i
                f = app.hv(key)
                lock = bool(self.owner) and not own
                tip = c["name"].split("\n")[0] + ("  ·  locked" if lock else "")
                tags = app.hit(key, click=lambda i=i: self.pick(i), tip=tip)
                if on:
                    app.rrect(cx - 3, y - 18, cx + 33, y + 18, 11, fill="", outline=ACCENT_HI,
                              width=2, depth=0)
                if not app.image(c.get("swatch"), cx, y - 15, 30, 30, radius=8, tags=tags):
                    app.rrect(cx, y - 15, cx + 30, y + 15, 8, fill=CARD_HI, tags=tags, depth=0)
                    app.text(cx + 15, y, str(i + 1), 9, "bold", anchor="center", tags=tags)
                if f > 0 and not on:
                    app.rrect(cx - 2, y - 17, cx + 32, y + 17, 10, fill="",
                              outline=mix(SURFACE, SOFT, f), depth=0)
                if lock:
                    app.circle(cx + 27, y + 12, 7, fill=SURFACE, depth=0)
                    app.icon(cx + 27, y + 12, "lock", 6, DIM)
                cx += 42
            ch_name = (s["chromas"][self.chroma_i].get("name") or "").split("\n")[0]
            app.text(cx + 8, y, ch_name, 9, fill=MUTED, maxw=x1 - cx - 40)
            y += 44
        levels = s["levels"]
        if len(levels) > 1 or (levels and levels[0].get("video")):
            app.text(px, y, "Levels", 8, "bold", DIM)
            cx = px + 76
            for i, lv in enumerate(levels):
                own = lv["uuid"] in self.owned_levels or (i == 0 and self.owns)
                vid = lv.get("video")
                label = f"{i + 1}" + (f" · {lv['item']}" if lv.get("item") else "")
                cur = playing and self.playing_url == vid and vid
                key = self.k(f"lv:{i}")
                lw = app.measure(label, 9, "bold") + (40 if vid else 24)
                if cx + lw > x1 - 28:
                    break
                tags = app.hit(key, click=(lambda v=vid: self.play(v)) if vid else None,
                               tip=("Play this level's video" if vid else "No video for this level")
                               + ("" if own or not self.owner else "  ·  not unlocked"))
                f = app.hv(key)
                fill = ACCENT if cur else (mix(CARD, CARD_HI, f) if vid else mix(CARD, SURFACE, 0.4))
                app.rrect(cx, y - 15, cx + lw, y + 15, 15, fill=fill, tags=tags, depth=0.8)
                fg = TEXT if (cur or (vid and (own or not self.owner))) else DIM
                tx = cx + 14
                if vid:
                    app.icon(tx + 4, y, "play", 7, fg, tags=tags)
                    tx += 16
                app.text(tx, y, label, 9, "bold", fg, tags=tags)
                cx += lw + 8
            y += 44
        # footer
        fy = y1 - 30 - 38
        on = self.uuid in app.state_["wishlist"]
        bx = x1 - 28
        bx -= self.button(bx, fy, "On wishlist" if on else "Add to wishlist", self.toggle_wish,
                          "wish", "star_on" if on else "star", primary=False, anchor="e",
                          h=38) + 10
        active = self.owner and app.state_.get("active") == self.owner
        if self.owns and active:
            self.button(bx, fy, "Equip", self.equip, "equip", "check", anchor="e", h=38)
        note = (f"Owned by {self.owner}. Log into it to equip." if self.owns and not active
                else f"{self.owner} doesn't own this skin." if self.owner and not self.owns
                else "")
        if note:
            app.text(px, fy + 19, note, 9, fill=DIM, maxw=bx - px - 200)

    def draw_controls(self, sx0, sy1, sx1, playing):
        """Bar along the bottom of the stage: play/stop, what's playing, sound, fullscreen."""
        app = self.app
        url = self.best_video()
        bar_y0, bar_y1 = sy1 - 52, sy1 - 10
        if not url and not playing:
            return
        app.rrect(sx0 + 10, bar_y0, sx1 - 10, bar_y1, 21, fill="#05040a", alpha=0.62, depth=0)
        cy = (bar_y0 + bar_y1) / 2
        # play / stop
        key = self.k("pp")
        f = app.hv(key)
        tags = app.hit(key, click=self.stop_video if playing else (lambda: self.play(url)),
                       tip="Stop" if playing else "Play preview")
        app.circle(sx0 + 34, cy, 15 - app.pressed(key),
                   fill=mix(ACCENT, ACCENT_HI, f), tags=tags, depth=1.0)
        app.icon(sx0 + 35 if not playing else sx0 + 34, cy, "stop" if playing else "play", 8,
                 "#ffffff", tags=tags)
        lab = "Playing preview" if playing else "Play preview"
        if playing:
            lvl = next((f"Level {i + 1}" + (f" · {lv['item']}" if lv.get("item") else "")
                        for i, lv in enumerate(self.skin["levels"])
                        if lv.get("video") == self.playing_url), None)
            ch = self.skin["chromas"][self.chroma_i] if self.skin["chromas"] else {}
            if not lvl and ch.get("video") == self.playing_url:
                lvl = (ch.get("name") or "Chroma").split("\n")[0]
            lab = lvl or lab
        app.text(sx0 + 58, cy, lab, 9, "bold", TEXT, maxw=(sx1 - sx0) / 2 - 80)
        # fullscreen
        fk = self.k("fs")
        tags = app.hit(fk, click=self.fullscreen, tip="Fullscreen")
        app.circle(sx1 - 34, cy, 14, fill=mix("#05040a", CARD_HI, app.hv(fk)), tags=tags,
                   depth=0)
        app.icon(sx1 - 34, cy, "fullscreen", 9, app.hcol(fk, SOFT, TEXT), tags=tags)
        # sound: mute toggle + volume slider (remembered)
        st = app.settings
        vol = max(0, min(100, int(st.get("preview_volume", 60))))
        muted = bool(st.get("preview_muted")) or vol == 0
        tx1 = sx1 - 64
        tx0 = tx1 - 120
        self._vol_track = (tx0, tx1)
        mk = self.k("mute")
        sup = PreviewAudio.supported()
        a = self.audio
        why = None
        if not sup:
            why = ("Sound needs the video add-on (py -m pip install av)"
                   if sys.platform == "win32" else "Sound isn't supported on this system")
        elif a and a.status == "none":
            why = "This preview has no sound"
        elif a and a.status == "error":
            why = f"Couldn't play the sound: {a.err}"
        tags = app.hit(mk, click=self.toggle_mute if sup else None,
                       tip=why or ("Unmute" if muted else "Mute"))
        mx = tx0 - 22
        app.circle(mx, cy, 14, fill=mix("#05040a", CARD_HI, app.hv(mk)), tags=tags, depth=0)
        app.icon(mx, cy, "mute" if (muted or why) else "volume", 10,
                 DIM if why else (GOLD if muted else app.hcol(mk, SOFT, TEXT)), tags=tags)
        vk = self.k("vol")
        frac = 0 if muted else vol / 100
        tags = app.hit(vk, down=lambda x, y: self.set_volume_at(x),
                       drag=lambda x, y: self.set_volume_at(x),
                       click=(lambda: None), tip=why or f"Volume {0 if muted else vol}%",
                       box=(tx0 - 6, cy - 12, tx1 + 6, cy + 12))
        tcol = DIM if why else ACCENT_HI
        app.rrect(tx0, cy - 2.5, tx1, cy + 2.5, 2.5, fill=mix("#05040a", SOFT, 0.25), depth=0)
        if frac > 0:
            app.rrect(tx0, cy - 2.5, tx0 + max(5, (tx1 - tx0) * frac), cy + 2.5, 2.5, fill=tcol,
                      depth=0)
        kx = tx0 + (tx1 - tx0) * frac
        kf = max(app.hv(vk), 1.0 if (self.app.press and self.app.press[0] == vk) else 0)
        app.circle(kx, cy, 6 + 1.5 * kf, fill="#ffffff" if not why else MUTED, depth=0.8)
        app.text(tx1 + 2, cy - 15, "" if not playing or why or not a or a.status == "ready"
                 else ("loading sound…" if a.status == "loading" else ""), 7, fill=DIM,
                 anchor="e")


class SkinPicker(Sheet):
    """Pick an owned skin for one weapon and equip it."""

    def __init__(self, app, weapon_name, skins, owner):
        super().__init__(app)
        self.app = app
        self.title(f"{weapon_name} skins")
        self.configure(bg=SURFACE)
        self.resizable(False, False)
        self.transient(app)
        f = tk.Frame(self, bg=SURFACE, padx=20, pady=18)
        f.pack(fill="both")
        tk.Label(f, text=f"{weapon_name} · {len(skins)} owned", bg=SURFACE, fg=TEXT,
                 font=(app.UI, 13, "bold"), anchor="w").pack(fill="x", pady=(0, 10))
        active = owner == app.state_.get("active")
        skins = sorted(skins, key=lambda su: (-ASSETS.ctiers.get(
            ASSETS.skins[su].get("tier") or "", {}).get("rank", 0), ASSETS.skins[su]["name"]))
        rows = (len(skins) - 1) // 4 + 1
        self.scroller = None
        if rows > 4:
            # long lists scroll inside the sheet instead of growing past the window
            self.scroller = tk.Canvas(f, bg=SURFACE, highlightthickness=0, bd=0, width=700,
                                      height=4 * 104)
            self.scroller.pack()
            grid = tk.Frame(self.scroller, bg=SURFACE)
            self.scroller.create_window(0, 0, window=grid, anchor="nw")
            grid.bind("<Configure>", lambda e: self.scroller.configure(
                scrollregion=self.scroller.bbox("all"), width=e.width))
        else:
            grid = tk.Frame(f, bg=SURFACE)
            grid.pack()
        self.labels = []
        for i, su in enumerate(skins):
            s = ASSETS.skins[su]
            im = app.images.get(s["icon"], 150, 56) if app.images else None
            cell = tk.Frame(grid, bg=CARD, padx=8, pady=6, cursor="hand2")
            cell.grid(row=i // 4, column=i % 4, padx=4, pady=4, sticky="nsew")
            a = tk.Label(cell, image=im or "", text="" if im else s["name"], bg=CARD, fg=MUTED,
                         width=None if im else 18, height=None if im else 3)
            a.image = im
            a.pack()
            b = tk.Label(cell, text=s["name"], bg=CARD, fg=TEXT, font=(app.UI, 8, "bold"),
                         wraplength=150)
            b.pack()
            for wdg in (cell, a, b):
                wdg.bind("<Button-1>", lambda e, su=su: self.pick(su, active))
                wdg.bind("<Enter>", lambda e, c=cell: [x.config(bg=CARD_HI) for x in
                                                       [c] + c.winfo_children()])
                wdg.bind("<Leave>", lambda e, c=cell: [x.config(bg=CARD) for x in
                                                       [c] + c.winfo_children()])
        tk.Label(f, text="Click a skin to equip it." if active else
                 f"Log into {owner} to equip. Click to view details.", bg=SURFACE, fg=DIM,
                 font=(app.UI, 9)).pack(fill="x", pady=(10, 0))
        self.bind("<Escape>", lambda e: self.destroy())
        app.center(self)
        self.wait_window()

    def on_wheel(self, e):
        if self.scroller:
            self.scroller.yview_scroll(int(-e.delta / 120) * 2, "units")

    def pick(self, su, active):
        self.destroy()
        if active:
            self.app.equip_skin(su)
        else:
            SkinDialog(self.app, su, self.app.selected)


class ColorPicker(Sheet):
    """Smooth shade field + hue slider + presets, with a live preview of the whole theme."""
    FW, FH, HB = 320, 200, 14          # field size, hue bar height
    PW = 220                           # preview width
    PRESETS = ["#7b4cff", "#2c1059", "#ff4655", "#ff7a2f", "#f5c451", "#16b877", "#2f8cff",
               "#e0458f", "#00d1c1", "#9696ab"]

    def __init__(self, app, start):
        super().__init__(app)
        import colorsys
        self.cs = colorsys
        self.app, self.result = app, None
        self.title("Pick a colour")
        self.configure(bg=SURFACE)
        r, g, b = (int(start[i:i + 2], 16) / 255 for i in (1, 3, 5))
        self.h, self.s, self.v = colorsys.rgb_to_hsv(r, g, b)
        self._field_cache = {}
        f = tk.Frame(self, bg=SURFACE, padx=26, pady=22)
        f.pack(fill="both")
        head = tk.Frame(f, bg=SURFACE)
        head.pack(fill="x")
        tk.Label(head, text="Theme colour", bg=SURFACE, fg=TEXT, font=(app.UI, 16, "bold"),
                 anchor="w").pack(side="left")
        tk.Label(f, text="The whole app is built from this one colour.", bg=SURFACE, fg=MUTED,
                 font=(app.UI, 9), anchor="w").pack(fill="x", pady=(2, 14))
        W = self.FW + 24 + self.PW
        H = self.FH + 20 + self.HB + 26 + 26
        self.W, self.H = W, H
        self.cv = tk.Canvas(f, width=W, height=H, bg=SURFACE, highlightthickness=0)
        self.cv.pack()
        self.py0 = self.FH + 20                      # hue bar y
        self.ry0 = self.py0 + self.HB + 22           # presets row y
        self.px0 = self.FW + 24                      # preview x
        self._imgs = {}
        self.field_item = self.cv.create_image(0, 0, anchor="nw",
                                               image=self.photo("field", self.field()))
        self.hue_item = self.cv.create_image(0, self.py0, anchor="nw",
                                             image=self.photo("hue", self.hue_bar()))
        self.preview_item = self.cv.create_image(self.px0, 0, anchor="nw",
                                                 image=self.photo("prev", self.preview(start)))
        knob = self.knob(22)
        self.k1 = self.cv.create_image(0, 0, image=self.photo("knob", knob))
        self.k2 = self.cv.create_image(0, 0, image=self.photo("knob2", knob))
        self.preset_items = []
        for i, col in enumerate(self.PRESETS):
            x = 12 + i * 31
            it = self.cv.create_image(x, self.ry0 + 12, image=self.photo(
                "p" + col, self.dot(col, 22)))
            self.cv.tag_bind(it, "<Button-1>", lambda e, c=col: self.set_hex(c))
            self.preset_items.append((col, x))
        self.sel_ring = self.cv.create_image(0, 0, image=self.photo("ring", self.ring(30)))
        self.prev_texts = [
            self.cv.create_text(self.px0 + 18, 24, anchor="w", font=(app.UI, 10, "bold")),
            self.cv.create_text(self.px0 + 18, 44, anchor="w", font=(app.UI, 8)),
            self.cv.create_text(self.px0 + self.PW / 2, 122, font=(app.UI, 10, "bold"),
                                text="Log in", fill="#ffffff"),
            self.cv.create_text(self.px0 + 34, 166, anchor="w", font=(app.UI, 8, "bold"),
                                text="Ranked")]
        row = tk.Frame(f, bg=SURFACE)
        row.pack(fill="x", pady=(14, 0))
        self.hexvar = tk.StringVar(value=start)
        e = app.entry(row, self.hexvar)
        e.config(width=10, font=(app.UI, 11))
        e.pack(side="left", ipady=6)
        e.bind("<Return>", lambda ev: self.from_hex())
        e.bind("<KeyRelease>", lambda ev: self.from_hex(quiet=True))
        tk.Label(row, text="hex", bg=SURFACE, fg=DIM, font=(app.UI, 8)).pack(side="left", padx=8)
        app.button(row, "Use colour", ACCENT, self.ok).pack(side="right")
        app.button(row, "Cancel", CARD, self.destroy).pack(side="right", padx=8)
        self.mode = None
        self.cv.bind("<ButtonPress-1>", self.press)
        self.cv.bind("<B1-Motion>", self.motion)
        self.cv.bind("<ButtonRelease-1>", lambda ev: setattr(self, "mode", None))
        self.bind("<Escape>", lambda ev: self.destroy())
        self.redraw()
        app.center(self)
        self.wait_window()

    # ---- images
    def photo(self, key, im):
        if not HAS_PIL or im is None:
            return ""
        ph = ImageTk.PhotoImage(im)
        self._imgs[key] = ph
        return ph

    def rounded(self, im, r):
        S = 3
        w, h = im.size
        m = Image.new("L", (w * S, h * S), 0)
        ImageDraw.Draw(m).rounded_rectangle((0, 0, w * S - 1, h * S - 1), r * S, fill=255)
        m = m.resize((w, h), Image.LANCZOS)
        out = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        out.paste(im.convert("RGBA"), (0, 0), m)
        return out

    def field(self):
        k = round(self.h * 360)
        if k in self._field_cache:
            return self._field_cache[k]
        hr, hg, hb = (int(c * 255) for c in self.cs.hsv_to_rgb(self.h, 1, 1))
        small = Image.new("RGB", (32, 2))
        small.putdata([tuple(int(255 + (c - 255) * x / 31) for c in (hr, hg, hb))
                       for x in range(32)] * 2)
        horiz = small.resize((self.FW, self.FH), Image.BICUBIC)
        vert = Image.linear_gradient("L").resize((self.FW, self.FH)).point(lambda v: 255 - v)
        im = ImageChops.multiply(horiz, Image.merge("RGB", (vert,) * 3))
        im = self.rounded(im, 14)
        if len(self._field_cache) > 40:
            self._field_cache.clear()
        self._field_cache[k] = im
        return im

    def hue_bar(self):
        if not HAS_PIL:
            return None
        n = 360
        strip = Image.new("RGB", (n, 1))
        strip.putdata([tuple(int(c * 255) for c in self.cs.hsv_to_rgb(i / n, 1, 1))
                       for i in range(n)])
        return self.rounded(strip.resize((self.FW, self.HB), Image.BILINEAR), self.HB // 2)

    def knob(self, d):
        if not HAS_PIL:
            return None
        S = 4
        im = Image.new("RGBA", ((d + 8) * S, (d + 8) * S), (0, 0, 0, 0))
        dr = ImageDraw.Draw(im)
        dr.ellipse((3 * S, 5 * S, (d + 5) * S, (d + 7) * S), fill=(0, 0, 0, 90))
        im = im.filter(ImageFilter.GaussianBlur(S * 1.5))
        dr = ImageDraw.Draw(im)
        dr.ellipse((4 * S, 4 * S, (d + 4) * S, (d + 4) * S), outline=(255, 255, 255, 255),
                   width=int(3.2 * S))
        return im.resize((d + 8, d + 8), Image.LANCZOS)

    def dot(self, col, d):
        if not HAS_PIL:
            return None
        S = 4
        im = Image.new("RGBA", (d * S, d * S), (0, 0, 0, 0))
        ImageDraw.Draw(im).ellipse((0, 0, d * S - 1, d * S - 1), fill=col)
        return im.resize((d, d), Image.LANCZOS)

    def ring(self, d):
        if not HAS_PIL:
            return None
        S = 4
        im = Image.new("RGBA", (d * S, d * S), (0, 0, 0, 0))
        ImageDraw.Draw(im).ellipse((S, S, d * S - S, d * S - S), outline=(255, 255, 255, 230),
                                   width=2 * S)
        return im.resize((d, d), Image.LANCZOS)

    def preview(self, col):
        """Mini version of the app in the picked colour."""
        acc, acc_hi, soft, glow, brand = custom_palette(col)
        base = "#0d0c12"
        surface = mix(base, brand, 0.35)
        card = mix("#16151d", brand, 0.45)
        w, h = self.PW, self.FH
        im = Image.new("RGB", (w, h), _rgb(surface))
        d = ImageDraw.Draw(im)
        S = 3
        big = Image.new("RGBA", (w * S, h * S), (0, 0, 0, 0))
        bd = ImageDraw.Draw(big)
        bd.rounded_rectangle((18 * S, 98 * S, (w - 18) * S, 146 * S), 24 * S, fill=acc)
        bd.rounded_rectangle((18 * S, 156 * S, 96 * S, 176 * S), 10 * S, fill=card)
        bd.rounded_rectangle((106 * S, 163 * S, (w - 18) * S, 169 * S), 3 * S, fill=card)
        bd.rounded_rectangle((106 * S, 163 * S, 160 * S, 169 * S), 3 * S, fill=acc)
        bd.rounded_rectangle((18 * S, 62 * S, (w - 18) * S, 86 * S), 8 * S, fill=card)
        bd.rounded_rectangle((26 * S, 70 * S, 70 * S, 78 * S), 4 * S, fill=soft)
        big = big.resize((w, h), Image.LANCZOS)
        im.paste(big, (0, 0), big)
        return self.rounded(im, 16)

    # ---- state
    def hex(self):
        r, g, b = self.cs.hsv_to_rgb(self.h, self.s, self.v)
        return "#%02x%02x%02x" % (round(r * 255), round(g * 255), round(b * 255))

    def redraw(self):
        col = self.hex()
        if HAS_PIL:
            self.cv.itemconfigure(self.field_item, image=self.photo("field", self.field()))
            self.cv.itemconfigure(self.preview_item, image=self.photo("prev", self.preview(col)))
        self.cv.coords(self.k1, self.s * self.FW, (1 - self.v) * self.FH)
        self.cv.coords(self.k2, self.h * self.FW, self.py0 + self.HB / 2)
        acc, acc_hi, soft, glow, brand = custom_palette(col)
        self.cv.itemconfigure(self.prev_texts[0], text="Preview", fill="#f2effa")
        self.cv.itemconfigure(self.prev_texts[1], text=col.upper(), fill=soft)
        self.cv.itemconfigure(self.prev_texts[3], fill=soft)
        sel = next((x for c, x in self.preset_items if c.lower() == col.lower()), None)
        if sel is None:
            self.cv.itemconfigure(self.sel_ring, state="hidden")
        else:
            self.cv.itemconfigure(self.sel_ring, state="normal")
            self.cv.coords(self.sel_ring, sel, self.ry0 + 12)

    def press(self, e):
        if 0 <= e.x <= self.FW and 0 <= e.y <= self.FH:
            self.mode = "field"
        elif 0 <= e.x <= self.FW and self.py0 - 8 <= e.y <= self.py0 + self.HB + 8:
            self.mode = "hue"
        else:
            self.mode = None
            return
        self.cv.focus_set()
        self.motion(e)

    def motion(self, e):
        if self.mode == "field":
            self.s = min(1, max(0, e.x / self.FW))
            self.v = min(1, max(0, 1 - e.y / self.FH))
        elif self.mode == "hue":
            self.h = min(0.9999, max(0, e.x / self.FW))
        else:
            return
        self.hexvar.set(self.hex())
        self.redraw()

    def set_hex(self, col):
        self.hexvar.set(col)
        self.from_hex()

    def from_hex(self, quiet=False):
        v = self.hexvar.get().strip()
        if not v.startswith("#"):
            v = "#" + v
        if re.fullmatch(r"#[0-9a-fA-F]{6}", v):
            r, g, b = (int(v[i:i + 2], 16) / 255 for i in (1, 3, 5))
            self.h, self.s, self.v = self.cs.rgb_to_hsv(r, g, b)
            self.redraw()

    def ok(self):
        self.from_hex()
        self.result = self.hex()
        self.destroy()


class HealthDialog(Sheet):
    def __init__(self, app, results):
        super().__init__(app)
        self.title("Health check")
        self.configure(bg=SURFACE)
        self.resizable(False, False)
        self.transient(app)
        f = tk.Frame(self, bg=SURFACE, padx=24, pady=20)
        f.pack(fill="both")
        good = sum(1 for r in results if r[0])
        bad = sum(1 for r in results if r[0] is False)
        tk.Label(f, text="Health check", bg=SURFACE, fg=TEXT, font=(app.UI, 14, "bold"),
                 anchor="w").pack(fill="x")
        tk.Label(f, text=f"{good} working · {bad} problem{'s' if bad != 1 else ''}", bg=SURFACE,
                 fg=DANGER if bad else GOOD, font=(app.UI, 10, "bold"), anchor="w").pack(
            fill="x", pady=(2, 12))
        for ok, label, detail in results:
            row = tk.Frame(f, bg=CARD, padx=12, pady=7)
            row.pack(fill="x", pady=2)
            mark, col = ("✓", GOOD) if ok else (("✕", DANGER) if ok is False else ("•", GOLD))
            tk.Label(row, text=mark, bg=CARD, fg=col, font=(app.UI, 11, "bold"), width=2).pack(
                side="left")
            tk.Label(row, text=label, bg=CARD, fg=TEXT, font=(app.UI, 9, "bold"),
                     anchor="w").pack(side="left")
            if detail:
                tk.Label(row, text=detail, bg=CARD, fg=MUTED, font=(app.UI, 8), anchor="e",
                         wraplength=300, justify="right").pack(side="right", padx=(16, 0))
        bar = tk.Frame(f, bg=SURFACE)
        bar.pack(fill="x", pady=(14, 0))
        app.button(bar, "Close", ACCENT, self.destroy).pack(side="right")
        self.bind("<Escape>", lambda e: self.destroy())
        app.center(self)
        self.wait_window()


WEAPON_ORDER = ["Vandal", "Phantom", "Operator", "Sheriff", "Melee", "Classic", "Ghost",
                "Spectre", "Marshal", "Outlaw", "Guardian", "Bulldog", "Judge", "Bucky",
                "Stinger", "Frenzy", "Shorty", "Bandit", "Ares", "Odin"]


class PlayerLayer(Layer, ScrollBody):
    """One player from your lobby: agent, rank, level and their whole skin loadout (with
    chromas and buddies). Hidden names stay hidden; click a skin for its preview."""
    W, H = 860, 660
    CW, CH = 150, 104

    def __init__(self, app, p, name):
        self.p, self.name = p, name
        lo = p.get("loadout") or {}
        if not lo and p.get("skins"):
            lo = {k: {"skin": v} for k, v in p["skins"].items()}
        rank = {n: i for i, n in enumerate(WEAPON_ORDER)}
        rows = []
        for wid, e in lo.items():
            sk = ASSETS.skins.get(e.get("skin") or "")
            wname = (ASSETS.weapons.get(wid) or {}).get("name") or (sk or {}).get("weapon", "")
            rows.append((rank.get(wname, 99), wname, wid, e, sk))
        rows.sort(key=lambda r: (r[0], r[1]))
        self.rows = rows
        super().__init__(app)

    def draw(self, x0, y0, x1, y1):
        app, p = self.app, self.p
        top, bot = y0 + 150, y1 - 44
        self.glide_scroll()
        self.draw_grid(x0 + 26, top, x1 - 26, bot)
        self.mask(x0, y0, x1, y1, top, bot)
        ag = ASSETS.agents.get(p.get("agent") or "", {})
        card = ASSETS.cards.get(p.get("card") or "", {})
        ban = (x0 + 8, y0 + 8, x1 - 8, y0 + 116)
        if not app.image(card.get("wide"), ban[0], ban[1], ban[2] - ban[0], ban[3] - ban[1],
                         mode="cover", radius=14, fade=True):
            app.rrect(*ban, 14, fill=mix(SURFACE, ACCENT, 0.15), depth=0)
        A = 74
        ax, ay = x0 + 30, y0 + 58
        app.rrect(ax - 5, ay - 5, ax + A + 5, ay + A + 5, 20, fill=SURFACE, depth=0)
        if not app.image(ag.get("icon"), ax, ay, A, A, radius=16):
            app.letter_avatar(ax, ay, A, self.name or "?", radius=16)
        nx = ax + A + 18
        app.text(nx, y0 + 108, self.name, 16, "bold", TEXT if p.get("name") else MUTED,
                 maxw=x1 - nx - 300)
        bits = [ag.get("name") or "No agent yet"]
        if p.get("level"):
            bits.append(f"Level {p['level']}")
        title = ASSETS.titles.get(p.get("title") or "")
        if title:
            bits.append(f"“{title}”")
        if p.get("me"):
            bits.append("You")
        elif p.get("party"):
            bits.append("Your party")
        elif p.get("ally") is False:
            bits.append("Enemy team")
        app.text(nx, y0 + 132, "  ·  ".join(bits), 9, fill=MUTED, maxw=x1 - nx - 300)
        hide = app.settings.get("focus_mode") and not p.get("me")
        bx = x1 - 30
        for t, label, rr in ((p.get("peak", 0), "Peak", None), (p.get("tier", 0), "Current",
                                                                   p.get("rr"))):
            w = 176
            app.rrect(bx - w, y0 + 100, bx, y0 + 142, 12, fill=mix(SURFACE, CARD, 0.5),
                      outline=LINE)
            if t >= 3 and not hide:
                app.rank_icon(t, bx - w + 22, y0 + 121, 26)
            app.text(bx - w + 42, y0 + 112, label, 7, "bold", DIM)
            nm = "Hidden" if hide else ASSETS.tier_name(t)
            if rr is not None and t >= 3 and not hide:
                nm += f" · {rr} RR"
            app.text(bx - w + 42, y0 + 129, nm, 9, "bold",
                     mix(ASSETS.tier_color(t) or MUTED, "#ffffff", 0.35) if not hide else DIM,
                     maxw=w - 50)
            bx -= w + 10
        fancy = sum(1 for r in self.rows if r[4] and not r[4].get("standard"))
        val = sum(ASSETS.skin_price(r[4]["uuid"]) or 0 for r in self.rows if r[4])
        app.text(x0 + 26, y1 - 22, f"{fancy} skinned weapons" + (f"  ·  about {val:,} VP equipped"
                                                                  if val else "")
                 + "  ·  click a skin for its preview", 8, fill=DIM)
        self.close_btn(x1 - 34, y0 + 34)

    def draw_grid(self, x0, top, x1, bot):
        app = self.app
        y = top + 12 - self.scroll
        if not self.rows:
            app.text((x0 + x1) / 2, top + 60, "Skins show up once the match has loaded their "
                     "loadout.", 10, fill=MUTED, anchor="center")
            self.max_scroll = 0
            return
        cols = max(1, int((x1 - x0 + 10) // (self.CW + 10)))
        cw = (x1 - x0 - 10 * (cols - 1)) / cols
        for i, (_, wname, wid, e, sk) in enumerate(self.rows):
            cx = x0 + (i % cols) * (cw + 10)
            cy = y + (i // cols) * (self.CH + 10)
            if not self.vis(cy, cy + self.CH, top, bot):
                continue
            std = not sk or sk.get("standard")
            key = self.k(f"sk:{i}")
            f = app.hv(key) if not std else 0
            self.row_box(key, cx, cy, cx + cw, cy + self.CH, top, bot,
                         (lambda su=sk["uuid"]: SkinDialog(app, su)) if not std else None,
                         tip=None if std else "Preview")
            tcol = ASSETS.ctiers.get((sk or {}).get("tier") or "", {}).get("color") if sk else None
            app.rrect(cx, cy, cx + cw, cy + self.CH, 12,
                      fill=mix(mix(SURFACE, CARD, 0.45), CARD_HI, 0.6 * f),
                      outline=mix(LINE, tcol or SOFT, 0.3 + 0.4 * f) if not std else LINE)
            url = None
            if sk:
                url = sk["icon"]
                ch = next((c for c in sk.get("chromas") or [] if c["uuid"] == e.get("chroma")),
                          None)
                if ch and sk["chromas"] and ch is not sk["chromas"][0] and ch.get("render"):
                    url = ch["render"]
            app.image(url, cx + cw / 2, cy + 38, cw - 24, 44, anchor="center")
            nm = sk["name"] if sk and not std else f"Standard {wname}"
            app.text(cx + cw / 2, cy + self.CH - 22, nm, 8, "bold", TEXT if not std else DIM,
                     anchor="center", maxw=cw - 16)
            if tcol and not std:
                app.rrect(cx + 14, cy + self.CH - 4, cx + cw - 14, cy + self.CH - 2, 1,
                          fill=tcol, depth=0)
            bud = ASSETS.buddy_levels.get(e.get("buddy") or "")
            if bud:
                app.image(bud.get("icon"), cx + cw - 30, cy + 6, 24, 24)
        n = len(self.rows)
        y += ((n - 1) // cols + 1) * (self.CH + 10)
        self.max_scroll = max(0.0, (y + self.scroll) - bot + 6)
        self.scroll_t = min(self.scroll_t, self.max_scroll)


OBS_PAGE = """<!doctype html><html><head><meta charset="utf-8"><style>
body{margin:0;background:transparent;font-family:'Segoe UI',sans-serif;color:#fff}
.card{display:inline-flex;align-items:center;gap:16px;padding:14px 22px 14px 14px;
border-radius:18px;background:rgba(10,8,18,.78);border:2px solid var(--c,#7b4cff)}
img{width:64px;height:64px}.rank{font-size:26px;font-weight:700}
.sub{font-size:15px;opacity:.8}.up{color:#3ddc97}.down{color:#ff5c7a}
</style></head><body><div class="card" id="c"><img id="i"><div>
<div class="rank" id="r">...</div><div class="sub" id="s"></div></div></div>
<script>
async function tick(){try{const d=await (await fetch('/data')).json();
document.getElementById('c').style.setProperty('--c',d.color);
const i=document.getElementById('i');if(d.icon){i.src=d.icon;i.style.display=''}else{i.style.display='none'}
document.getElementById('r').textContent=d.rank+(d.rank!=='Unranked'?' · '+d.rr+' RR':'');
const t=d.today_rr;const cls=t>0?'up':(t<0?'down':'');
document.getElementById('s').innerHTML=(d.name?d.name+' · ':'')+'Today '+d.w+'W '+d.l+'L '+
'<span class="'+cls+'">'+(t>0?'+':'')+t+' RR</span>';}catch(e){}}
tick();setInterval(tick,5000);
</script></body></html>"""


class MiniWindow(tk.Toplevel):
    """Small always-on-top switcher + live lobby overlay."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", 0.94)
        except Exception:
            pass
        self.configure(bg=LINE)
        self.body = tk.Frame(self, bg=SURFACE, padx=10, pady=8)
        self.body.pack(fill="both", expand=True, padx=1, pady=1)
        self.geometry(app.state_.get("mini_pos") or "+40+40")
        self._drag = None
        self.bind("<ButtonPress-3>", lambda e: self.app.toggle_mini())
        self.render()

    def start_drag(self, e):
        self._drag = (e.x_root - self.winfo_x(), e.y_root - self.winfo_y())

    def drag(self, e):
        if self._drag:
            self.geometry(f"+{e.x_root - self._drag[0]}+{e.y_root - self._drag[1]}")

    def end_drag(self, e):
        self._drag = None
        self.app.state_["mini_pos"] = f"+{self.winfo_x()}+{self.winfo_y()}"
        save_state(self.app.state_)

    def render(self):
        if not self.winfo_exists():
            return
        app = self.app
        for w in self.body.winfo_children():
            w.destroy()
        head = tk.Frame(self.body, bg=SURFACE, cursor="fleur")
        head.pack(fill="x")
        grip = tk.Label(head, text="⠿  RiotHub", bg=SURFACE, fg=DIM,
                        font=(app.UI, 8, "bold"))
        grip.pack(side="left")
        x = tk.Label(head, text="✕", bg=SURFACE, fg=DIM, cursor="hand2", font=(app.UI, 9, "bold"))
        x.pack(side="right")
        x.bind("<Button-1>", lambda e: app.toggle_mini())
        for wdg in (head, grip):
            wdg.bind("<ButtonPress-1>", self.start_drag)
            wdg.bind("<B1-Motion>", self.drag)
            wdg.bind("<ButtonRelease-1>", self.end_drag)
        active = app.state_.get("active")
        for i, n in enumerate(app.accounts()[:9]):
            m = app.m(n)
            if m.get("archived"):
                continue
            on = n == active
            row = tk.Frame(self.body, bg=ACCENT if on else CARD, padx=8, pady=4, cursor="hand2")
            row.pack(fill="x", pady=2)
            a = tk.Label(row, text=f"{i + 1}  {n}", bg=row["bg"], fg=TEXT,
                         font=(app.UI, 9, "bold"), anchor="w")
            a.pack(side="left")
            b = tk.Label(row, text=ASSETS.tier_name(m.get("tier")) if m.get("tier") else "",
                         bg=row["bg"], fg=TEXT if on else MUTED, font=(app.UI, 8))
            b.pack(side="right", padx=(12, 0))
            for wdg in (row, a, b):
                wdg.bind("<Button-1>", lambda e, n=n: app.switch(n))
        live = app.live or {}
        if live.get("party_id") and live.get("phase") == "none":
            self.party(live)
        if live.get("phase") in ("pregame", "ingame"):
            tk.Frame(self.body, bg=LINE, height=1).pack(fill="x", pady=6)
            for p in live.get("players") or []:
                ag = ASSETS.agents.get(p["agent"], {}).get("name", "?")
                nm = p["name"].split("#")[0] if p["name"] and not app.streamer() else ag
                r = tk.Frame(self.body, bg=SURFACE)
                r.pack(fill="x")
                tk.Label(r, text="●", bg=SURFACE, fg=GOOD if p["ally"] else DANGER,
                         font=(app.UI, 7)).pack(side="left")
                tk.Label(r, text=f" {nm}", bg=SURFACE, fg=TEXT, font=(app.UI, 8, "bold"),
                         anchor="w").pack(side="left")
                if not app.settings.get("focus_mode") or p["me"]:
                    tk.Label(r, text=ASSETS.tier_name(p["tier"]), bg=SURFACE, fg=MUTED,
                             font=(app.UI, 8)).pack(side="right", padx=(12, 0))
        tk.Label(self.body, text="Drag the top bar · right-click to close", bg=SURFACE, fg=DIM,
                 font=(app.UI, 7)).pack(fill="x", pady=(4, 0))
        self.after(1000 if app.queueing() else 3000, self.render)

    def party(self, live):
        """Who's in your party, plus queue and open/closed - same as the Live page."""
        app = self.app
        tk.Frame(self.body, bg=LINE, height=1).pack(fill="x", pady=6)
        q = live.get("queue") or ""
        n = len(live.get("party") or [])
        head = tk.Frame(self.body, bg=SURFACE)
        head.pack(fill="x")
        tk.Label(head, text=QUEUES.get(q, q.title() or "Custom"), bg=SURFACE, fg=TEXT,
                 font=(app.UI, 9, "bold")).pack(side="left")
        tk.Label(head, text=f"party of {n}" if n > 1 else "solo", bg=SURFACE, fg=MUTED,
                 font=(app.UI, 8)).pack(side="left", padx=6)
        for p in live.get("players") or []:
            nm = (p.get("name") or "").split("#")[0] if not app.streamer() else ""
            nm = "You" if p.get("me") else (nm or "Party member")
            r = tk.Frame(self.body, bg=SURFACE)
            r.pack(fill="x")
            own = p.get("puuid") == live.get("party_owner")
            tk.Label(r, text="★" if own else "●", bg=SURFACE, fg=GOLD if own else GOOD,
                     font=(app.UI, 7)).pack(side="left")
            tk.Label(r, text=f" {nm}", bg=SURFACE, fg=TEXT, font=(app.UI, 8, "bold"),
                     anchor="w").pack(side="left")
            if not app.settings.get("focus_mode") or p.get("me"):
                tk.Label(r, text=ASSETS.tier_name(p.get("tier")) if p.get("tier") else "",
                         bg=SURFACE, fg=MUTED, font=(app.UI, 8)).pack(side="right", padx=(12, 0))
        bar = tk.Frame(self.body, bg=SURFACE)
        bar.pack(fill="x", pady=(6, 0))
        if app.queueing():
            e = int(queue_elapsed(live))
            b = app.button(bar, f"Stop queue  {e // 60}:{e % 60:02d}", CARD_HI,
                           lambda: app.party_do("leave"))
        else:
            b = app.button(bar, "Start queue", ACCENT, lambda: app.party_do("join"))
        b.config(font=(app.UI, 8, "bold"), padx=10, pady=4)
        b.pack(side="left")
        op = bool(live.get("party_open"))
        o = app.button(bar, "Open" if op else "Closed", CARD,
                       lambda: app.party_do("access", not op))
        o.config(font=(app.UI, 8, "bold"), padx=10, pady=4)
        o.pack(side="left", padx=(6, 0))


def _user32():
    try:
        return ctypes.windll.user32
    except Exception:
        return None


class FloatWin(tk.Toplevel):
    """Borderless, always-on-top, draggable little window (the mini agent picker)."""

    def __init__(self, app, pos_key, default_pos, alpha=0.97, drag=True):
        super().__init__(app)
        self.app, self.pos_key = app, pos_key
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", alpha)
        except Exception:
            pass
        self.configure(bg=LINE)
        self.body = tk.Frame(self, bg=SURFACE, padx=12, pady=10)
        self.body.pack(fill="both", expand=True, padx=1, pady=1)
        self.geometry(app.state_.get(pos_key) or default_pos)
        self._drag = None
        self.imgs = []
        if app.images:
            app.images.listeners.add(self.refresh_imgs)
        self.after(50, self._no_activate)

    CLICK_THROUGH = False

    def _no_activate(self):
        """Clicking this window must not pull focus away from the game."""
        u = _user32()
        if not u:
            return
        try:
            hwnd = u.GetParent(self.winfo_id()) or self.winfo_id()
            ex = u.GetWindowLongW(hwnd, -20)
            ex |= 0x08000000 | 0x80 | 0x8          # NOACTIVATE | TOOLWINDOW | TOPMOST
            if self.CLICK_THROUGH:
                ex |= 0x20 | 0x80000              # TRANSPARENT | LAYERED
            u.SetWindowLongW(hwnd, -20, ex)
        except Exception:
            pass

    def draggable(self, *widgets):
        for w in widgets:
            w.bind("<ButtonPress-1>", self._start)
            w.bind("<B1-Motion>", self._move)
            w.bind("<ButtonRelease-1>", self._end)

    def _start(self, e):
        self._drag = (e.x_root - self.winfo_x(), e.y_root - self.winfo_y())

    def _move(self, e):
        if self._drag:
            self.geometry(f"+{e.x_root - self._drag[0]}+{e.y_root - self._drag[1]}")

    def _end(self, e):
        self._drag = None
        self.app.state_[self.pos_key] = f"+{self.winfo_x()}+{self.winfo_y()}"
        save_state(self.app.state_)

    def want(self, label, url, w, h, **kw):
        self.imgs.append((label, url, w, h, kw))

    def refresh_imgs(self):
        if not self.app.images:
            return
        for label, url, w, h, kw in self.imgs:
            if not url:
                continue
            try:
                if not label.winfo_exists():
                    continue
                im = self.app.images.get(url, w, h, **kw)
                if im and getattr(label, "image", None) is not im:
                    label.config(image=im, width=w, height=h)
                    label.image = im
            except tk.TclError:
                pass

    def clear(self):
        for w in self.body.winfo_children():
            w.destroy()
        self.imgs = []

    def destroy(self):
        if self.app.images:
            self.app.images.listeners.discard(self.refresh_imgs)
        try:
            super().destroy()
        except tk.TclError:
            pass


class AgentPicker(FloatWin):
    """Tiny always-on-top agent select: favourites up top, everything else below.
    One click = pick (and lock, if instant lock is on). Right-click = favourite."""
    BIG, SMALL = 54, 34

    def __init__(self, app):
        super().__init__(app, "picker_pos", "+60+120")
        self.locked_at = None
        self.render()

    def render(self):
        try:
            if not self.winfo_exists():
                return
        except tk.TclError:
            return
        app = self.app
        d = app.live or {}
        self.clear()
        st = app.settings
        head = tk.Frame(self.body, bg=SURFACE, cursor="fleur")
        head.pack(fill="x")
        mp = ASSETS.maps.get(d.get("map") or "", {}).get("name") or "Agent select"
        t = tk.Label(head, text=f"⠿  {mp}", bg=SURFACE, fg=TEXT, font=(app.UI, 10, "bold"))
        t.pack(side="left")
        if d.get("timer") and not d.get("my_locked"):
            left = max(0, d["timer"] - (time.time() - d.get("timer_t", time.time())))
            tk.Label(head, text=f"{int(left)}s", bg=SURFACE, fg=DANGER if left < 10 else SOFT,
                     font=(app.UI, 10, "bold")).pack(side="left", padx=8)
        x = tk.Label(head, text="✕", bg=SURFACE, fg=DIM, cursor="hand2", font=(app.UI, 10, "bold"))
        x.pack(side="right")
        x.bind("<Button-1>", lambda e: app.close_picker())
        big = tk.Label(head, text="Open app", bg=SURFACE, fg=DIM, cursor="hand2",
                       font=(app.UI, 8, "bold"))
        big.pack(side="right", padx=8)
        big.bind("<Button-1>", lambda e: (app.close_picker(), app.show_window(),
                                          app.set_page("live")))
        self.draggable(head, t)
        if d.get("phase") != "pregame":
            tk.Label(self.body, text="Waiting for agent select…", bg=SURFACE, fg=MUTED,
                     font=(app.UI, 9)).pack(fill="x", pady=10)
            return
        if d.get("my_locked"):
            ag = ASSETS.agents.get(d.get("my_agent") or "", {})
            row = tk.Frame(self.body, bg=SURFACE)
            row.pack(fill="x", pady=(10, 2))
            il = tk.Label(row, bg=SURFACE)
            il.pack(side="left")
            self.want(il, ag.get("icon"), 40, 40, radius=10)
            tk.Label(row, text=f"  Locked in as {ag.get('name', '?')}", bg=SURFACE, fg=GOOD,
                     font=(app.UI, 11, "bold")).pack(side="left")
            self.refresh_imgs()
            if not self.locked_at:
                self.locked_at = time.time()
                self.after(2500, app.close_picker)
            return
        if not st.get("agent_grid_ok"):
            w = tk.Frame(self.body, bg=mix(SURFACE, GOLD, 0.12), padx=10, pady=8)
            w.pack(fill="x", pady=(8, 0))
            tk.Label(w, text="Picking agents from outside the game is what Riot shut Recon Bolt "
                     "down for. It's manual here, but it could still get flagged.",
                     bg=w["bg"], fg=TEXT, font=(app.UI, 8), wraplength=300,
                     justify="left").pack(fill="x")
            ok = app.button(w, "Use it anyway", ACCENT, self.accept)
            ok.config(font=(app.UI, 8, "bold"), padx=10, pady=4)
            ok.pack(anchor="e", pady=(6, 0))
            return
        cur = d.get("my_agent")
        m = app.m(app.state_.get("active"))
        owned = {o.lower() for o in owned_ids(m, "agents")}
        taken = {p["agent"] for p in d.get("players") or [] if p.get("locked") and not p["me"]
                 and p.get("ally")}
        favs = [a for a in st.get("fav_agents") or [] if a in ASSETS.agents]
        inst = st.get("instant_lock", True)

        def tile(parent, aid, size, r, c):
            info = ASSETS.agents.get(aid, {})
            have = info.get("base") or aid in owned or not owned
            gone = aid in taken
            ring = ACCENT if aid == cur else SURFACE
            fr = tk.Frame(parent, bg=ring, padx=2, pady=2)
            fr.grid(row=r, column=c, padx=2, pady=2)
            lab = tk.Label(fr, bg=CARD, width=size // 8, height=size // 16,
                           cursor="hand2" if have and not gone else "")
            lab.pack()
            self.want(lab, info.get("icon"), size, size, radius=size // 5,
                      gray=not have or gone)
            if have and not gone:
                lab.bind("<Button-1>", lambda e: app.picker_pick(aid, inst))
                lab.bind("<Double-Button-1>", lambda e: app.picker_pick(aid, True))
                lab.bind("<Enter>", lambda e: (fr.config(bg=SOFT if aid != cur else ACCENT),
                                               self.hint.config(text=info.get("name", ""))))
                lab.bind("<Leave>", lambda e: (fr.config(bg=ring),
                                               self.hint.config(text=self.HINT)))
            lab.bind("<Button-3>", lambda e: app.toggle_fav_agent(aid))

        self.HINT = ("Click to lock in" if inst else "Click to pick · double-click to lock") \
            + " · right-click to favourite"
        if favs:
            tk.Label(self.body, text="★  Favourites", bg=SURFACE, fg=GOLD,
                     font=(app.UI, 8, "bold"), anchor="w").pack(fill="x", pady=(8, 2))
            fg = tk.Frame(self.body, bg=SURFACE)
            fg.pack(fill="x")
            for i, aid in enumerate(favs[:12]):
                tile(fg, aid, self.BIG, i // 6, i % 6)
        rest = sorted((a for a in ASSETS.agents if a not in favs),
                      key=lambda a: ASSETS.agents[a]["name"])
        tk.Label(self.body, text="All agents" if favs else "All agents  ·  right-click to favourite",
                 bg=SURFACE, fg=DIM, font=(app.UI, 8, "bold"), anchor="w").pack(fill="x",
                                                                                pady=(8, 2))
        ag = tk.Frame(self.body, bg=SURFACE)
        ag.pack(fill="x")
        for i, aid in enumerate(rest):
            tile(ag, aid, self.SMALL, i // 9, i % 9)
        foot = tk.Frame(self.body, bg=SURFACE)
        foot.pack(fill="x", pady=(8, 0))
        self.hint = tk.Label(foot, text=self.HINT, bg=SURFACE, fg=DIM, font=(app.UI, 7),
                             anchor="w")
        self.hint.pack(side="left")
        tg = tk.Label(foot, text=("☑" if inst else "☐") + " Instant lock", bg=SURFACE,
                      fg=SOFT if inst else DIM, cursor="hand2", font=(app.UI, 8, "bold"))
        tg.pack(side="right")
        tg.bind("<Button-1>", lambda e: (app.toggle("instant_lock"), self.render()))
        if cur and not inst:
            lk = app.button(self.body, f"Lock {ASSETS.agents.get(cur, {}).get('name', '')}",
                            ACCENT, lambda: app.picker_pick(cur, True))
            lk.pack(fill="x", pady=(8, 0))
        self.refresh_imgs()

    def accept(self):
        self.app.settings["agent_grid_ok"] = True
        save_state(self.app.state_)
        self.render()


# ================================================================ app
class App(tk.Tk):
    SIDE, BOTTOM, RIGHT, TILE = 76, 88, 300, 150
    PAGES = [("play", "play", "Play"), ("home", "home", "Accounts"), ("profile", "person", "Profile"),
             ("live", "game", "Live match"), ("store", "shop", "Store & wishlist"),
             ("compare", "compare", "Compare accounts"), ("sync", "copy", "Sync & crosshairs"),
             ("social", "chat", "Friends, leaderboard & servers")]

    def __init__(self, start_hidden=False):
        super().__init__()
        fams = set(tkfont.families(self))
        self.UI = next((f for f in ("Segoe UI Variable Display", "Segoe UI", "Helvetica")
                        if f in fams), "TkDefaultFont")
        self.ICON = next((f for f in ("Segoe Fluent Icons", "Segoe MDL2 Assets") if f in fams),
                         None)
        self._fonts = {}
        self.title(APP_TITLE)
        self.minsize(900, 620)

        self.q = queue.Queue()
        self.state_ = load_state()
        self.geometry(self.state_.get("geometry") or "1280x800")
        self.settings = self.state_["settings"]
        if self.settings.get("custom_color"):
            THEMES["Custom"] = custom_palette(self.settings["custom_color"])
        apply_theme(self.settings.get("theme", "Violet"))
        self.configure(bg=BG)
        self.meta = {n: load_meta(n) for n in self.accounts()}
        self.selected = self.state_.get("active")
        self.busy = False
        self.fetching = set()
        self.status = ""
        self.status_until = 0
        self.hover = None
        self._tw = {}
        self.hits = {}
        self.hit_boxes = []
        self.page = self.settings.get("start_page", "play") if self.settings.get("start_page", "play") in ("play", "home") else "home"
        self.launching = {}
        self.client_warming = False
        self.running_games = set()
        self.ptab = "overview"
        self.inv_tab = "skins"
        self.weapon = "All"
        self.expanded = None
        self.compare_sort = ("rank", True)
        self.sync_source = None
        self.sync_cats = {"crosshair"}
        self.scrolls = {}
        self.scroll_t = {}
        self.max_scroll = 0
        self._pending = False
        self._spin = 0
        self.press = None
        self.dragging = None
        self.drag_pos = (0, 0)
        self.tile_slots = []
        self.watch_id = 0
        self.toasts = []
        self.progress = None
        self.search_shown = False
        self.live = None
        self.live_error = None
        self.live_busy = False
        self.rank_cache = {}
        self._vc = None
        self.enc = {}
        self.inv_sort = "weapon"
        self.show_history = set()
        self.tag_filter = ""
        self.show_archived = False
        self.friends = None
        self.friends_err = None
        self.status_items = None
        self.soc_tab = "friends"
        self.store_acc = None
        self.scan = None
        self.lb = {"region": None, "page": 1, "rows": None, "err": None, "total": 0,
                   "busy": False, "need_key": False}
        self.srv = {"region": None, "data": {}, "busy": False, "t": 0}
        self.duos = None
        self.mini = None
        self.picker = None
        self.locked = bool(self.settings.get("pin"))
        self.obs = None
        self.errors = []
        self.bg_photo = None
        self.league_busy = False
        self._obs_snapshot = {}
        self.session = None
        self.flips = {}
        self._bg_cache = None
        from collections import OrderedDict
        self._shapes = OrderedDict()
        self.page_t = 0
        self.kbd_focus = False
        self.mouse = (0, 0)
        self.tab_t = 0
        self.page_dir = 1
        self._tab_mark = None
        self._bar_i = 0
        self.glow_cur = GLOW
        self._more = self._shimmer = False
        self._ovl_more = self._ovl_loop = False
        self.sheets, self._bd, self._sheet_loop = [], None, False
        self.layers = []
        self._bd_frames, self._bd_raw, self._bd_final = {}, None, None
        self._routed, self._appkeys = set(), {}
        self.pop = None
        self.tray = None
        self.hotkeys = None
        self.images = Images(self) if HAS_PIL else None
        self.app_ico = None
        self.proxy = StatusProxy(lambda k, i: self.call_ui(lambda: self.on_proxy(k, i)))
        self.proxy.mode = self.settings.get("status_mode", "online")
        self.proxy.control = bool(self.settings.get("chat_control", True))
        self.proxy_state = "idle"

        self.cv = tk.Canvas(self, bg=BG, highlightthickness=0)
        self.cv.pack(fill="both", expand=True)
        self.cv.bind("<Configure>", lambda e: (self.redraw(), self._sheets_relayout()))
        self.cv.bind("<Motion>", self.on_motion)
        self.cv.bind("<Leave>", lambda e: (setattr(self, "mouse", (None, None)),
                                           self.set_hover(None)))
        self.cv.bind("<ButtonPress-1>", self.on_press)
        self.cv.bind("<B1-Motion>", self.on_drag)
        self.cv.bind("<ButtonRelease-1>", self.on_release)
        self.cv.bind("<Double-Button-1>", lambda e: self.fire("dbl", e))
        self.cv.bind("<Button-3>", lambda e: self.fire("right", e))
        self.bind_all("<MouseWheel>", self.on_wheel)
        self.bind_all("<Control-Shift-F>", lambda e: self.toggle_perf_hud())
        self.bind_all("<Control-Shift-f>", lambda e: self.toggle_perf_hud())
        self.key("<Control-f>", lambda e: self.focus_search())
        for k, d in (("<Left>", -1), ("<Right>", 1), ("<Up>", -4), ("<Down>", 4)):
            self.key(k, lambda e, d=d: self.nav(d))
        self.key("<Return>", lambda e: self.nav_enter())
        self.key("<Escape>", lambda e: self.cv.focus_set())
        for i, (p, _, _) in enumerate(self.PAGES):
            self.key(f"<Control-Key-{i + 1}>", lambda e, p=p: self.set_page(p))

        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self.redraw())
        self.search = self.entry(self.cv, self.search_var, plain=True)

        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.report_callback_exception = self._on_tk_error
        dark_titlebar(self)
        self.make_icons()
        self._poll()
        self.start_ipc()
        self.start_tray()
        self.apply_hotkeys()
        if self.settings.get("start_with_windows"):
            try:
                set_autostart(True)
            except Exception:
                pass
        threading.Thread(target=self._load_assets, daemon=True).start()
        threading.Thread(target=self._playtime_loop, daemon=True).start()
        threading.Thread(target=self._league_loop, daemon=True).start()
        self.after(45_000, self._bg_tick)
        self.after(15_000, self._live_tick)
        self.after(1500, self._games_tick)
        self.after(2500, self.warm_client)
        self.after(1200, self.maybe_welcome)
        self.after(8000, self.check_updates)
        if sys.platform == "win32":
            self.after(4000, self.offer_admin_fix)
        self.after(60_000, self._session_tick)
        self.after(20_000, self._ext_tick)
        if not self.accounts():
            self.status = "Log into the Riot Client with 'Stay signed in' ticked, then hit Save."
            self.status_until = time.time() + 3600
        if start_hidden and self.tray:
            self.withdraw()

    # ------------------------------------------------------------ plumbing
    def call_ui(self, fn):
        self.q.put(fn)

    def _poll(self):
        try:
            while True:
                fn = self.q.get_nowait()
                try:
                    fn()
                except Exception as e:
                    print("UI callback error:", repr(e))
        except queue.Empty:
            pass
        self.after(40, self._poll)

    def _load_assets(self):
        ASSETS.ensure()
        self.call_ui(self.redraw)

    def logo_photo(self, size):
        if not HAS_PIL:
            return None
        k = (size, ACCENT, ACCENT_HI)
        cache = self.__dict__.setdefault("_logos", {})
        if k not in cache:
            try:
                cache[k] = ImageTk.PhotoImage(make_app_icon(size))
            except Exception:
                cache[k] = None
        return cache[k]

    def make_icons(self):
        if not HAS_PIL:
            return
        try:
            APP_DIR.mkdir(parents=True, exist_ok=True)
            self.app_ico = APP_DIR / "app.ico"
            make_ico(self.app_ico)
            self._icon_photos = [ImageTk.PhotoImage(make_app_icon(sz)) for sz in (64, 32, 16)]
            self.iconphoto(True, *self._icon_photos)
        except Exception:
            pass

    def accounts(self):
        """Saved accounts in display order. Called many times per frame, so it's cached:
        the folder is only listed again when its modification time changes (adding,
        deleting or renaming an account), checked at most twice a second."""
        now = time.time()
        c = getattr(self, "_acc_cache", None)
        order = tuple(self.state_.get("order", [])) + (ACC_GEN[0],)
        if c and now - c[0] < 0.5 and c[2] == order:
            return list(c[3])
        try:
            mt = ACC_DIR.stat().st_mtime_ns if ACC_DIR.exists() else 0
        except OSError:
            mt = 0
        if c and c[1] == mt and c[2] == order:
            self._acc_cache = (now, mt, order, c[3])
            return list(c[3])
        names = [p.name for p in ACC_DIR.iterdir()
                 if p.is_dir() and not p.name.endswith(".tmp")] if ACC_DIR.exists() else []
        od = [n for n in self.state_.get("order", []) if n in names]
        res = od + sorted((n for n in names if n not in od), key=str.lower)
        self._acc_cache = (now, mt, order, tuple(res))
        return res

    def accounts_changed(self):
        self._acc_cache = None

    def persist(self):
        self.state_["order"] = self.accounts()
        save_state(self.state_)
        if self.tray:
            try:
                self.tray.update_menu()
            except Exception:
                pass

    def m(self, name):
        if not name:
            return {}
        if name not in self.meta:
            self.meta[name] = load_meta(name)
        return self.meta[name]

    def update_meta(self, name, upd):
        m = self.m(name)
        m.update(upd)
        save_meta(name, m)
        self.redraw()

    def is_hidden(self):
        return self.state() == "withdrawn"

    def save_soon(self, delay=500):
        """Save settings once things settle (e.g. while a slider is being dragged)."""
        if getattr(self, "_save_job", None):
            try:
                self.after_cancel(self._save_job)
            except Exception:
                pass
        self._save_job = self.after(delay, lambda: (setattr(self, "_save_job", None),
                                                    save_state(self.state_)))

    def play_ui(self, name):
        """Optional, very quiet interface sounds (Settings > Appearance, off by default)."""
        if not self.settings.get("ui_sounds") or PreviewAudio.current is not None:
            return
        now = time.time()
        if now - getattr(self, "_snd_t", 0) < 0.05:
            return
        self._snd_t = now
        threading.Thread(target=play_ui_sound, args=(name,), daemon=True).start()

    def toast(self, msg, kind="info", tray=True):
        if kind == "bad":
            self.log(msg)
        if kind in ("good", "wish"):
            self.play_ui("success")
        elif kind == "bad":
            self.play_ui("error")
        self.status, self.status_until = msg, time.time() + 6
        for t in self.toasts:            # the same message again just refreshes its timer
            if t["msg"] == msg and not t.get("gone"):
                t["t"] = max(t["t"], time.time() - 0.3)
                self.draw_overlays()
                return
        self._toast_id = getattr(self, "_toast_id", 0) + 1
        self.toasts.append({"msg": msg, "kind": kind, "t": time.time(), "id": self._toast_id})
        self.toasts = self.toasts[-4:]
        self.after(5600, self.redraw)
        self.redraw()
        if tray and self.tray and self.is_hidden() and kind in ("good", "bad", "wish"):
            try:
                self.tray.notify(msg, APP_TITLE)
            except Exception:
                pass

    def set_status(self, msg, kind=None):
        if kind:
            self.call_ui(lambda: self.toast(msg, kind))
        else:
            def apply():
                self.status, self.status_until = msg, time.time() + 15
                self.redraw()
                self.after(15100, self.redraw)
            self.call_ui(apply)

    def status_opts(self):
        return {"mode": self.settings.get("status_mode", "online"),
                "engine": self.settings.get("status_engine", "builtin"),
                "deceive_path": self.settings.get("deceive_path", ""),
                "enabled": self.settings.get("status_enabled", False), "proxy": self.proxy}

    def streamer(self):
        return bool(self.settings.get("streamer"))

    def rid(self, m):
        if not m.get("game_name"):
            return None
        if self.streamer():
            return "Hidden#•••"
        return f"{m['game_name']}#{m.get('tag', '')}"

    def short_vp(self, n):
        n = int(n or 0)
        if n >= 1_000_000:
            return f"{n / 1_000_000:.1f}M"
        if n >= 10_000:
            return f"{round(n / 1000):,}k"
        return f"{n:,}"

    def money(self, n):
        return "•••" if self.streamer() else f"{n or 0:,}"

    # ------------------------------------------------------------ widgets
    def entry(self, parent, var, show="", plain=False):
        if plain:
            return tk.Entry(parent, textvariable=var, bg=CARD, fg=TEXT, insertbackground=TEXT,
                            relief="flat", font=(self.UI, 10), highlightthickness=0, show=show)
        box = RoundField(self, parent, var, show)
        e = box.entry
        # geometry calls go to the rounded container, everything else to the Entry
        for meth in ("pack", "grid", "place", "pack_forget", "grid_forget", "destroy"):
            setattr(e, meth, (lambda m: lambda *a, **k: getattr(box, m)(
                *a, **{kk: vv for kk, vv in k.items() if kk not in ("ipady", "ipadx")}))(meth))

        orig_config = e.config

        def config(**kw):
            r = orig_config(**kw)
            if "width" in kw:
                box.configure(width=e.winfo_reqwidth() + 28)
            return r
        e.config = e.configure = config
        e.box = box
        return e

    def button(self, parent, text, color, cmd):
        return RoundButton(self, parent, text, color, cmd)

    def center(self, win):
        if isinstance(win, Sheet):
            win.present()
            return
        dark_titlebar(win)
        win.update_idletasks()
        if self.is_hidden():
            x = (win.winfo_screenwidth() - win.winfo_width()) // 2
            y = (win.winfo_screenheight() - win.winfo_height()) // 3
        else:
            x = self.winfo_rootx() + (self.winfo_width() - win.winfo_width()) // 2
            y = self.winfo_rooty() + max(20, (self.winfo_height() - win.winfo_height()) // 3)
        win.geometry(f"+{max(0, x)}+{max(0, y)}")
        win.lift()
        win.attributes("-topmost", True)
        win.grab_set()
        win.focus_force()

    # ------------------------------------------------------------ drawing helpers
    def fobj(self, size, weight):
        k = (size, weight)
        if k not in self._fonts:
            self._fonts[k] = tkfont.Font(family=self.UI, size=size, weight=weight)
        return self._fonts[k]

    def measure(self, s, size=10, weight="normal"):
        k = (s, size, weight)
        c = self.__dict__.setdefault("_mcache", {})
        v = c.get(k)
        if v is None:
            if len(c) > 6000:
                c.clear()
            v = c[k] = self.fobj(size, weight).measure(s)
        return v

    def wrap(self, s, size, maxw, weight="normal", max_lines=None):
        """Word-wrap text to a width (in pixels) using the real font metrics."""
        out = []
        fo = self.fobj(size, weight)
        for para in str(s or "").split("\n"):
            line = ""
            for word in para.split(" "):
                t = (line + " " + word).strip()
                if fo.measure(t) <= maxw or not line:
                    line = t
                else:
                    out.append(line)
                    line = word
            out.append(line)
        if max_lines and len(out) > max_lines:
            out = out[:max_lines]
            while out[-1] and fo.measure(out[-1] + "…") > maxw:
                out[-1] = out[-1][:-1]
            out[-1] += "…"
        return out

    def shape_img(self, w, h, r, fill, outline, width, depth=0.0, alpha=1.0):
        """Anti-aliased rounded rectangle as a cached image (Tk polygons are jagged).
        depth > 0 lights it from above: the fill brightens slightly towards the top and the
        top edge of the border catches the light, which reads as a raised surface."""
        depth = round(depth, 2)
        alpha = round(alpha, 2)
        key = (w, h, round(r, 1), fill, outline, width, depth, alpha)
        im = self._shapes.get(key)
        if im is not None:
            self._shapes.move_to_end(key)
            self._shape_pil = self.__dict__.get("_pil_of", {}).get(key)
            if self._shape_pil is not None:
                return im
        s_ = 3
        W, H = w * s_, h * s_
        rr = max(0, min(r, w / 2, h / 2)) * s_
        bw = max(1, int(width * s_)) if outline else 0
        if not depth:
            big = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            ImageDraw.Draw(big).rounded_rectangle((0, 0, W - 1, H - 1), rr, fill=fill or None,
                                                  outline=outline or None, width=bw)
        else:
            big = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            mask = Image.new("L", (W, H), 0)
            ImageDraw.Draw(mask).rounded_rectangle((0, 0, W - 1, H - 1), rr, fill=255)
            if fill:
                top = mix(fill, "#ffffff", 0.028 * depth)
                bot = mix(fill, "#000000", 0.06 * depth)
                big.paste(_vgrad(W, H, top, bot), (0, 0), mask)
                # a whisper of light just inside the top edge
                gl = Image.new("L", (W, H), 0)
                ImageDraw.Draw(gl).rounded_rectangle((0, 0, W - 1, min(H - 1, int(H * 0.5))), rr,
                                                     fill=int(7 * depth))
                from PIL import ImageFilter as _IF
                gl = ImageChops.multiply(gl.filter(_IF.GaussianBlur(max(2, H * 0.12))), mask)
                big = Image.composite(Image.new("RGBA", (W, H), (255, 255, 255, 255)), big,
                                      gl) if fill else big
                big.putalpha(ImageChops.multiply(big.getchannel("A"), mask))
            edge = outline or (mix(fill, "#ffffff", 0.10) if fill else None)
            if edge:
                ring = Image.new("L", (W, H), 0)
                ImageDraw.Draw(ring).rounded_rectangle((0, 0, W - 1, H - 1), rr, outline=255,
                                                       width=bw or s_)
                hi = mix(edge, "#ffffff", 0.13 * depth)
                lo = edge if outline else mix(fill, "#000000", 0.0)
                col = _vgrad(W, H, hi, lo, 0.55)
                if not outline:   # borderless: only the lit top edge shows, fading out
                    ring = ImageChops.multiply(ring, _vgrad_l(W, H, 150, 0, 0.45))
                big = Image.composite(col, big, ring)
        if alpha < 1:
            big.putalpha(big.getchannel("A").point(lambda v: int(v * alpha)))
        small = big.resize((w, h), Image.LANCZOS)
        self._shape_pil = small
        pil_of = self.__dict__.setdefault("_pil_of", {})
        if len(pil_of) > 400:
            pil_of.clear()
        pil_of[key] = small
        im = ImageTk.PhotoImage(small)
        self._shapes[key] = im
        if len(self._shapes) > 5000:
            for _ in range(800):
                self._shapes.popitem(last=False)
        return im

    def shape_parts(self, w, h, r, fill, outline, width, depth, rr):
        """A big rounded rectangle split into 3 opaque bands plus 4 small corners. Opaque
        images are just copied to the screen; only the corners need alpha blending (Tk
        does that in software, so blending a whole panel every frame was costly)."""
        key = ("parts", w, h, round(r, 1), fill, outline, width, round(depth, 2), rr)
        got = self._shapes.get(key)
        if got is not None:
            self._shapes.move_to_end(key)
            return got
        self.shape_img(w, h, r, fill, outline, width, depth)          # builds the PIL image
        big = self._shape_pil
        out = []
        for box, opaque in (((rr, 0, w - rr, rr), True), ((0, rr, w, h - rr), True),
                            ((rr, h - rr, w - rr, h), True), ((0, 0, rr, rr), False),
                            ((w - rr, 0, w, rr), False), ((0, h - rr, rr, h), False),
                            ((w - rr, h - rr, w, h), False)):
            piece = big.crop(box)
            if opaque:
                piece = piece.convert("RGB")
            out.append((ImageTk.PhotoImage(piece), box[0], box[1]))
        self._shapes[key] = out
        return out

    def rrect(self, x1, y1, x2, y2, r, **kw):
        if HAS_PIL and not kw.get("dash"):
            X1, Y1 = int(round(x1)), int(round(y1))
            W, H = int(round(x2)) - X1, int(round(y2)) - Y1
            if W < 1 or H < 1:
                return None
            fill, out = kw.get("fill", ""), kw.get("outline", "")
            if not fill and not out:
                return None
            depth = kw.get("depth")
            if depth is None:     # bordered panels get gentle depth everywhere by default
                depth = 1.0 if (out and fill and H >= 34 and W >= 60) else 0.0
            try:
                a_ = kw.get("alpha", 1.0)
                rr = int(min(r, W / 2, H / 2) + 1.5)
                if fill and a_ >= 1 and W * H >= 9000 and W > 2 * rr + 4 and H > 2 * rr + 4:
                    parts = self.shape_parts(W, H, r, fill, out, kw.get("width", 1), depth, rr)
                    tags = kw.get("tags", ())
                    first = None
                    for ph, dx, dy in parts:
                        i_ = self.cv.create_image(X1 + dx, Y1 + dy, image=ph, anchor="nw",
                                                  tags=tags)
                        first = first or i_
                    return first
                img = self.shape_img(W, H, r, fill, out, kw.get("width", 1), depth, a_)
                return self.cv.create_image(X1, Y1, image=img, anchor="nw",
                                            tags=kw.get("tags", ()))
            except Exception:
                pass
        kw.pop("depth", None)
        kw.pop("alpha", None)
        r = max(0, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
        pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
               x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
        kw.setdefault("outline", "")
        return self.cv.create_polygon(pts, smooth=True, **kw)

    SOFT_ON = False     # big blurred images are expensive for Tk to blend on Windows

    def soft(self, x1, y1, x2, y2, r, color="#000000", alpha=110, spread=14, dy=6, tags=(),
             keep=False):
        """Blurred shadow / glow behind a rounded box. Only drawn for things that float
        above the page (keep=True): Tk blends these in software on every redraw."""
        if not HAS_PIL or not (keep or self.SOFT_ON):
            return
        W, H = int(x2 - x1), int(y2 - y1)
        if W < 2 or H < 2:
            return
        key = ("soft", W, H, round(r), color, alpha, spread)
        im = self._shapes.get(key)
        if im is None:
            from PIL import ImageFilter
            pad = spread * 2
            sm = 2
            base = Image.new("RGBA", ((W + pad * 2) // sm, (H + pad * 2) // sm), (0, 0, 0, 0))
            rgb = tuple(int(color[i:i + 2], 16) for i in (1, 3, 5))
            ImageDraw.Draw(base).rounded_rectangle(
                (pad // sm, pad // sm, (pad + W) // sm, (pad + H) // sm), max(1, r // sm),
                fill=rgb + (alpha,))
            base = base.filter(ImageFilter.GaussianBlur(spread / sm / 1.6))
            im = ImageTk.PhotoImage(base.resize((W + pad * 2, H + pad * 2), Image.BILINEAR))
            self._shapes[key] = im
        pad = spread * 2
        self.cv.create_image(int(x1) - pad, int(y1) - pad + dy, image=im, anchor="nw", tags=tags)

    def icon(self, x, y, name, size, fill, **kw):
        if self.ICON:
            return self.cv.create_text(x, y, text=ICON_CODES[name], font=(self.ICON, size),
                                       fill=fill, **kw)
        return self.cv.create_text(x, y, text=ICON_FALLBACK[name],
                                   font=(self.UI, size + 2, "bold"), fill=fill, **kw)

    def text(self, x, y, s, size=10, weight="normal", fill=None, maxw=None, **kw):
        s = str(s)
        if maxw and s:
            if self.measure(s, size, weight) > maxw:
                key = (s, size, weight, int(maxw))
                tc = self.__dict__.setdefault("_tcache", {})
                cut = tc.get(key)
                if cut is None:
                    lo, hi = 0, len(s)          # binary search, not one measure per char
                    while lo < hi:
                        mid = (lo + hi + 1) // 2
                        if self.measure(s[:mid] + "…", size, weight) <= maxw:
                            lo = mid
                        else:
                            hi = mid - 1
                    if len(tc) > 4000:
                        tc.clear()
                    cut = tc[key] = s[:lo] + "…"
                s = cut
        kw.setdefault("anchor", "w")
        return self.cv.create_text(x, y, text=s, font=(self.UI, size, weight),
                                   fill=fill or TEXT, **kw)

    def toggle_switch(self, x, cy, on, key, tags=(), enabled=True, w=42, h=24):
        """Toggle switch: the knob glides over with a tiny overshoot, squishes while pressed
        and the track lights up when on."""
        t = self.tween("tog:" + key, 1.0 if on else 0.0, 0.3, "back")
        tq = round(max(0.0, min(1.0, t)) * 10) / 10
        pr = self.pressed(key) if enabled else 0
        f = self.hv(key) if enabled else 0
        y0, y1 = cy - h / 2, cy + h / 2
        if tq > 0 and enabled:
            self.soft(x, y0, x + w, y1, h / 2, ACCENT, alpha=int(70 * tq), spread=7, dy=1,
                      tags=tags)
        off_col = mix(mix(CARD_HI, BG, 0.15), CARD_HI, 0.5 * f)
        track = mix(off_col, ACCENT, tq) if enabled else mix(CARD, SURFACE, 0.4)
        self.rrect(x, y0, x + w, y1, h / 2, fill=track, depth=0.8,
                   outline=mix(mix(LINE, "#ffffff", 0.06), ACCENT_HI, tq) if enabled else LINE,
                   tags=tags)
        kr = h / 2 - 3
        kw = 2 * kr + 5 * pr                       # squish while held
        kx = x + 3 + (w - 6 - kw) * max(-0.05, min(1.05, t))
        self.soft(kx, cy - kr, kx + kw, cy + kr, kr, "#000000", alpha=110, spread=4, dy=2,
                  tags=tags)
        knob = mix(mix(MUTED, "#ffffff", 0.3), "#ffffff", tq) if enabled else DIM
        self.rrect(kx, cy - kr, kx + kw, cy + kr, kr, fill=knob, depth=1.0, tags=tags)
        return w

    def hover_bg(self, x1, y1, x2, y2, r, key, base=None, hot=None, tags=()):
        """Hover highlight for a row that sits inside a panel. Nothing is drawn at rest (so
        the panel's own shading shows through) and the row stays clickable via its box."""
        self.hit_boxes.append(((x1, y1, x2, y2), key))
        f = self.hv(key)
        pr = self.pressed(key)
        if f <= 0 and not pr:
            return
        hot = hot or CARD
        col = mix(base or SURFACE, hot, f)
        if pr:
            col = mix(col, mix(hot, "#000000", 0.2), 0.5 * pr)
        self.rrect(x1, y1, x2, y2, r, fill=col, tags=tags, depth=0)

    def pill(self, x, y, label, fill=None, fg=None, size=8, tags=(), anchor="w", outline=""):
        w = self.measure(label, size, "bold") + 16
        if anchor == "e":
            x -= w
        elif anchor == "center":
            x -= w / 2
        self.rrect(x, y - 10, x + w, y + 10, 10, fill=fill or CARD, tags=tags, outline=outline)
        self.text(x + w / 2, y, label, size, "bold", fg or MUTED, anchor="center", tags=tags)
        return w

    def hit(self, key, click=None, dbl=None, right=None, tip=None, box=None, down=None,
            drag=None):
        self.hits[key] = {"click": click, "dbl": dbl, "right": right, "tip": tip,
                          "down": down, "drag": drag}
        if box:
            self.hit_boxes.append((box, key))
        return ("hit:" + key,)

    def circle(self, x, y, r, **kw):
        if HAS_PIL and not kw.get("dash") and r >= 2:
            return self.rrect(x - r, y - r, x + r, y + r, r, **kw)
        kw.setdefault("outline", "")
        kw.pop("depth", None)
        return self.cv.create_oval(x - r, y - r, x + r, y + r, **kw)

    def image(self, url, x, y, w, h, anchor="nw", tags=(), **kw):
        im = self.images.get(url, w, h, **kw) if (self.images and url) else None
        if im:
            self.cv.create_image(x, y, image=im, anchor=anchor, tags=tags)
        elif self.images and url and url in self.images.pending:
            x0, y0 = (x - w / 2, y - h / 2) if anchor == "center" else (x, y)
            self.skel(x0, y0, x0 + w, y0 + h, min(12, kw.get("radius") or 8), tags=tags)
        return im

    def empty_state(self, x0, x1, y, icon, title, sub="", action=None, tone=None, h=None):
        """The one look for 'nothing here yet' and 'couldn't load' states: an icon in a soft
        glowing well, a title, a line of explanation and an optional button.
        action = (label, fn, key, icon). Returns the bottom y."""
        col = tone or ACCENT
        bw = x1 - x0
        lines = 1 + int(self.measure(sub, 10) // max(1, min(560, bw - 80))) if sub else 0
        h = h or (150 + 18 * max(0, lines - 1) + (52 if action else 0))
        self.rrect(x0, y, x1, y + h, 18, fill=SURFACE, outline=LINE)
        cx = (x0 + x1) / 2
        iy = y + 44
        self.soft(cx - 24, iy - 24, cx + 24, iy + 24, 24, col, alpha=80, spread=12, dy=0)
        self.circle(cx, iy, 24, fill=mix(SURFACE, col, 0.18), depth=1.0)
        self.icon(cx, iy, icon, 13, mix(col, "#ffffff", 0.35))
        self.text(cx, y + 90, title, 13, "bold", anchor="center", maxw=bw - 40)
        if sub:
            self.cv.create_text(cx, y + 112, text=sub, width=min(560, bw - 80), anchor="n",
                                justify="center", font=(self.UI, 10), fill=MUTED)
        if action:
            lab, fn, key, ic = (tuple(action) + (None,))[:4]
            bwid = self.measure(lab, 10, "bold") + (48 if ic else 30)
            self.action_button(cx - bwid / 2, y + h - 54, lab, fn, key, ic)
        return y + h

    # ---- skeletons: shaped placeholders that shimmer while content loads
    def skel(self, x0, y0, x1, y1, r=8, phase=0.0, tags=()):
        """One shimmering placeholder block. A soft highlight sweeps left to right across
        every skeleton on screen together, so loading looks calm and deliberate."""
        col = mix(SURFACE, CARD, 0.6 + 0.15 * ((int(phase * 2)) % 2))
        self.rrect(x0, y0, x1, y1, r, fill=col, depth=0, tags=tags)

    def skeleton_rows(self, x0, x1, y, n=4, row_h=58, avatar=True, panel=True):
        """A list's worth of skeleton rows (avatar + two lines). Returns the bottom y."""
        if panel:
            self.rrect(x0, y, x1, y + n * row_h + 12, 16, fill=SURFACE, outline=LINE)
        for i in range(n):
            ry = y + 6 + i * row_h
            lx = x0 + 18
            if avatar:
                self.skel(lx, ry + 10, lx + 38, ry + 48, 19, i)
                lx += 54
            wide = (x1 - lx) * (0.42 - 0.06 * (i % 3))
            self.skel(lx, ry + 16, lx + wide, ry + 27, 5, i)
            self.skel(lx, ry + 35, lx + wide * 0.6, ry + 44, 4, i + 0.5)
            self.skel(x1 - 110, ry + 22, x1 - 22, ry + 36, 7, i + 1)
        return y + n * row_h + 12

    def skeleton_cards(self, x0, x1, y, n=3, h=140, cols=3, gap=14):
        cw = (x1 - x0 - gap * (cols - 1)) / cols
        for i in range(n):
            cx = x0 + (i % cols) * (cw + gap)
            cy = y + (i // cols) * (h + gap)
            self.rrect(cx, cy, cx + cw, cy + h, 16, fill=SURFACE, outline=LINE)
            self.skel(cx + 16, cy + 16, cx + cw - 16, cy + h * 0.5, 10, i)
            self.skel(cx + 16, cy + h * 0.5 + 14, cx + cw * 0.6, cy + h * 0.5 + 26, 5, i)
            self.skel(cx + 16, cy + h * 0.5 + 34, cx + cw * 0.4, cy + h * 0.5 + 44, 4, i)
        return y + ((n - 1) // cols + 1) * (h + gap)

    def avatar_img(self, size, radius, col):
        key = ("av", size, round(radius), col)
        im = self._shapes.get(key)
        if im is None:
            s_ = 2
            n = size * s_
            top = tuple(int(mix(col, "#ffffff", 0.18)[i:i + 2], 16) for i in (1, 3, 5))
            bot = tuple(int(mix(col, "#000000", 0.35)[i:i + 2], 16) for i in (1, 3, 5))
            grad = Image.new("RGBA", (1, 256))
            grad.putdata([tuple(int(a + (b - a) * (i / 255)) for a, b in zip(top, bot)) + (255,)
                          for i in range(256)])
            from PIL import ImageFilter
            g = grad.resize((n, n))
            hl = Image.new("RGBA", (n, n), (0, 0, 0, 0))
            ImageDraw.Draw(hl).ellipse((-n * 0.2, -n * 0.7, n * 1.0, n * 0.35),
                                       fill=(255, 255, 255, 34))
            hl = hl.filter(ImageFilter.GaussianBlur(n * 0.08))
            g = Image.alpha_composite(g, hl)
            mask = Image.new("L", (n, n), 0)
            ImageDraw.Draw(mask).rounded_rectangle((0, 0, n - 1, n - 1), radius * s_, fill=255)
            g.putalpha(mask)
            im = ImageTk.PhotoImage(g.resize((size, size), Image.LANCZOS))
            self._shapes[key] = im
        return im

    def letter_avatar(self, x, y, size, name, radius=14, tags=(), hover=False):
        col = avatar_color(name)
        if hover:
            col = mix(col, "#ffffff", 0.08)
        drawn = False
        if HAS_PIL:
            try:
                self.cv.create_image(int(x), int(y), image=self.avatar_img(int(size), radius, col),
                                     anchor="nw", tags=tags)
                drawn = True
            except Exception:
                drawn = False
        if not drawn:
            self.rrect(x, y, x + size, y + size, radius, fill=col, tags=tags)
        self.cv.create_text(x + size / 2, y + size / 2, text=name[:1].upper(),
                            font=(self.UI, max(9, int(size * 0.33)), "bold"),
                            fill="#ffffff", tags=tags)

    def card_url(self, name, kind="small"):
        card = self.m(name).get("card")
        return ASSETS.cards.get(card, {}).get(kind) if card else None

    def account_art(self, x, y, size, name, radius=14, tags=(), hover=False):
        if not self.image(self.card_url(name), x, y, size, size, tags=tags, mode="cover",
                          radius=int(radius)):
            self.letter_avatar(x, y, size, name, radius, tags, hover)

    def rank_icon(self, tier, x, y, size, tags=(), large=False):
        if not tier or tier < 3:
            return False
        return bool(self.image(ASSETS.tier_icon(tier, large), x, y, size, size,
                               anchor="center", tags=tags))

    def rank_text(self, m):
        if m.get("tier") is None:
            return None
        if not m.get("tier") or m["tier"] < 3:
            return "Unranked"
        return f"{ASSETS.tier_name(m['tier'])} · {m.get('rr', 0)} RR"

    def bar(self, x, y, w, frac, h=8, color=None, bg=None, key=None):
        """Progress bar. Fills in from empty when its page opens and glides when the value
        changes; bars are told apart by draw order unless they pass a key."""
        self._bar_i = getattr(self, "_bar_i", 0) + 1
        k = "bar:" + (key or f"{self.page}:{self._bar_i}")
        frac = max(0.0, min(1.0, float(frac or 0)))
        # drawn at its value straight away: a growing bar is a new image every frame
        f = frac
        self.rrect(x, y, x + w, y + h, h / 2, fill=bg or CARD)
        if f > 0.002:
            col = color or ACCENT
            fw = max(h, w * f)
            self.rrect(x, y, x + fw, y + h, h / 2, fill=col)
            if h >= 6 and fw > h * 2:     # soft highlight along the top of the fill
                self.rrect(x + h / 2, y + 1, x + fw - h / 2, y + max(2, h * 0.38), h * 0.2,
                           fill=mix(col, "#ffffff", 0.22))

    def section(self, x, y, icon, title, extra=None):
        self.icon(x + 8, y + 12, icon, 12, SOFT)
        self.text(x + 26, y + 12, title, 15, "bold")
        if extra:
            self.text(x + 36 + self.measure(title, 15, "bold"), y + 13, extra, 10, fill=DIM)

    def card_box(self, x1, y1, x2, y2, title=None, icon=None, r=16):
        self.soft(x1, y1, x2, y2, r, alpha=90, spread=10, dy=5)
        self.rrect(x1, y1, x2, y2, r, fill=SURFACE, outline=LINE)
        if title:
            if icon:
                self.icon(x1 + 22, y1 + 22, icon, 10, SOFT)
            self.text(x1 + (38 if icon else 18), y1 + 22, title, 9, "bold", DIM,
                      maxw=x2 - x1 - 50)

    # ---- motion: tiny tween engine on top of the redraw loop
    # Every animated value in the app goes through tween(): one place decides the curves,
    # one place keeps frames coming while anything moves, and turning Animations off in
    # Settings snaps everything to its final state.
    def tween(self, key, target, dur=0.22, ease="out", delay=0.0):
        """Eased value that glides to `target`. Keeps frames coming while it moves."""
        if not self.settings.get("animations", True):
            self._tw.pop(key, None)
            return target
        now = time.time()
        st = self._tw.get(key)
        if st is None:
            self._tw[key] = (target, target, now, dur, ease)
            return target
        frm, to, t0, d, ez = st if len(st) == 5 else st + ("out",)
        k = min(1.0, max(0.0, (now - t0) / d)) if d else 1.0
        cur = frm + (to - frm) * EASES.get(ez, ease_out)(k)
        if to != target:
            self._tw[key] = (cur, target, now + delay, dur, ease)
            self._more = True
            return cur
        if k < 1:
            self._more = True
        return cur

    def tween_from(self, key, start, target, dur=0.5, ease="quint", delay=0.0):
        """Start a tween at `start` (if it isn't running yet) and glide to `target`."""
        if key not in self._tw and self.settings.get("animations", True):
            self._tw[key] = (start, target, time.time() + delay, dur, ease)
            self._more = True
        return self.tween(key, target, dur, ease)

    def reset_anims(self, *prefixes):
        """Forget tweens so the next draw replays their entrance (counters, bars...)."""
        self._tw = {k: v for k, v in self._tw.items() if not k.startswith(prefixes)}

    def hv(self, key, on=None):
        """1.0 while `key` is hovered, else 0.0. Instant on purpose: an eased hover meant
        ~15 full redraws per mouse-over, which is what made the app feel sluggish."""
        on = (self.hover == key) if on is None else bool(on)
        return 1.0 if on else 0.0

    def pressed(self, key):
        """1.0 while `key` is held down (instant, like hover)."""
        return 1.0 if (self.press and self.press[0] == key and self.hover == key) else 0.0

    def hcol(self, key, base, hot, on=None):
        f = self.hv(key, on)
        pr = self.pressed(key) if self.press else 0
        if f <= 0 and not pr:
            return base
        if not (isinstance(base, str) and isinstance(hot, str) and base.startswith("#")
                and hot.startswith("#")):
            return hot if f >= 0.5 else base
        col = hot if f >= 1 else mix(base, hot, f)
        if pr:
            col = mix(col, mix(base, "#000000", 0.25), 0.55 * pr)   # pressed: a touch deeper
        return col

    def count(self, key, value, dur=0.9):
        """Number that counts up to `value` the first time it's shown on a page visit,
        then glides between values when it changes."""
        try:
            v = float(value or 0)
        except (TypeError, ValueError):
            return value
        cur = self.tween_from("cnt:" + key, 0.0, v, dur, "quint")
        return int(round(cur)) if float(v).is_integer() else cur

    def chips(self, x, y, options, current, on_pick, key, size=10, h=32):
        """Row of selectable pills; the selected one slides between options."""
        pos = []
        cx = x
        for value, label in options:
            tw = self.measure(label, size, "bold") + 28
            pos.append((value, label, cx, tw))
            cx += tw + 8
        sel = next(((px, tw) for v, _, px, tw in pos if v == current), None)
        for value, label, px, tw in pos:
            k = f"{key}:{value}"
            if value != current:
                tags = self.hit(k, click=lambda v=value: on_pick(v))
                self.rrect(px, y, px + tw, y + h, h / 2,
                           fill=self.hcol(k, CARD, CARD_HI), tags=tags)
        if sel:
            sx = self.tween(f"chip:{key}:x", sel[0] - x, 0.34, "back") + x
            sw = self.tween(f"chip:{key}:w", sel[1], 0.34, "back")
            if h >= 26:
                self.soft(sx, y, sx + sw, y + h, h / 2, ACCENT, alpha=70, spread=8, dy=2)
            self.rrect(sx, y, sx + sw, y + h, h / 2, fill=ACCENT, depth=1.0)
        for value, label, px, tw in pos:
            k = f"{key}:{value}"
            on = value == current
            tags = self.hit(k, click=lambda v=value: on_pick(v))
            self.text(px + tw / 2, y + h / 2, label, size, "bold",
                      TEXT if on else self.hcol(k, MUTED, TEXT), anchor="center", tags=tags)
        return cx

    def action_button(self, x, y, label, fn, key, icon=None, primary=True, anchor="w", h=34,
                      tip=None, disabled=False):
        w = self.measure(label, 10, "bold") + (48 if icon else 30)
        if anchor == "e":
            x -= w
        hov = self.hover == key and not disabled
        tags = self.hit(key, click=None if disabled else fn, tip=tip)
        f = 0 if disabled else self.hv(key, hov)
        pr = 0 if disabled else self.pressed(key)
        if primary:
            fill = mix(DIM, CARD, 0.4) if disabled else self.hcol(key, ACCENT, ACCENT_HI, hov)
            if f > 0 and not pr:
                self.soft(x, y, x + w, y + h, h / 2, ACCENT, alpha=int(110 * f), spread=10,
                          dy=3, tags=tags)
        else:
            fill = mix(CARD, SURFACE, 0.5) if disabled else self.hcol(key, CARD, CARD_HI, hov)
        ins = 1.5 * pr                      # pressed: sinks a hair and tightens
        self.rrect(x + ins, y + ins, x + w - ins, y + h - ins + 0.5 * pr, h / 2, fill=fill,
                   tags=tags, depth=0 if disabled else (1.0 - 0.6 * pr),
                   outline="" if primary or disabled else mix(LINE, CARD_HI, f))
        dy = 0.5 * pr
        fg = DIM if disabled else (TEXT if primary else self.hcol(key, SOFT, TEXT, hov))
        tx = x + 15
        if icon:
            self.icon(tx + 6, y + h / 2 + dy, icon, 10, fg, tags=tags)
            tx += 20
        self.text(tx, y + h / 2 + dy, label, 10, "bold", fg, tags=tags)
        return w

    # ------------------------------------------------------------ main draw
    def redraw(self):
        if self._pending:
            return
        self._pending = True
        self.after_idle(self._draw)

    # ------------------------------------------------------------- frame pacing
    FRAME = 1 / 60

    def next_frame(self, fn):
        """Schedule the next animation frame on a steady 60 fps clock. Waiting a flat 16 ms
        *after* each frame (plus Windows' default ~16 ms timer tick) gave 25-30 fps with
        uneven gaps - choppy on any PC. While anything animates we hold Windows' 1 ms timer
        and subtract the time the frame took."""
        now = self.hold_fine_timer()
        start = getattr(self, "_frame_t0", now)
        delay = max(1, int((self.FRAME - (now - start)) * 1000))
        self.after(delay, fn)

    def hold_fine_timer(self):
        now = time.perf_counter()
        if not getattr(self, "_fine_timer", False):
            self._fine_timer = True
            timer_resolution(True)
            self.after(500, self._fine_timer_check)
        self._fine_until = now + 1.5
        return now

    def _fine_timer_check(self):
        if time.perf_counter() < getattr(self, "_fine_until", 0):
            self.after(500, self._fine_timer_check)
        else:
            self._fine_timer = False
            timer_resolution(False)

    def toggle_perf_hud(self):
        self.perf_hud = not getattr(self, "perf_hud", False)
        self._perf = []
        self.redraw()

    def _perf_note(self, draw_ms):
        """Frame stats for the Ctrl+Shift+F readout: Python build time, Tk paint time
        (measured by an idle callback queued behind the canvas repaint) and frame rate."""
        t_end = time.perf_counter()
        t0 = self._frame_t0

        def painted():
            now = time.perf_counter()
            self._perf.append((t0, draw_ms, (now - t_end) * 1000))
            self._perf = self._perf[-90:]
            self._perf_paint()
        self.after_idle(painted)

    def _perf_paint(self):
        c = self.cv
        c.delete("perfhud")
        f = [p for p in self._perf if time.perf_counter() - p[0] < 1.0]
        if len(f) >= 2:
            fps = (len(f) - 1) / max(1e-3, f[-1][0] - f[0][0])
        else:
            fps = 0
        dr = sum(p[1] for p in f) / max(1, len(f))
        pt = sum(p[2] for p in f) / max(1, len(f))
        worst = max((p[1] + p[2] for p in f), default=0)
        txt = (f"{fps:4.0f} fps   build {dr:4.1f} ms   paint {pt:4.1f} ms   worst {worst:4.0f} ms"
               f"   items {len(c.find_all())}")
        w = c.winfo_width()
        c.create_rectangle(w - 470, 6, w - 8, 30, fill="#000000", outline="", tags="perfhud")
        c.create_text(w - 14, 18, text=txt, anchor="e", fill="#7CFFB2",
                      font=("Consolas", 10), tags="perfhud")

    def _draw(self):
        self._pending = False
        self._frame_t0 = time.perf_counter()
        c = self.cv
        try:
            had_focus = self.focus_get() is self.search
        except Exception:
            had_focus = False
        try:
            foc = self.focus_get()
        except Exception:
            foc = None
        c.delete("all")
        for L in self.layers:
            L.entries = {n: (e, None) for n, (e, _) in L.entries.items()}
        self._refocus = foc if any(foc is e for L in self.layers
                                   for e, _ in L.entries.values()) else None
        self.hits = {}
        self.hit_boxes = []
        self.search_shown = False
        w, h = max(c.winfo_width(), 400), max(c.winfo_height(), 300)

        self._more = False
        self._shimmer = False
        anim = self.settings.get("animations", True)
        self.advance_scroll()
        if len(self._tw) > 1500:
            now_ = time.time()
            self._tw = {k: v for k, v in self._tw.items()
                        if now_ - v[2] < v[3] + 0.5 or k.startswith(("cnt:", "bar:"))}
        # no fade between rank colours: every in-between colour was a brand-new full-window
        # image (~15 MP pushed into Tk per account click) - the main source of click lag
        self.glow_cur = self.glow_target()
        c.create_rectangle(0, 0, w, h, fill=BG, outline="")
        cx, cy, R = w * 0.58, h * 0.98, max(w, h) * 0.78
        bgp = self.bg_image(w, h) or self.glow_photo(w, h, self.glow_cur)
        steps = 0 if bgp else 38
        if bgp:
            c.create_image(0, 0, image=bgp, anchor="nw")
        for i in range(steps):
            t = i / (steps - 1)
            r = R * (1 - t * 0.92)
            c.create_oval(cx - r * 1.25, cy - r, cx + r * 1.25, cy + r,
                          fill=mix(BG, self.glow_cur, (t ** 1.7) * 0.95), outline="")

        marker = (c.find_all() or (0,))[-1]
        page = getattr(self, "draw_" + self.page, self.draw_home)
        try:
            page(w, h)
        except Exception as e:
            import traceback
            tb = traceback.format_exc()
            if getattr(self, "_last_draw_err", None) != tb:
                self._last_draw_err = tb
                self.log(f"draw {self.page}: {tb}")
            x0, x1 = self.SIDE + 36, w - 32
            self.rrect(x0, 40, x1, 170, 18, fill=mix(SURFACE, DANGER, 0.1), outline=DANGER)
            self.text(x0 + 24, 76, "This page hit a bug", 14, "bold", DANGER)
            self.text(x0 + 24, 106, f"{type(e).__name__}: {e}", 9, fill=MUTED, maxw=x1 - x0 - 48)
            self.text(x0 + 24, 134, "Everything else still works. Settings > Export diagnostics "
                                    "and send the zip so it can be fixed.", 9, fill=MUTED,
                      maxw=x1 - x0 - 48)
        self.draw_transition(marker, w, h, anim)
        self._bar_i = 0
        if self.dragging:
            self.draw_drag_ghost()
        self.draw_sidebar(w, h)
        self.draw_bottom(w, h)
        self._hb_lyr = len(self.hit_boxes)
        lyr_more = lyr_shim = False
        if self.layers:
            self._more = self._shimmer = False        # the page is frozen under a dialog
            lmark = (c.find_all() or (0,))[-1]
            self.draw_layers(w, h)
            for item in c.find_all():
                if item <= lmark:
                    continue
                tg = c.gettags(item)
                if "lyrwin" not in tg and "lyrscrim" not in tg:
                    c.addtag_withtag("lyr", item)
            lyr_more, lyr_shim = self._more, self._shimmer
            self._more = self._shimmer = False
        self._hb_base = len(self.hit_boxes)
        self.draw_overlays()
        if lyr_more:
            self.next_frame(self.layer_redraw)
        elif lyr_shim:
            self.after(60, self.layer_redraw)
        if had_focus and self.search_shown:
            self.search.focus_set()
        if getattr(self, "_refocus", None) is not None:
            try:
                self._refocus.focus_set()
            except tk.TclError:
                pass
            self._refocus = None
        if self.sheets:          # covered by a dialog: don't spend frames on the page
            self._more = self._shimmer = False
        if self._more:
            self.next_frame(self.redraw)
        elif self._shimmer:
            self.after(60, self.redraw)
        if getattr(self, "perf_hud", False):
            self._perf_note((time.perf_counter() - self._frame_t0) * 1000)


    # ---- page & tab transitions: content glides in while the background fades it up
    PAGE_T, TAB_T = 0.2, 0.16

    def draw_transition(self, marker, w, h, anim):
        if not anim:
            return
        now = time.time()
        c = self.cv
        if now - self.page_t < self.PAGE_T:
            age, dur, mk, y0, dist = now - self.page_t, self.PAGE_T, marker, 0, 10
        elif now - self.tab_t < self.TAB_T and self._tab_mark and self._tab_mark[2] == self.page:
            age, dur, (mk, y0, _) = now - self.tab_t, self.TAB_T, self._tab_mark
            dist = 10
        else:
            return
        self._more = True
        k = ease_out_quint(age / dur)
        dy = round((1 - k) * dist * self.page_dir, 1)
        if abs(dy) >= 0.5:
            for item in c.find_all():
                if item > mk:
                    c.move(item, 0, dy)
        # (no fade overlay: blending a full-window image every frame cost more than it
        # was worth on Windows - the slide alone reads as a transition)

    FADE_LEVELS = 4

    def fade_photo(self, w, h, level, build=True):
        """The window background at `level` opacity, laid over a new page to fade it in (Tk
        can't fade canvas items, but it does blend images). Only the current background's
        few levels are kept, and they're built ahead of time while the app is idle."""
        bg = getattr(self, "_bg_pil", None)
        n = round(level * self.FADE_LEVELS)
        if not HAS_PIL or bg is None or n <= 0 or bg.size != (w, h):
            return None
        ident = (id(bg), w, h)
        if getattr(self, "_fade_ident", None) != ident:
            self._fade_ident, self._fades = ident, {}
        ph = self._fades.get(n)
        if ph is None and build:
            crop = bg.crop((self.SIDE + 1, 0, w, h - self.BOTTOM)).convert("RGBA")
            crop.putalpha(int(255 * n / self.FADE_LEVELS))
            ph = self._fades[n] = ImageTk.PhotoImage(crop)
        return ph

    def _warm_fades(self):
        """Build the next missing fade level during idle time, one per call."""
        self._warm_job = None
        if not self.settings.get("animations", True) or not HAS_PIL:
            return
        if self._more:                              # busy animating: try again shortly
            self._warm_job = self.after(250, self._warm_fades)
            return
        w, h = max(self.cv.winfo_width(), 400), max(self.cv.winfo_height(), 300)
        for n in range(1, self.FADE_LEVELS + 1):
            if self.fade_photo(w, h, n / self.FADE_LEVELS, build=False) is None:
                self.fade_photo(w, h, n / self.FADE_LEVELS)
                self._warm_job = self.after(60, self._warm_fades)
                return

    def mark_tab_content(self, y):
        """Pages call this right under their tab bar so a tab switch only animates what
        changed, not the header above it."""
        self._tab_mark = ((self.cv.find_all() or (0,))[-1], y, self.page)

    def tab_switched(self, direction=1):
        if self.settings.get("animations", True):
            self.tab_t = time.time()
            self.page_dir = 1 if direction >= 0 else -1
            self.reset_anims("cnt:", "bar:")

    def glow_photo(self, w, h, col):
        """Smooth radial glow rendered once per size/colour (no banding, fewer canvas items)."""
        if not HAS_PIL:
            return None
        key = (w, h, col, BG)
        cache = self.__dict__.setdefault("_glow_lru", {})
        if key in cache:
            ph, pil = cache.pop(key)
            cache[key] = (ph, pil)              # most recent last
            self._bg_cache, self._bg_pil = (key, ph), pil
            return ph
        try:
            sw, sh = max(8, w // 4), max(8, h // 4)
            rgb = lambda c_: tuple(int(c_[i:i + 2], 16) for i in (1, 3, 5))  # noqa: E731
            base = Image.new("RGB", (sw, sh), rgb(BG))
            R = max(sw, sh) * 0.78
            gw, gh = int(R * 2.5), int(R * 2)
            grad = Image.radial_gradient("L").resize((gw, gh), Image.BILINEAR)
            mask = grad.point(lambda v: int(242 * max(0.0, min(1.0, (1 - v / 255) / 0.92)) ** 1.7))
            glow = Image.new("RGB", (gw, gh), rgb(col))
            base.paste(glow, (int(sw * 0.58 - gw / 2), int(sh * 0.98 - gh / 2)), mask)
            full = base.resize((w, h), Image.BICUBIC)
            ph = ImageTk.PhotoImage(full)
            self._bg_cache = (key, ph)
            self._bg_pil = full
            cache[key] = (ph, full)
            while len(cache) > 6:               # a few rank colours / window sizes
                cache.pop(next(iter(cache)))
            return ph
        except Exception:
            return None

    def glow(self, x1, y1, x2, y2, r, col=None, tags=()):
        """Soft coloured glow behind a hovered card."""
        col = col or ACCENT
        if HAS_PIL:
            self.soft(x1, y1, x2, y2, r, col, alpha=150, spread=12, dy=2, tags=tags)
            return
        for i, a in ((9, 0.10), (6, 0.18), (3, 0.30)):
            self.rrect(x1 - i, y1 - i, x2 + i, y2 + i, r + i, fill="", outline=mix(BG, col, a),
                       width=2, tags=tags)

    def glow_target(self):
        if not self.settings.get("rank_glow", True):
            return GLOW
        name = self.selected if self.page in ("profile", "home") and self.selected else \
            self.state_.get("active")
        tc = ASSETS.tier_color(self.m(name).get("tier")) if name else None
        if not tc:
            return GLOW
        return mix(mix(GLOW, tc, 0.5), BG, 0.3)

    def scroll(self):
        # whole pixels: the canvas can't draw between them, and fractional offsets made
        # cached images (graph, rounded shapes) miss the cache on every scroll frame
        return int(round(self.scrolls.get(self.page, 0)))

    def reset_scroll(self):
        self.scrolls[self.page] = 0
        self.scroll_t[self.page] = 0

    def advance_scroll(self):
        """Glide the current page's scroll towards where the wheel sent it."""
        p = self.page
        if p not in self.scroll_t:
            return
        cur, tgt = self.scrolls.get(p, 0), self.scroll_t[p]
        if not self.settings.get("animations", True) or abs(tgt - cur) < 0.6:
            self.scrolls[p] = tgt
            return
        now = time.time()
        dt = min(0.05, max(0.004, now - getattr(self, "_scroll_last", now - 0.016)))
        self._scroll_last = now
        k = 1 - 0.00008 ** dt         # ~ frame-rate independent ease-out
        self.scrolls[p] = cur + (tgt - cur) * k
        self._more = True

    def finish_scroll(self, top_y, y, h):
        content_h = y - top_y + 40
        view = h - self.BOTTOM - 10
        self.max_scroll = max(0, content_h - view)
        if self.scroll() > self.max_scroll:
            self.scrolls[self.page] = self.max_scroll
            self.scroll_t[self.page] = min(self.scroll_t.get(self.page, 0), self.max_scroll)
            self.redraw()
        if self.max_scroll > 0:
            age = time.time() - getattr(self, "_wheel_t", 0)
            a = 1.0 if age < 0.8 else max(0.0, 1 - (age - 0.8) / 0.5)
            if a > 0:
                w = max(self.cv.winfo_width(), 400)
                track = view - 24
                th = max(36, track * view / (view + self.max_scroll))
                ty = 12 + (track - th) * (self.scroll() / max(1, self.max_scroll))
                self.rrect(w - 9, ty, w - 4, ty + th, 2.5, fill=mix(BG, SOFT, 0.45 * a))
                self._more = True

    def place_search(self, x_right, y, width=220, hint="Search"):
        h = self.cv.winfo_height()
        if self.layers:
            if 8 < y < h - self.BOTTOM - 30:
                self.rrect(x_right - width, y - 17, x_right, y + 17, 17, fill=CARD,
                           outline=LINE, width=1)
                self.icon(x_right - width + 18, y, "search", 10, DIM)
                self.text(x_right - width + 34, y, self.search_var.get() or hint, 10,
                          fill=TEXT if self.search_var.get() else DIM, maxw=width - 48)
            return
        if 8 < y < h - self.BOTTOM - 30:
            x0 = x_right - width
            focused = self.focus_get() is self.search
            self.rrect(x0, y - 17, x_right, y + 17, 17, fill=CARD,
                       outline=ACCENT if focused else LINE, width=1)
            self.icon(x0 + 18, y, "search", 10, SOFT if focused else DIM)
            self.search.config(bg=CARD, highlightthickness=0, bd=0, relief="flat")
            self.cv.create_window(x0 + 34, y, window=self.search, anchor="w",
                                  width=width - 48, height=24)
            self.search_shown = True
            if not self.search_var.get() and not focused:
                self.text(x0 + 34, y, hint, 10, fill=DIM)

    def focus_search(self):
        if self.search_shown:
            self.search.focus_set()

    def page_header(self, x0, x1, y, icon, title, sub=None):
        self.soft(x0, y, x0 + 32, y + 32, 10, ACCENT, alpha=55, spread=8, dy=1)
        self.rrect(x0, y, x0 + 32, y + 32, 10, fill=mix(CARD, ACCENT, 0.22), depth=1.0,
                   outline=mix(LINE, ACCENT, 0.35))
        self.icon(x0 + 16, y + 16, icon, 12, mix(SOFT, "#ffffff", 0.3))
        self.text(x0 + 44, y + 16, title, 20, "bold")
        if sub:
            self.text(x0 + 54 + self.measure(title, 20, "bold"), y + 18, sub, 10, fill=DIM,
                      maxw=x1 - x0 - 420)

    # ------------------------------------------------------------ in-canvas layers
    LAYER_IN, LAYER_OUT = 0.22, 0.15

    def push_layer(self, L):
        self.close_pop()
        if self.is_hidden():
            # straight deiconify: show_window() asks for the PIN, which is itself a layer
            self.deiconify()
            self.lift()
            self.focus_force()
        first = not self.layers
        self.layers.append(L)
        for other in self.layers[:-1]:
            other.hide_entries()
        if first:
            self.hover = None
            self.press = None
            self.cv.config(cursor="")
        self.redraw()

    def layer_closing(self, L):
        if not self.settings.get("animations", True):
            self.remove_layer(L)
        else:
            self.layer_redraw()

    def remove_layer(self, L):
        if L.closed:
            return
        L.closed = True
        try:
            if L.__dict__.get("_scrim_item"):
                self.cv.delete(L._scrim_item)
        except tk.TclError:
            pass
        if L in self.layers:
            self.layers.remove(L)
        try:
            L.cleanup()
        except Exception as e:
            self.log(f"layer cleanup: {e!r}")
        self.hover = None
        self.press = None
        try:
            self.cv.focus_set()
        except tk.TclError:
            pass
        self.redraw()

    def close_layers(self):
        for L in list(self.layers):
            L.close()

    def top_layer(self):
        live = [L for L in self.layers if L.tc is None]
        return live[-1] if live else None

    def scrim_photo(self, w, h, n):
        """Dark veil over the page behind a dialog, at one of 4 strengths (cached)."""
        if not HAS_PIL or n <= 0:
            return None
        cache = self.__dict__.setdefault("_scrims", {})
        if cache.get("size") != (w, h, BG):
            cache.clear()
            cache["size"] = (w, h, BG)
        ph = cache.get(n)
        if ph is None:
            im = Image.new("RGBA", (w, h), _rgb(mix(BG, "#000000", 0.4)) + (int(150 * n / 4),))
            ph = cache[n] = ImageTk.PhotoImage(im)
        return ph

    def draw_layers(self, w, h):
        now = time.time()
        anim = self.settings.get("animations", True)
        live = [L for L in self.layers if not L.closed]
        top = self.top_layer()
        for L in live:
            k = 1.0 if not anim else ease_out_quint((now - L.t0) / self.LAYER_IN)
            if L.tc is not None:
                c = 1.0 if not anim else (now - L.tc) / self.LAYER_OUT
                if c >= 1:
                    if not getattr(L, "_removing", False):
                        L._removing = True
                        self.after_idle(lambda L=L: self.remove_layer(L))
                    L.hide_entries()
                    continue
                k = min(k, 1 - ease_in_out(c))
            if k < 1:
                self._more = True
            if getattr(L, "opaque", False):       # lock screen: hide everything behind it
                self.cv.create_rectangle(0, 0, w, h, fill=mix(BG, "#000000", 0.3), outline="")
            else:
                lvl = max(1, round(k * 4))
                sc = self.scrim_photo(w, h, lvl)
                if sc:
                    item = L.__dict__.get("_scrim_item")
                    try:
                        alive = item and self.cv.type(item)
                    except tk.TclError:
                        alive = False
                    if alive:
                        if L.__dict__.get("_scrim_lvl") != lvl:
                            self.cv.itemconfigure(item, image=sc)
                        if self.cv.find_above(item):        # stacked dialogs only
                            self.cv.tag_raise(item)
                    else:
                        L._scrim_item = self.cv.create_image(0, 0, image=sc, anchor="nw",
                                                             tags=("lyrscrim",))
                    L._scrim_lvl = lvl
            pw, ph = (int(v) for v in L.size(w, h))
            x0 = int((w - pw) / 2)
            y0 = int(max(16, (h - ph) / 2 - 6) + round((1 - k) * 18))
            x1, y1 = x0 + pw, y0 + ph
            L.box = (x0, y0, x1, y1)
            self.soft(x0, y0, x1, y1, 20, "#000000", alpha=int(170 * k), spread=26, dy=14, keep=True)
            self.rrect(x0, y0, x1, y1, 20, fill=SURFACE,
                       outline=mix(LINE, "#ffffff", 0.09), depth=0)
            # the light catching the panel's top edge
            self.rrect(x0 + 18, y0, x1 - 18, y0 + 1.2, 0.6, fill=mix(SURFACE, "#ffffff", 0.16),
                       depth=0)
            if L is not top:
                L.hide_entries()
            try:
                L.draw(x0, y0, x1, y1)
            except Exception as e:
                import traceback
                tb = traceback.format_exc()
                if getattr(L, "_last_err", None) != tb:
                    L._last_err = tb
                    self.log(f"layer {type(L).__name__}: {tb}")
                self.text((x0 + x1) / 2, (y0 + y1) / 2 - 10, "Something went wrong here", 13,
                          "bold", DANGER, anchor="center")
                self.text((x0 + x1) / 2, (y0 + y1) / 2 + 14, f"{type(e).__name__}: {e}", 9,
                          fill=MUTED, anchor="center", maxw=pw - 60)
                L.close_btn(x1 - 30, y0 + 30)
            if k < 1:       # fade the contents in with the panel
                self.rrect(x0 + 1, y0 + 1, x1 - 1, y1 - 1, 19, fill=SURFACE, depth=0,
                           alpha=round((1 - k) * 6) / 6)

    def layer_redraw(self):
        """Redraw only the layers (and toasts/menus above them) - never the page."""
        if not self.layers:
            self.redraw()
            return
        if self._pending or getattr(self, "_lyr_pending", False):
            return
        self._lyr_pending = True
        self.after_idle(self._layer_draw)

    def _layer_draw(self):
        self._lyr_pending = False
        if self._pending:
            return                      # a full redraw is on its way anyway
        self._frame_t0 = time.perf_counter()
        c = self.cv
        c.delete("lyr")
        c.delete("ovl")
        base = getattr(self, "_hb_lyr", None)
        if base is not None:
            del self.hit_boxes[base:]
        w, h = max(c.winfo_width(), 400), max(c.winfo_height(), 300)
        saved = (self._more, self._shimmer)
        self._more = self._shimmer = False
        marker = (c.find_all() or (0,))[-1]
        self.draw_layers(w, h)
        for item in c.find_all():
            if item <= marker:          # only ask Tk about the items just drawn
                continue
            tg = c.gettags(item)
            if "lyrwin" not in tg and "lyrscrim" not in tg:
                c.addtag_withtag("lyr", item)
        more, shim = self._more, self._shimmer
        self._more, self._shimmer = saved
        self._hb_base = len(self.hit_boxes)
        self.draw_overlays()
        if more:
            self.next_frame(self.layer_redraw)
        elif shim:
            self.after(60, self.layer_redraw)
        if getattr(self, "perf_hud", False):
            self._perf_note((time.perf_counter() - self._frame_t0) * 1000)

    def key_ok(self, key):
        """While a layer is open, only its own controls (and toasts/menus) respond."""
        if not key:
            return False
        top = self.top_layer()
        if not self.layers or top is None:
            return not self.layers or key.startswith(("toast:", "pop:"))
        return key.startswith((top.kp, "toast:", "pop:"))

    # ------------------------------------------------------------ in-app sheets
    def sheet_push(self, sh):
        if self.sheets:
            self.sheets[-1].hide()
        self.sheets.append(sh)
        self.close_pop()
        if self._bd is None:
            self._make_backdrop()
        self._bd_go(1.0, 0.22)

    def sheet_pop(self, sh):
        top = self.sheets and self.sheets[-1] is sh
        if sh in self.sheets:
            self.sheets.remove(sh)
        if self.sheets:
            if top:
                self.sheets[-1].unhide()
        else:
            self._bd_go(0.0, 0.18)
            try:
                self.cv.focus_set()
            except tk.TclError:
                pass

    def _make_backdrop(self):
        W, H = max(1, self.winfo_width()), max(1, self.winfo_height())
        raw = grab_window(self)
        if raw is None and HAS_PIL:
            raw = Image.new("RGB", (W, H), _rgb(BG))
        self._bd_raw = raw
        self._bd_final = None
        if raw is not None:
            from PIL import ImageFilter
            k = 6
            small = raw.resize((max(1, W // k), max(1, H // k)), Image.BILINEAR)
            small = small.filter(ImageFilter.GaussianBlur(3.2))
            blur = small.resize((W, H), Image.BICUBIC)
            self._bd_final = Image.blend(blur, Image.new("RGB", (W, H), _rgb(mix(BG, "#000000",
                                                                                 0.35))), 0.42)
        self._bd_frames = {}
        cv = tk.Canvas(self, bg=mix(BG, "#000000", 0.3), highlightthickness=0, bd=0)
        cv.place(x=0, y=0, relwidth=1, relheight=1)
        cv.bind("<ButtonPress-1>", self._bd_click)
        cv.bind("<Button-3>", self._bd_click)
        self._bd = cv
        self._bd_lvl = self._bd_from = self._bd_to = 0.0
        self._bd_t0, self._bd_dur = time.time(), 0.2
        self._bd_item = None
        self._bd_show(0.0)

    def _bd_show(self, lvl):
        if self._bd is None or self._bd_final is None:
            return
        n = 2           # raw -> halfway -> final: each frame is a full-window image
        k = max(0, min(n, round(lvl * n)))
        ph = self._bd_frames.get(k)
        if ph is None:
            im = self._bd_raw if k == 0 else (self._bd_final if k == n else
                                              Image.blend(self._bd_raw, self._bd_final, k / n))
            ph = self._bd_frames[k] = ImageTk.PhotoImage(im)
        if self._bd_item is None:
            self._bd_item = self._bd.create_image(0, 0, anchor="nw", image=ph)
            self._bd.tag_lower(self._bd_item) if hasattr(self._bd, "tag_lower") else None
        else:
            self._bd.itemconfigure(self._bd_item, image=ph)

    def _bd_go(self, to, dur):
        if self._bd is None:
            return
        self._bd_from, self._bd_to, self._bd_t0, self._bd_dur = self._bd_lvl, to, time.time(), dur
        if not self.settings.get("animations", True):
            self._bd_lvl = to
            self._bd_show(to)
            if to == 0:
                self._bd_kill()
            return
        self.sheet_anim()

    def _bd_kill(self):
        if self._bd is not None and not self.sheets:
            self._bd.destroy()
            self._bd = None
            self._bd_frames = {}
            self._bd_raw = self._bd_final = None
            self.redraw()

    def _bd_click(self, e):
        if not self.sheets:
            return
        top = self.sheets[-1]
        if top.contains(e.x, e.y):
            return
        if top._dismiss:
            fn = top._keys.get("<Escape>")
            fn(e) if fn else top.destroy()

    def sheet_card(self, w, h):
        """Rounded panel + soft shadow drawn behind a sheet (frames can't round corners)."""
        if not HAS_PIL:
            return None
        P, SH, R = Sheet.PAD, Sheet.SH, Sheet.RAD
        k = (w, h, SURFACE, LINE)
        cache = self.__dict__.setdefault("_cards", {})
        if k in cache:
            return cache[k]
        from PIL import ImageFilter
        W, H = w + 2 * (P + SH), h + 2 * (P + SH)
        a = Image.new("L", (W, H), 0)
        ImageDraw.Draw(a).rounded_rectangle((SH, SH + 12, W - SH, H - SH + 12), R, fill=175)
        a = a.filter(ImageFilter.GaussianBlur(SH / 2.0))
        im = Image.merge("RGBA", (Image.new("L", (W, H), 0),) * 3 + (a,))
        ss = 2
        big = Image.new("RGBA", (W * ss, H * ss), (0, 0, 0, 0))
        ImageDraw.Draw(big).rounded_rectangle(
            (SH * ss, SH * ss, (W - SH) * ss - 1, (H - SH) * ss - 1), R * ss,
            fill=_rgb(SURFACE) + (255,), outline=_rgb(mix(LINE, "#ffffff", 0.08)) + (255,),
            width=ss)
        # light catching the top edge of the panel
        fade = Image.new("L", (1, H * ss), 0)
        top_px = SH * ss
        fade.putdata([max(0, 120 - int(120 * max(0, y - top_px) / (H * ss * 0.35)))
                      for y in range(H * ss)])
        edge = Image.new("L", (W * ss, H * ss), 0)
        ImageDraw.Draw(edge).rounded_rectangle(
            (SH * ss, SH * ss, (W - SH) * ss - 1, (H - SH) * ss - 1), R * ss, outline=255,
            width=ss)
        edge = ImageChops.multiply(edge, fade.resize((W * ss, H * ss)))
        big = Image.composite(Image.new("RGBA", big.size, (255, 255, 255, 255)), big, edge)
        im = Image.alpha_composite(im, big.resize((W, H), Image.LANCZOS))
        if len(cache) > 24:
            cache.clear()
        cache[k] = ImageTk.PhotoImage(im)
        return cache[k]

    def sheet_anim(self):
        if not self._sheet_loop:
            self._sheet_loop = True
            self.after(1, self._sheet_tick)

    def _sheet_tick(self):
        self._sheet_loop = False
        now = time.time()
        more = False
        if self._bd is not None and self._bd_lvl != self._bd_to:
            k = ease_out((now - self._bd_t0) / self._bd_dur)
            self._bd_lvl = self._bd_from + (self._bd_to - self._bd_from) * k
            if k >= 1:
                self._bd_lvl = self._bd_to
            self._bd_show(self._bd_lvl)
            if self._bd_lvl == 0 and not self.sheets:
                self._bd_kill()
            else:
                more = more or self._bd_lvl != self._bd_to
        for sh in list(self.sheets) + [c for c in self.winfo_children()
                                       if isinstance(c, Sheet) and c._closing]:
            try:
                more = sh.step(now) or more
            except tk.TclError:
                pass
            except Exception as e:      # never let one dialog freeze the others
                self.log(f"sheet anim: {e!r}")
                try:
                    sh._vis = sh._to
                    sh._apply()
                    if sh._closing:
                        sh._final()
                except Exception:
                    pass
        if more:
            self._sheet_loop = True
            self.hold_fine_timer()
            self.after(16, self._sheet_tick)

    def _sheets_relayout(self):
        for sh in self.sheets:
            sh._layout()

    def route_key(self, seq):
        if seq not in self._routed:
            self._routed.add(seq)
            self.bind(seq, lambda e, s=seq: self._route(s, e))

    def key(self, seq, fn):
        self._appkeys[seq] = fn
        self.route_key(seq)

    def _route(self, seq, e):
        if self.sheets:
            top = self.sheets[-1]
            fn = top._keys.get(seq)
            if fn is None and seq == "<Escape>" and top._dismiss:
                fn = lambda ev: top.destroy()
            if fn:
                fn(e)
            return "break"
        if self.pop and seq in ("<Escape>", "<Up>", "<Down>", "<Return>"):
            self.pop_key(seq)
            return "break"
        if self.layers:
            top = self.top_layer()
            if top and top.on_key(seq, e):
                return "break"
            return None          # pages don't react to keys under a dialog
        fn = self._appkeys.get(seq)
        if fn:
            return fn(e)

    # ------------------------------------------------------------ popover menus
    def popmenu(self, items, x, y, anchor="nw"):
        """Animated in-app menu. items: dicts {label, fn, icon, check, disabled, danger, hint}
        or None for a divider. (x, y) are canvas coordinates."""
        self.pop = {"items": items, "x": x, "y": y, "anchor": anchor, "t0": time.time(),
                    "sel": -1}
        self._pop_xy = (x, y, anchor)
        self.redraw()

    def close_pop(self):
        if self.pop:
            self._pop_closing = dict(self.pop, tc=time.time())
            self.pop = None
            self.redraw()

    def pop_key(self, seq):
        p = self.pop
        idx = [i for i, it in enumerate(p["items"]) if it and not it.get("disabled")]
        if seq == "<Escape>" or not idx:
            self.close_pop()
            return
        if seq == "<Return>":
            if p["sel"] in idx:
                self._pop_run(p["sel"])
            return
        cur = idx.index(p["sel"]) if p["sel"] in idx else (-1 if seq == "<Down>" else 0)
        p["sel"] = idx[(cur + (1 if seq == "<Down>" else -1)) % len(idx)]
        self.redraw()

    def _pop_run(self, i):
        it = self.pop["items"][i] if self.pop else None
        if self.pop:
            self._pop_closing = dict(self.pop, tc=time.time(), picked=i)
        self.pop = None
        self.redraw()
        if it and it.get("fn") and not it.get("disabled"):
            self.hold_fine_timer()
            self.after(15, it["fn"])

    def draw_pop(self, w, h):
        p = self.pop
        closing = False
        if not p:
            p = getattr(self, "_pop_closing", None)
            if not p or not self.settings.get("animations", True) or \
                    time.time() - p["tc"] > 0.13:
                self._pop_closing = None
                return
            closing = True
        items = p["items"]
        RH, SEP, PADV = 34, 11, 7
        width = 230
        for it in items:
            if it:
                lw = self.measure(it["label"], 10, "bold") + 64
                if it.get("hint"):
                    lw += self.measure(it["hint"], 8) + 16
                width = max(width, lw)
        width = min(width, 360)
        height = PADV * 2 + sum(RH if it else SEP for it in items)
        x, y = p["x"], p["y"]
        if "s" in p["anchor"]:
            y -= height
        if p["anchor"] in ("s", "n"):
            x -= width / 2
        elif "e" in p["anchor"]:
            x -= width
        x = max(8, min(x, w - width - 8))
        y = max(8, min(y, h - height - 8))
        anim = self.settings.get("animations", True)
        k = ease_out((time.time() - p["t0"]) / 0.17) if anim else 1
        if closing:
            k = min(k, 1 - ease_in_out((time.time() - p["tc"]) / 0.13))
            self._ovl_more = True
        if k < 1:
            self._ovl_more = True
        dy = (1 - k) * (8 if "s" in p["anchor"] else -8)
        y += dy
        base = mix(BG, SURFACE, 0.4)
        fill = mix(base, mix(SURFACE, CARD, 0.5), 0.35 + 0.65 * k)
        self.soft(x, y, x + width, y + height, 14, "#000000", int(150 * round(k * 4) / 4), 18, 9, keep=True)
        self.rrect(x, y, x + width, y + height, 14, fill=fill,
                   outline=mix(fill, mix(LINE, "#ffffff", 0.1), k), depth=k)
        cy = y + PADV
        for i, it in enumerate(items):
            if not it:
                self.cv.create_line(x + 14, cy + SEP / 2, x + width - 14, cy + SEP / 2,
                                    fill=mix(fill, LINE, k))
                cy += SEP
                continue
            key = f"pop:{i}"
            dis = it.get("disabled")
            if closing:
                tags = ()
                hov = p.get("picked") == i
            else:
                tags = self.hit(key, click=(lambda i=i: self._pop_run(i)) if not dis else None,
                                box=(x + 5, cy, x + width - 5, cy + RH))
                hov = (self.hover == key or p["sel"] == i) and not dis
            hf = self.tween("pophv:" + key, 1.0 if hov else 0.0, 0.1 if hov else 0.16) if \
                not closing else (1.0 if hov else 0.0)
            if hf > 0.05:
                hc = mix(DANGER, fill, 0.72) if it.get("danger") else mix(ACCENT, fill, 0.55)
                self.rrect(x + 5, cy + 1, x + width - 5, cy + RH - 1, 9,
                           fill=mix(fill, hc, round(hf * 6) / 6), tags=tags, depth=0)
            col = DIM if dis else (DANGER if it.get("danger") and not hov else TEXT)
            col = mix(fill, col, k)
            if it.get("check") is not None:
                if it["check"]:
                    self.icon(x + 22, cy + RH / 2, "check", 10, mix(fill, GOOD if not dis else
                                                                   DIM, k), tags=tags)
            elif it.get("icon"):
                self.icon(x + 22, cy + RH / 2, it["icon"], 10,
                          mix(fill, col if hov or it.get("danger") else SOFT, k), tags=tags)
            self.text(x + 42, cy + RH / 2, it["label"], 10, "bold", col, tags=tags,
                      maxw=width - 60)
            if it.get("hint"):
                self.text(x + width - 14, cy + RH / 2, it["hint"], 8,
                          fill=mix(fill, DIM, k), anchor="e", tags=tags)
            cy += RH
        if not closing:
            p["box"] = (x, y, x + width, y + height)

    # ------------------------------------------------------------ overlays
    def draw_overlays(self):
        """Progress card, toasts and the loading bar live on their own layer so they can
        animate at ~30 fps without redrawing the whole page."""
        c = self.cv
        c.delete("ovl")
        base = getattr(self, "_hb_base", None)
        if base is not None:           # forget the last overlay frame's click areas
            del self.hit_boxes[base:]
        else:
            self._hb_base = len(self.hit_boxes)
        w, h = max(c.winfo_width(), 400), max(c.winfo_height(), 300)
        marker = (c.find_all() or (0,))[-1]
        self._ovl_more = False
        if self.busy or self.fetching or self.league_busy:
            top = h - self.BOTTOM
            span = w * 0.26
            pos = ease_in_out((time.time() * 0.62) % 1)
            xa = -span + pos * (w + span)
            self.soft(max(0, xa), top - 1, min(w, xa + span), top + 1, 1, ACCENT, alpha=170,
                      spread=6, dy=0)
            c.create_line(max(0, xa), top, min(w, xa + span), top, fill=ACCENT, width=2)
            c.create_line(max(0, xa + span * 0.25), top, min(w, xa + span * 0.75), top,
                          fill=ACCENT_HI, width=2)
            self._ovl_more = True
        self.draw_progress(w, h)
        self.draw_toasts(w, h)
        self.draw_tooltip(w, h)
        self.draw_pop(w, h)
        for item in c.find_all():
            if item > marker:
                c.addtag_withtag("ovl", item)
        if self._ovl_more and not self._ovl_loop:
            self._ovl_loop = True
            self.after(33, self._ovl_tick)

    def _ovl_tick(self):
        self._ovl_loop = False
        if self._pending:
            return  # a full redraw is coming anyway
        try:
            self.draw_overlays()
        except Exception as e:
            self.log(f"overlay: {e}")

    def draw_tooltip(self, w, h):
        k = self.hover
        if not k or self.pop or self.dragging or k.startswith("side:"):
            return
        tip = (self.hits.get(k) or {}).get("tip")
        if not tip:
            return
        age = time.time() - getattr(self, "hover_t", 0) - 0.45
        if age < 0:
            return
        a = min(1.0, age / 0.14) if self.settings.get("animations", True) else 1.0
        if a < 1:
            self._ovl_more = True
        mx, my = getattr(self, "mouse", (w / 2, h / 2))
        maxw = 320
        tw = min(maxw, self.measure(tip, 9, "bold")) + 24
        lines = 1 + int(self.measure(tip, 9, "bold") // maxw)
        th = 14 + 16 * lines
        x = min(max(8, mx + 14), w - tw - 8)
        y = my + 22 if my + 22 + th < h - 6 else my - th - 12
        y += (1 - a) * 4
        bg = mix(BG, mix(SURFACE, CARD_HI, 0.55), a)
        self.soft(x, y, x + tw, y + th, 10, alpha=int(150 * a), spread=10, dy=4, keep=True)
        self.rrect(x, y, x + tw, y + th, 10, fill=bg,
                   outline=mix(bg, mix(LINE, "#ffffff", 0.08), a), depth=a)
        self.cv.create_text(x + 12, y + th / 2, text=tip, anchor="w", width=maxw,
                            font=(self.UI, 9, "bold"), fill=mix(bg, TEXT, a))

    TOAST_LIFE = 5.0
    TOAST_LOOK = {"good": ("check", "GOOD"), "bad": ("warning", "DANGER"),
                  "wish": ("star_on", "GOLD"), "info": ("info", "ACCENT")}

    def draw_toasts(self, w, h):
        """Notifications: slide in from the right, stack and glide as others leave, pause
        while hovered, and dismiss on click. A thin line shows how long each has left."""
        now = time.time()
        anim = self.settings.get("animations", True)
        dt = now - getattr(self, "_toast_last", now)
        self._toast_last = now
        life = self.TOAST_LIFE
        mx, my = getattr(self, "mouse", (-1, -1))
        live = [t for t in self.toasts if now - t["t"] < life + 0.45]
        self.toasts = live
        if not live:
            return
        self._ovl_more = True
        x1 = w - 22
        ybase = h - self.BOTTOM - 16
        stack = 0.0
        for t in reversed(live):
            ic, cname = self.TOAST_LOOK.get(t["kind"], self.TOAST_LOOK["info"])
            col = globals()[cname]
            tw = min(440, self.measure(t["msg"], 10, "bold") + 78)
            th = 50
            age = now - t["t"]
            # slide/fade in (with a hint of overshoot) and out
            if not anim:
                k_in, k_out = 1.0, 0.0
            else:
                k_in = ease_out_back(min(1.0, age / 0.42), 0.9)
                k_out = ease_in_out(max(0.0, (age - life) / 0.42))
            vis = max(0.0, min(1.0, min(1.0, age / 0.2) * (1 - k_out)))
            ty_target = stack
            ty = self.tween(f"toast:y:{t['id']}", ty_target, 0.32, "out") if anim else ty_target
            stack += (th + 10) * (1 - k_out)
            xr = x1 + (1 - k_in) * (tw + 40) + k_out * 60
            yb = ybase - ty
            x0, y0 = xr - tw, yb - th
            hov = x0 <= mx <= xr and y0 <= my <= yb
            if hov and age < life:            # hovering holds it on screen
                t["t"] += dt
            key = f"toast:{t['id']}"
            self.hit(key, click=lambda t=t: t.update(t=time.time() - life), tip=None,
                     box=(x0, y0, xr, yb))
            bg = mix(BG, mix(SURFACE, col, 0.1), vis)
            self.soft(x0, y0, xr, yb, 14, "#000000", alpha=int(150 * vis), spread=14, dy=7, keep=True)
            if vis > 0.5:
                self.soft(x0, y0, xr, yb, 14, col, alpha=int(40 * vis), spread=10, dy=0)
            self.rrect(x0, y0, xr, yb, 14, fill=bg,
                       outline=mix(bg, mix(LINE, col, 0.45 + (0.2 if hov else 0)), vis),
                       depth=1.0)
            cx, cy = x0 + 26, y0 + th / 2
            self.circle(cx, cy, 13, fill=mix(bg, mix(SURFACE, col, 0.28), vis), depth=0)
            self.icon(cx, cy, ic, 9, mix(bg, col, vis))
            self.text(x0 + 48, cy, t["msg"], 10, "bold", mix(bg, TEXT, vis), maxw=tw - 62)
            left = max(0.0, 1 - age / life)
            if left > 0 and vis > 0.3:
                lw = (tw - 28) * left
                self.rrect(x0 + 14, yb - 4, x0 + 14 + max(3, lw), yb - 2, 1, depth=0,
                           fill=mix(bg, col, 0.55 * vis))

    def draw_progress(self, w, h):
        p = self.progress
        if not p:
            return
        pw, ph = 380, 84 + 26 * len(p["steps"])
        x0 = (self.SIDE + w) / 2 - pw / 2
        y0 = 24
        age = time.time() - p.get("t0", 0)
        if self.settings.get("animations", True) and age < 0.3:
            y0 -= (1 - age / 0.3) ** 3 * (ph + 30)
        self._ovl_more = True
        col = DANGER if p.get("error") else (GOOD if p.get("done") else ACCENT)
        ph = self.tween("prog:h", ph, 0.25)
        self.soft(x0, y0, x0 + pw, y0 + ph, 18, alpha=160, spread=18, dy=10, keep=True)
        self.soft(x0, y0, x0 + pw, y0 + ph, 18, col, alpha=45, spread=12, dy=0)
        self.rrect(x0, y0, x0 + pw, y0 + ph, 18, fill=SURFACE, outline=mix(SURFACE, col, 0.5),
                   depth=1.0)
        n = max(1, len(p["steps"]))
        done_f = 1.0 if p.get("done") else min(1.0, (p["i"] + 0.5) / n)
        fr = self.tween("prog:f", done_f, 0.5, "quint")
        if fr > 0:
            self.rrect(x0 + 18, y0 + ph - 7, x0 + 18 + (pw - 36) * fr, y0 + ph - 4, 1.5, depth=0,
                       fill=mix(SURFACE, col, 0.85))
        name = p.get("name")
        if name:
            self.account_art(x0 + 18, y0 + 16, 40, name, 10)
        self.text(x0 + 70, y0 + 28, p["title"], 12, "bold", maxw=pw - 90)
        self.text(x0 + 70, y0 + 47, p.get("error") or p.get("sub", ""), 9,
                  fill=DANGER if p.get("error") else MUTED, maxw=pw - 90)
        y = y0 + 84
        for i, s in enumerate(p["steps"]):
            if i < p["i"] or p.get("done"):
                pop_ = self.tween_from(f"prog:ok:{id(p)}:{i}", 0.4, 1.0, 0.35, "back")
                self.circle(x0 + 30, y, 8 * pop_, fill=GOOD)
                if pop_ > 0.7:
                    self.icon(x0 + 30, y, "check", 7, BG)
                fg = MUTED
            elif i == p["i"] and not p.get("error"):
                self.circle(x0 + 30, y, 8, fill="", outline=mix(SURFACE, ACCENT, 0.45), width=2)
                a = -(time.time() * 300) % 360
                self.cv.create_arc(x0 + 22, y - 8, x0 + 38, y + 8, start=a, extent=110,
                                   style="arc", outline=SOFT, width=2)
                fg = TEXT
            else:
                self.circle(x0 + 30, y, 8, fill="", outline=DIM)
                fg = DIM
            self.text(x0 + 48, y, s, 10, "bold" if i == p["i"] else "normal", fg)
            y += 26

    def start_progress(self, title, steps, name=None, sub=""):
        self.progress = {"title": title, "steps": steps, "i": 0, "name": name, "sub": sub,
                         "t0": time.time()}
        self._tick()
        self.redraw()

    def step(self, i, sub=None):
        def apply():
            if self.progress:
                self.progress["i"] = i
                if sub is not None:
                    self.progress["sub"] = sub
                self.redraw()
        self.call_ui(apply)

    def end_progress(self, error=None, delay=1.6):
        def apply():
            if not self.progress:
                return
            if error:
                self.progress["error"] = error
            else:
                self.progress["done"] = True
            p = self.progress
            self.after(int((4 if error else delay) * 1000),
                       lambda: (setattr(self, "progress", None) if self.progress is p else None,
                                self.redraw()))
            self.redraw()
        self.call_ui(apply)

    # ------------------------------------------------------------ sidebar / bottom
    def chrome_photo(self, kind, w, h):
        """Shaded panels for the sidebar and bottom bar (cached per size and theme)."""
        if not HAS_PIL:
            return None
        key = (kind, w, h, BAR, LINE, ACCENT)
        cache = self.__dict__.setdefault("_chrome", {})
        if key in cache:
            return cache[key]
        if len(cache) > 12:
            cache.clear()
        try:
            if kind == "side":
                im = _vgrad(w, h, mix(BAR, "#ffffff", 0.018), mix(BAR, "#000000", 0.18))
                d = ImageDraw.Draw(im)
                d.line((w - 1, 0, w - 1, h), fill=_rgb(mix(BAR, LINE, 0.75)) + (255,))
                # a faint accent haze behind the logo
                haze = Image.new("L", (w, h), 0)
                ImageDraw.Draw(haze).ellipse((-w * 0.6, -60, w * 1.6, 150), fill=34)
                haze = haze.filter(ImageFilter.GaussianBlur(28))
                im = Image.composite(Image.new("RGBA", (w, h), _rgb(ACCENT) + (255,)), im, haze)
            else:
                im = _vgrad(w, h, mix(BAR, "#ffffff", 0.025), mix(BAR, "#000000", 0.25))
                d = ImageDraw.Draw(im)
                d.line((0, 0, w, 0), fill=_rgb(mix(BAR, LINE, 0.9)) + (255,))
                glow = Image.new("L", (w, h), 0)
                ImageDraw.Draw(glow).ellipse((w * 0.32, -h * 0.9, w * 0.68, h * 0.55), fill=26)
                glow = glow.filter(ImageFilter.GaussianBlur(30))
                im = Image.composite(Image.new("RGBA", (w, h), _rgb(ACCENT) + (255,)), im, glow)
                d = ImageDraw.Draw(im)
                d.line((0, 1, w, 1), fill=_rgb(mix(BAR, "#ffffff", 0.05)) + (255,))
            cache[key] = ImageTk.PhotoImage(im.convert("RGB"))   # opaque: no blending
        except Exception:
            cache[key] = None
        return cache[key]

    def side_positions(self, h):
        """Nav item y positions - spaced to fit, so short windows never overlap Settings."""
        n = len(self.PAGES)
        settings_y = h - self.BOTTOM - 40
        step = max(44, min(58, (settings_y - 70 - 110) / max(1, n - 1)))
        ys = {p: 110 + i * step for i, (p, _, _) in enumerate(self.PAGES)}
        ys["settings"] = settings_y
        return ys

    def draw_sidebar(self, w, h):
        S = self.SIDE
        bg = self.chrome_photo("side", S, h - self.BOTTOM)
        if bg:
            self.cv.create_image(0, 0, image=bg, anchor="nw")
        else:
            self.cv.create_rectangle(0, 0, S, h, fill=BAR, outline="")
            self.cv.create_line(S, 0, S, h - self.BOTTOM, fill=mix(BAR, LINE, 0.6))
        logo = self.logo_photo(40)
        lk = "side:logo"
        ltags = self.hit(lk, click=lambda: self.set_page("home"), tip=APP_TITLE)
        lf = self.hv(lk)
        if logo:
            self.soft(S / 2 - 20, 24, S / 2 + 20, 64, 13, ACCENT, int(90 + 60 * lf), 10, 4)
            self.cv.create_image(S / 2, 42 - round(1.5 * lf), image=logo, tags=ltags)
        else:
            self.rrect(S / 2 - 20, 22, S / 2 + 20, 62, 13, fill=ACCENT, tags=ltags)
            self.icon(S / 2, 42, "compare", 15, "#ffffff", tags=ltags)
        tip_draw = None
        hits = self.store_hits()
        ys = self.side_positions(h)
        for p_, yy_ in ys.items():   # hit areas that don't depend on what's drawn on top
            self.hit_boxes.append(((S / 2 - 24, yy_ - 24, S / 2 + 24, yy_ + 24), "side:" + p_))
            self.hit("side:" + p_, click=lambda p=p_: self.set_page(p))
        if self.page in ys:
            ay = self.tween("side:y", ys[self.page], 0.42, "back")
            self.soft(S / 2 - 22, ay - 22, S / 2 + 22, ay + 22, 14, ACCENT, alpha=70, spread=10,
                      dy=2)
            self.rrect(S / 2 - 22, ay - 22, S / 2 + 22, ay + 22, 14,
                       fill=mix(CARD_HI, ACCENT, 0.18), depth=1.0)
            self.soft(0, ay - 12, 4, ay + 12, 2, ACCENT, alpha=170, spread=6, dy=0)
            self.rrect(0, ay - 12, 4, ay + 12, 2, fill=ACCENT_HI, depth=0)
        items = [(p, ic, f"{tip}   Ctrl+{i + 1}") for i, (p, ic, tip) in enumerate(self.PAGES)]
        items.append(("settings", "settings", "Settings"))
        for page, ic, tip in items:
            y = ys[page]
            key = "side:" + page
            hov = self.hover == key
            cur = self.page == page
            tags = self.hit(key, click=lambda p=page: self.set_page(p), tip=tip)
            f = self.hv(key)
            pr = self.pressed(key)
            if not cur and (f > 0 or pr):
                self.rrect(S / 2 - 22 + pr, y - 22 + pr, S / 2 + 22 - pr, y + 22 - pr, 14,
                           fill=mix(mix(BAR, CARD, f), SURFACE, 0.4 * pr), depth=0.6 * f,
                           tags=tags)
            lift = 0 if cur else round(1.5 * f - pr, 1)
            self.icon(S / 2, y - lift, ic, 15,
                      TEXT if cur else self.hcol(key, MUTED, TEXT), tags=tags)
            badge = None
            if page == "home":
                badge = (str(len(self.accounts())), ACCENT)
            elif page == "store" and hits:
                badge = (str(len(hits)), GOLD)
            elif page == "live" and self.queueing():
                e = int(queue_elapsed(self.live))
                badge = (f"{e // 60}:{e % 60:02d}", ACCENT_HI)
                self._more = True
            elif page == "live" and (self.live or {}).get("phase") in ("pregame", "ingame"):
                badge = ("●", GOOD)
            if badge:
                n, col = badge
                bw = max(16, self.measure(n, 8, "bold") + 10)
                bx = S / 2 + 4
                step = ys.get("social", 0) - ys.get("compare", 0) if "social" in ys else 58
                by = y - min(18, step / 2 - 9) - lift      # stays inside its own slot
                self.rrect(bx - 2, by - 10, bx + bw + 2, by + 10, 10, fill=BAR, depth=0)
                self.rrect(bx, by - 8, bx + bw, by + 8, 8, fill=col, depth=0.8)
                self.text(bx + bw / 2, by, n, 8, "bold", BG if col == GOLD else "#ffffff",
                          anchor="center")
            if hov:
                tip_draw = (y, tip)
        if self.streamer():
            self.icon(S / 2, h - self.BOTTOM - 92, "eye_off", 13, GOLD)
        # nav label: slides out from the bar and fades in
        st = self.tween("sidetip", 1.0 if tip_draw else 0.0, 0.16 if tip_draw else 0.1)
        if tip_draw:
            self._side_tip = tip_draw
        if st > 0.02 and getattr(self, "_side_tip", None):
            ty, tip = self._side_tip
            tw = self.measure(tip, 9, "bold") + 22
            tx = S + 4 + round(6 * st)
            bgc = mix(BG, mix(SURFACE, CARD_HI, 0.6), st)
            self.soft(tx, ty - 15, tx + tw, ty + 15, 9, "#000000", alpha=int(140 * st),
                      spread=10, dy=4)
            self.rrect(tx, ty - 15, tx + tw, ty + 15, 9, fill=bgc,
                       outline=mix(bgc, mix(LINE, "#ffffff", 0.08), st), depth=0)
            self.text(tx + 11, ty, tip, 9, "bold", mix(bgc, TEXT, st))

    def draw_bottom(self, w, h):
        B = self.BOTTOM
        top = h - B
        bg = self.chrome_photo("bottom", w, B)
        if bg:
            self.cv.create_image(0, top, image=bg, anchor="nw")
        else:
            self.cv.create_rectangle(0, top, w, h, fill=BAR, outline="")
            self.cv.create_line(0, top, w, top, fill=LINE)
        mid = top + B / 2

        active = self.state_.get("active")
        if active and active in self.accounts():
            key = "bot:active"
            tags = self.hit(key, click=lambda: self.open_profile(active),
                            tip="Open profile")
            f = self.hv(key)
            if f > 0:
                self.soft(22, mid - 24, 70, mid + 24, 24, ACCENT, alpha=int(90 * f), spread=10,
                          dy=2, tags=tags)
            self.account_art(22, mid - 24, 48, active, 24, tags=tags)
            m = self.m(active)
            # signed-in dot on the avatar
            self.circle(62, mid + 16, 7.5, fill=BAR, depth=0, tags=tags)
            self.circle(62, mid + 16, 5, fill=GOOD, depth=0, tags=tags)
            self.text(84, mid - 10, active, 12, "bold", maxw=220, tags=tags,
                      fill=self.hcol(key, TEXT, "#ffffff"))
            sub = self.rank_text(m) or "Logged in"
            since = self.state_.get("active_since")
            if since:
                sub += f"  ·  on for {dur(time.time() - since)}"
            self.text(84, mid + 12, sub, 9, fill=SOFT, maxw=230, tags=tags)
        else:
            self.circle(46, mid, 24, fill=CARD)
            self.icon(46, mid, "person", 13, DIM)
            self.text(84, mid - 10, "No account active", 12, "bold")
            self.text(84, mid + 12, "Pick an account to log in", 9, fill=MUTED)

        cx = w / 2
        key = "bot:login"
        sel = self.selected if self.selected in self.accounts() else None
        act = self.state_.get("active")
        g = self.m(act).get("default_game") or self.state_["game"]
        if not GAMES.get(g):
            g = "VALORANT"
        prod = GAMES.get(g)
        running = prod in self.running_games
        starting = prod in self.launching and not running
        if self.page in ("play", "live", "store", "social", "sync") or not sel or sel == act:
            label = (f"{g} running" if running else "Starting…" if starting else f"Play {g}")
            fn = (lambda g=g: self.play_game(g)) if act else self.add_new
            if not act:
                label = "Add an account"
            tip = f"Play {g} on {self.play_account()}" if act else None
        else:
            label, fn, tip = f"Switch to {sel}", (lambda: self.switch(self.selected)), None
        if self.busy:
            label = "Working…"
        hov = self.hover == key and not self.busy
        tags = self.hit(key, click=None if self.busy or running else fn, tip=tip)
        pw = self.tween("bot:pw", max(170, self.measure(label, 11, "bold") + 76), 0.3, "back")
        f = self.hv(key, hov)
        pr = self.pressed(key) if not (self.busy or running) else 0
        col = (mix(SURFACE, GOOD, 0.4) if running else mix(DIM, ACCENT, 0.25) if self.busy else
               mix(ACCENT, ACCENT_HI, f))
        if starting or self.busy:
            ph = 0.5 + 0.5 * math.sin(time.time() * 4.2)
            col = mix(ACCENT, ACCENT_HI, ph) if starting else mix(mix(DIM, ACCENT, 0.25), ACCENT,
                                                                   0.35 * ph)
            self._more = True
        if not running:
            self.soft(cx - pw / 2, mid - 24, cx + pw / 2, mid + 24, 24, ACCENT,
                      alpha=int(55 + 95 * f - 40 * pr), spread=14, dy=int(4 + 2 * f), tags=tags)
        ins = 2 * pr
        self.rrect(cx - pw / 2 + ins, mid - 24 + ins, cx + pw / 2 - ins, mid + 24 - ins + 0.5 * pr,
                   24, fill=col, tags=tags, depth=1.0 - 0.5 * pr)
        lw = self.measure(label, 11, "bold")
        dy = 0.5 * pr
        if self.busy:
            a = -(time.time() * 320) % 360
            self.cv.create_arc(cx - lw / 2 - 18, mid - 8 + dy, cx - lw / 2 - 2, mid + 8 + dy,
                               start=a, extent=250, style="arc", outline="#ffffff", width=2,
                               tags=tags)
        else:
            self.icon(cx - lw / 2 - 10, mid + dy, "check" if running else "play", 12, "#ffffff",
                      tags=tags)
        self.text(cx + 10, mid + dy, label, 11, "bold", "#ffffff", anchor="center", tags=tags)

        # right: presence status chip + game + message
        mode = self.settings.get("status_mode", "online")
        enabled = self.offline_on()
        dot = {"online": GOOD, "offline": DIM, "mobile": GOLD}[mode]
        label = ("Appear " + STATUS_MODES[mode].lower()) if enabled else "Offline mode: off"
        key = "bot:status"
        hov = self.hover == key
        tw = self.measure(label, 10, "bold") + 64
        tags = self.hit(key, click=self.status_menu,
                        tip="Offline mode: click to turn on/off or change status")
        x1 = w - 22
        pr = self.pressed(key)
        self.rrect(x1 - tw + pr, mid - 15 + pr, x1 - pr, mid + 15 - pr, 15,
                   fill=mix(CARD, ACCENT, 0.25) if enabled else (self.hcol(key, CARD, CARD_HI, hov)),
                   outline=ACCENT if enabled else mix(LINE, CARD_HI, self.hv(key)), tags=tags,
                   depth=0.8)
        self.icon(x1 - tw + 18, mid, "moon", 10, SOFT if enabled else MUTED, tags=tags)
        if enabled:
            self.soft(x1 - tw + 32, mid - 4, x1 - tw + 40, mid + 4, 4, dot, alpha=150, spread=5,
                      dy=0, tags=tags)
        self.circle(x1 - tw + 36, mid, 4, fill=dot if enabled else DIM, tags=tags)
        self.text(x1 - tw + 46, mid, label, 10, "bold",
                  TEXT if enabled else self.hcol(key, MUTED, TEXT), tags=tags)
        status = self.status if time.time() < self.status_until else ""
        if not status and self.running_games:
            names = [g for g, p in GAMES.items() if p in self.running_games]
            status = f"{', '.join(names)} running" if names else ""
        # status line sits between the Play button and the offline pill, fading in and out
        room = (x1 - tw - 18) - (cx + 130)
        if status:
            self._bot_status = status
        a = self.tween("bot:status", 1.0 if status else 0.0, 0.25 if status else 0.4)
        msg = getattr(self, "_bot_status", "")
        if msg and a > 0.02 and room > 90:
            self.text(x1 - tw - 18, mid + round(3 * (1 - a)), msg, 9, fill=mix(BAR, MUTED, a),
                      anchor="e", maxw=room)

    def offline_on(self):
        return bool(self.settings.get("status_enabled")
                    or self.settings.get("status_engine") == "deceive")

    def status_menu(self, x=None, y=None):
        on = self.offline_on()
        cur = self.settings.get("status_mode", "online")
        deceive = self.settings.get("status_engine") == "deceive"
        items = [{"label": "Offline mode is on" if on else "Offline mode is off",
                  "check": on, "hint": "click to turn " + ("off" if on else "on"),
                  "fn": self.toggle_offline_mode}, None]
        for k, label in STATUS_MODES.items():
            items.append({"label": f"Appear {label.lower()}", "check": k == cur,
                          "fn": lambda k=k: self.quick_status(k), "disabled": not on})
        items += [None,
                  {"label": "RiotHub friend in chat",
                   "check": bool(self.settings.get("chat_control", True)), "disabled": deceive,
                   "fn": lambda: self.toggle("chat_control")},
                  {"label": "Use Deceive.exe instead", "check": deceive,
                   "fn": self.toggle_deceive_engine}]
        if on and not self.proxy.connected and self.state_.get("active") and not deceive:
            items += [None, {"label": "Apply now (relaunch Riot Client)", "icon": "refresh",
                             "fn": lambda: self.switch(self.state_.get("active"))}]
        items += [None, {"label": "More options…", "icon": "settings",
                         "fn": lambda: self.set_page("settings")}]
        if x is None:
            x = self.winfo_pointerx() - self.winfo_rootx()
            y = self.winfo_pointery() - self.winfo_rooty() - 16
        self.popmenu(items, x, y, anchor="s")

    def quick_status(self, mode):
        self.set_status_mode(mode)

    def toggle_offline_mode(self):
        if self.settings.get("status_engine") == "deceive":
            self.settings["status_engine"] = "builtin"
            self.settings["status_enabled"] = False
            save_state(self.state_)
            self.toast("Offline mode off. Your next login is normal.")
            self.redraw()
            return
        val = not self.settings.get("status_enabled")
        self.settings["status_enabled"] = val
        if val and self.settings.get("status_mode") == "online":
            self.settings["status_mode"] = "offline"
            self.proxy.mode = "offline"
        save_state(self.state_)
        if val:
            active = self.state_.get("active")
            if active and not self.proxy.connected and not self.busy:
                if self.confirm("Offline mode on", "It takes effect when the Riot Client starts "
                                                   "through RiotHub. Relaunch it now?",
                                ok="Relaunch now", cancel="Later"):
                    self.switch(active)
                    return
            self.toast("Offline mode on. You'll appear offline from your next login.", "good")
        else:
            if self.proxy.connected:
                self.proxy.set_mode("online")
            self.toast("Offline mode off. You appear online again.")
        if self.tray:
            try:
                self.tray.update_menu()
            except Exception:
                pass
        self.redraw()

    def toggle_deceive_engine(self):
        if self.settings.get("status_engine") == "deceive":
            self.settings["status_engine"] = "builtin"
            save_state(self.state_)
            self.toast("Using the built-in offline mode.")
        else:
            if not self.settings.get("deceive_path"):
                self.pick_deceive()
                if not self.settings.get("deceive_path"):
                    return
            self.settings["status_engine"] = "deceive"
            if self.settings.get("status_mode") == "online":
                self.settings["status_mode"] = "offline"
            save_state(self.state_)
            self.toast("Logins now launch through Deceive.", "good")
        self.redraw()

    # ------------------------------------------------------------ home
    def draw_home(self, w, h):
        show_right = w >= 1060
        x0 = self.SIDE + 36
        x1 = w - (self.RIGHT + 44 if show_right else 32)
        y = 30 - self.scroll()
        top = y
        names = self.accounts()
        full = list(names)
        self.page_header(x0, x1, y, "home", "Accounts")
        cx = x1
        lay = self.settings.get("layout", "grid")
        for val, ic in (("list", "list"), ("grid", "grid")):
            key = "layout:" + val
            on = lay == val
            hov = self.hover == key
            tags = self.hit(key, click=lambda v=val: self.set_setting("layout", v),
                            tip=f"{val.title()} view")
            self.rrect(cx - 34, y + 2, cx, y + 32, 10,
                       fill=ACCENT if on else (self.hcol(key, CARD, CARD_HI, hov)), tags=tags)
            self.icon(cx - 17, y + 17, ic, 11, TEXT if on else self.hcol(key, MUTED, TEXT, hov), tags=tags)
            cx -= 40
        cx -= 10
        on = self.offline_on()
        lab = "Offline mode on" if on else "Offline mode off"
        tw = self.measure(lab, 10, "bold") + 84
        key = "home:offline"
        hov = self.hover == key
        tags = self.hit(key, click=self.toggle_offline_mode,
                        right=lambda e: self.status_menu(),
                        tip="Click to turn offline mode on/off · right-click for options")
        self.rrect(cx - tw, y + 2, cx, y + 32, 15,
                   fill=mix(CARD, ACCENT, 0.35) if on else (self.hcol(key, CARD, CARD_HI, hov)),
                   outline=ACCENT if on else "", tags=tags)
        self.icon(cx - tw + 18, y + 17, "moon", 10, SOFT if on else MUTED, tags=tags)
        self.toggle_switch(cx - 38, y + 17, on, key, tags, w=30, h=18)
        self.text(cx - tw + 32, y + 17, lab, 10, "bold", TEXT if on else self.hcol(key, MUTED, TEXT, hov), tags=tags)
        cx -= tw + 18
        game = self.state_["game"]
        lab = game if GAMES.get(game) else "Client only"
        tw = self.measure(lab, 10, "bold") + 62
        key = "home:game"
        hov = self.hover == key
        tags = self.hit(key, click=lambda x=cx - tw / 2, yy=y + 38: self.game_menu(x, yy),
                        tip="Which game opens after you log in")
        self.rrect(cx - tw, y + 2, cx, y + 32, 15, fill=self.hcol(key, ACCENT, ACCENT_HI, hov), tags=tags)
        self.icon(cx - tw + 18, y + 17, "game", 10, "#ffffff", tags=tags)
        self.text(cx - tw + 32, y + 17, lab, 10, "bold", tags=tags)
        self.text(cx - 16, y + 17, "▾", 9, "bold", tags=tags, anchor="center")
        y += 62

        extra = f"{len(names)} saved" + ("  ·  drag to reorder" if len(names) > 1 else "")
        self.section(x0, y, "bolt", "Your accounts", extra)
        if len(names) > 3:
            self.place_search(x1, y + 12, 200, "Filter accounts")
        archived = [n for n in names if self.m(n).get("archived")]
        if not self.show_archived:
            names = [n for n in names if not self.m(n).get("archived")]
        else:
            names = archived
        tags = sorted({t for n in full for t in (self.m(n).get("tags") or [])}, key=str.lower)
        n_ready = sum(1 for n in full if ranked_status(self.m(n))[0] == "ready")
        if tags or archived or n_ready:
            y += 34
            opts = [("", "All")] + ([(self.RANKED_CHIP, f"Ranked ready ({n_ready})")]
                                    if n_ready else []) + [(t, t) for t in tags[:10]]
            cx = self.chips(x0, y, opts, self.tag_filter, self.set_tag_filter, "tagf", size=8,
                            h=24)
            if archived:
                key = "archived"
                hov = self.hover == key
                lab = f"Archived ({len(archived)})"
                tw = self.measure(lab, 8, "bold") + 28
                tg = self.hit(key, click=self.flip_archived)
                self.rrect(cx + 6, y, cx + 6 + tw, y + 24, 12,
                           fill=ACCENT if self.show_archived else (self.hcol(key, CARD, CARD_HI, hov)),
                           tags=tg)
                self.text(cx + 6 + tw / 2, y + 12, lab, 8, "bold", TEXT, anchor="center", tags=tg)
            y -= 4
        if self.tag_filter == self.RANKED_CHIP:
            names = [n for n in names if ranked_status(self.m(n))[0] == "ready"]
        elif self.tag_filter:
            names = [n for n in names if self.tag_filter in (self.m(n).get("tags") or [])]
        q = self.search_var.get().strip().lower()
        if q:
            def match(n):
                m = self.m(n)
                hay = " ".join([n, m.get("game_name") or "", " ".join(m.get("tags") or []),
                                ASSETS.tier_name(m.get("tier")) if m.get("tier") else ""])
                return q in hay.lower()
            names = [n for n in names if match(n)]
        y += 40
        self.tile_slots = []
        if lay == "list":
            for i, name in enumerate(names):
                self.draw_row(x0, y, x1 - x0, name, full.index(name))
                self.tile_slots.append((name, x0, y))
                y += 70
            self.draw_add_row(x0, y, x1 - x0)
            y += 76
        else:
            T, gap = self.TILE, 30
            rowh = T + self.TILE_INFO + self.TILE_PAD + 20
            y += self.TILE_PAD
            x0 += self.TILE_PAD
            cols = max(1, int((x1 - x0 - self.TILE_PAD + gap) // (T + gap)))
            items = names + ["__add__"]
            for i, name in enumerate(items):
                tx = x0 + (i % cols) * (T + gap)
                ty = y + (i // cols) * rowh
                if name == "__add__":
                    self.draw_add_tile(tx, ty, T)
                else:
                    self.tile_slots.append((name, tx, ty))
                    self.draw_tile(tx, ty, T, name, full.index(name))
            y += ((len(items) - 1) // cols + 1) * rowh - 4
            x0 -= self.TILE_PAD

        hits = self.store_hits()
        if hits:
            self.section(x0, y, "star_on", "Wishlist alert",
                         f"{len(hits)} wanted skin{'s' if len(hits) > 1 else ''} in store now")
            y += 40
            hx = x0
            for skin, acc, price in hits[:6]:
                s = ASSETS.skins.get(skin)
                if not s:
                    continue
                key = f"hit:{acc}:{skin}"
                hov = self.hover == key
                tags = self.hit(key, click=lambda a=acc: (self.select(a), self.set_page("store")))
                ww = 250
                if hx + ww > x1:
                    break
                self.rrect(hx, y, hx + ww, y + 76, 14, fill=mix(SURFACE, GOLD, (0.07 + (0.12 - 0.07) * self.hv(key, hov))),
                           outline=GOLD, tags=tags)
                self.image(s["icon"], hx + 12, y + 12, 96, 52, tags=tags)
                self.text(hx + 118, y + 26, s["name"], 10, "bold", maxw=ww - 128, tags=tags)
                self.text(hx + 118, y + 46, f"{acc}  ·  {price or '?'} VP", 9, fill=GOLD,
                          maxw=ww - 128, tags=tags)
                hx += ww + 12
            y += 92

        self.section(x0, y, "rocket", "Quick actions")
        y += 40
        actions = [
            ("save", "Save current login", "Save whoever's signed in now", self.save_current),
            ("game", "Launch game", "Open the selected game, no switch", self.launch_only),
            ("refresh", "Refresh stats", "Reload everything for the active account",
             lambda: self.refresh_stats(self.state_.get("active"))),
        ]
        ncol = 3 if (x1 - x0) >= 720 else 1
        rw = ((x1 - x0) - (ncol - 1) * 14) / ncol
        for i, (ic, title, sub, fn) in enumerate(actions):
            rx = x0 + (i % ncol) * (rw + 14)
            ry = y + (i // ncol) * 70
            key = "act:" + title
            hov = self.hover == key
            tags = self.hit(key, click=fn)
            f = self.hv(key, hov)
            pr = self.pressed(key)
            lift = round(2 * f - pr, 1)
            ry -= lift
            self.soft(rx, ry, rx + rw, ry + 58, 14, "#000000", alpha=int(60 + 50 * f),
                      spread=10, dy=int(4 + 3 * f), tags=tags)
            if f > 0:
                self.soft(rx, ry, rx + rw, ry + 58, 14, ACCENT, alpha=int(70 * f), spread=10,
                          dy=2, tags=tags)
            self.rrect(rx, ry, rx + rw, ry + 58, 14,
                       fill=self.hcol(key, mix(SURFACE, CARD, 0.4), CARD_HI, hov), tags=tags,
                       outline=mix(LINE, mix(CARD_HI, SOFT, 0.15), f), depth=1.0)
            self.rrect(rx + 7, ry + 7, rx + 51, ry + 51, 10,
                       fill=self.hcol(key, CARD_HI, ACCENT, hov), tags=tags, depth=1.0)
            self.icon(rx + 29, ry + 29, ic, 14, TEXT, tags=tags)
            self.text(rx + 66, ry + 21, title, 11, "bold", maxw=rw - 76, tags=tags)
            self.text(rx + 66, ry + 40, sub, 9, fill=MUTED, maxw=rw - 76, tags=tags)
        y += ((len(actions) - 1) // ncol + 1) * 70
        self.finish_scroll(top, y, h)
        if show_right:
            self.draw_panel(w, h)

    def ranked_pill(self, name):
        """(label, fill, fg, tip) for the rank-ready pill, or None."""
        st, lab, tip = ranked_status(self.m(name))
        if st == "ready":
            return lab, mix(SURFACE, GOOD, 0.22), GOOD, tip
        if st == "level":
            return lab, CARD_HI, MUTED, tip
        if st == "blocked":
            return lab, mix(SURFACE, DANGER, 0.25), "#ff9aa8", tip
        return None

    def tile_badges(self, name):
        """(label, fill, fg) badges for an account, most important first."""
        m = self.m(name)
        out = []
        if m.get("expired"):
            out.append(("Login expired", DANGER, "#ffffff"))
        if (m.get("penalties") or {}).get("items"):
            out.append(("Restricted", DANGER, "#ffffff"))
        if any(a == name for _, a, _ in self.store_hits()):
            out.append(("★ Wishlist in store", GOLD, BG))
        if self.state_.get("active") == name and not m.get("expired"):
            out.append(("● Logged in", "#0c0917", SOFT))
        last = self.state_["last_used"].get(name)
        if last and time.time() - last > 25 * 86400 and self.state_.get("active") != name:
            out.append(("May need re-login", "#3a2a10", GOLD))
        return out

    TILE_PAD, TILE_INFO = 8, 98   # profile card: padding around the art, info area below

    def tile_card(self, x, y, T, key, f, pr, sel_f=0.0, live=False, color=None, tags=()):
        """The card a tile sits on. Lifts on hover, sinks on press, glows when selected.
        Returns the vertical lift so the content can move with it."""
        P, IB = self.TILE_PAD, self.TILE_INFO
        lift = round(3 * f - 1.5 * pr, 1)
        x0, y0, x1, y1 = x - P, y - P - lift, x + T + P, y + T + IB - lift
        self.soft(x0, y0, x1, y1, 18, "#000000", alpha=int(80 + 50 * f), spread=14,
                  dy=int(6 + 5 * f), tags=tags)
        if sel_f > 0:
            self.soft(x0, y0, x1, y1, 18, ACCENT, alpha=int(105 * sel_f), spread=12, dy=2,
                      tags=tags)
        elif f > 0 and color:
            self.soft(x0, y0, x1, y1, 18, color, alpha=int(60 * f), spread=12, dy=4, tags=tags)
        fill = mix(mix(SURFACE, CARD, 0.32), CARD_HI, 0.22 * f)
        if pr:
            fill = mix(fill, SURFACE, 0.35 * pr)
        out = mix(mix(LINE, CARD_HI, 0.5 * f), ACCENT, sel_f) if sel_f else \
            mix(LINE, mix(CARD_HI, SOFT, 0.15), f)
        self.rrect(x0, y0, x1, y1, 18, fill=fill, outline=out, width=2 if sel_f > 0.5 else 1,
                   depth=1.0, tags=tags)
        if self.kbd_focus and sel_f >= 1:    # keyboard focus: a clear ring outside the card
            self.rrect(x0 - 4, y0 - 4, x1 + 4, y1 + 4, 21, fill="", depth=0,
                       outline=mix(ACCENT_HI, "#ffffff", 0.35), width=1.5)
        if live:   # logged-in account: a soft green light along the top edge
            cx, ww = (x0 + x1) / 2, (x1 - x0) * 0.42
            self.soft(cx - ww / 2, y0 - 1, cx + ww / 2, y0 + 2, 2, GOOD, alpha=150, spread=6,
                      dy=0, tags=tags)
            self.rrect(cx - ww / 2, y0, cx + ww / 2, y0 + 2.5, 1.2, fill=GOOD, depth=0,
                       tags=tags)
        return lift

    def draw_tile(self, x, y, T, name, idx):
        key, pkey = "tile:" + name, "play:" + name
        m = self.m(name)
        P, IB = self.TILE_PAD, self.TILE_INFO
        if self.dragging == name:   # the empty slot it left behind
            self.rrect(x - P, y - P, x + T + P, y + T + IB, 18, fill=mix(BG, SURFACE, 0.5),
                       outline=mix(LINE, ACCENT, 0.5), depth=0)
            return
        hov = self.hover in (key, pkey) and not self.dragging
        sel = self.selected == name
        live = self.state_.get("active") == name and not m.get("expired")
        tags = self.hit(key, click=lambda: self.select(name), dbl=lambda: self.switch(name),
                        right=lambda e: self.popup(e, name))
        lc = m.get("color")
        f = self.hv(key, hov)
        pr = self.pressed(key)
        sf = round(self.tween("sel:" + name, 1.0 if sel else 0.0, 0.3) * 8) / 8
        lift = self.tile_card(x, y, T, key, f, pr, sf, live, lc, tags)
        y = y - lift
        self.account_art(x, y, T, name, 12, tags, hov)
        if lc:
            self.circle(x + T - 13, y + 13, 6.5, fill=lc, outline=mix(BG, lc, 0.25), width=2,
                        tags=tags)
        badges = self.tile_badges(name)
        if badges:
            lab, fill, fg = badges[0]
            bw = min(T - 16, self.measure(lab, 8, "bold") + 18)
            self.soft(x + 8, y + 8, x + 8 + bw, y + 30, 11, "#000000", alpha=90, spread=6, dy=2,
                      tags=tags)
            self.rrect(x + 8, y + 8, x + 8 + bw, y + 30, 11, fill=fill, tags=tags, depth=0.6)
            self.text(x + 8 + bw / 2, y + 19, lab, 8, "bold", fg, anchor="center",
                      maxw=bw - 10, tags=tags)
        if self.settings.get("hotkeys") and idx < 9 and f > 0:
            # top-right, under the colour dot: clear of the status badge and the play button
            lab = f"Ctrl+Alt+{idx + 1}"
            bw = self.measure(lab, 8, "bold") + 14
            hy = y + (30 if lc else 8)
            self.rrect(x + T - 8 - bw, hy, x + T - 8, hy + 20, 10,
                       fill="#0c0917", alpha=round(0.85 * f, 2), depth=0, tags=tags)
            self.text(x + T - 8 - bw / 2, hy + 10, lab, 8, "bold", mix("#0c0917", SOFT, f),
                      anchor="center", tags=tags)
        tier = m.get("tier")
        if tier and tier >= 3 and self.images:
            self.circle(x + 26, y + T - 26, 21, fill="#0c0917", tags=tags)
            self.rank_icon(tier, x + 26, y + T - 26, 30, tags)
        if f > 0 and not self.busy:
            ptags = self.hit(pkey, click=lambda: self.switch(name),
                             right=lambda e: self.popup(e, name))
            pf = self.hv(pkey)
            ppr = self.pressed(pkey)
            r = 12 + 8 * f + 2 * pf - 1.5 * ppr
            self.soft(x + T - 30 - r, y + T - 30 - r, x + T - 30 + r, y + T - 30 + r, r, ACCENT,
                      alpha=int(120 * f), spread=8, dy=3, tags=ptags)
            self.circle(x + T - 30, y + T - 30, r, fill=mix(ACCENT, ACCENT_HI, pf), tags=ptags,
                        depth=1.0)
            if f > 0.5:
                self.icon(x + T - 29, y + T - 30, "play", 12, "#ffffff", tags=ptags)

        ix = x + 2
        self.text(ix, y + T + 20, name, 11, "bold", maxw=T, tags=tags)
        self.text(ix, y + T + 39, self.rid(m) or ago(self.state_["last_used"].get(name)), 9,
                  fill=MUTED, maxw=T, tags=tags)
        rt = self.rank_text(m)
        if rt:
            col = ASSETS.tier_color(tier) or DIM
            self.text(ix, y + T + 57, rt, 9, "bold", mix(col, "#ffffff", 0.35), maxw=T,
                      tags=tags)
        tx, ty = x, y + T + 80
        rp = self.ranked_pill(name)
        if rp and not m.get("expired"):
            wpill = self.measure(rp[0], 8, "bold") + 16
            self.pill(tx, ty, rp[0], fill=rp[1], fg=rp[2],
                      tags=self.hit("rk:" + name, click=lambda: self.select(name), tip=rp[3]))
            tx += wpill + 4
        for t in (m.get("tags") or [])[:3]:
            wpill = self.measure(t, 8, "bold") + 16
            if tx + wpill > x + T + 4:
                break
            self.pill(tx, ty, t, fill=CARD_HI, fg=SOFT, tags=tags)
            tx += wpill + 4

    def draw_row(self, x, y, w, name, idx):
        key, pkey = "tile:" + name, "play:" + name
        m = self.m(name)
        if self.dragging == name:
            self.rrect(x, y, x + w, y + 60, 14, fill=mix(BG, CARD, 0.4), outline=DIM,
                       dash=(5, 4))
            return
        hov = self.hover in (key, pkey) and not self.dragging
        sel = self.selected == name
        tags = self.hit(key, click=lambda: self.select(name), dbl=lambda: self.switch(name),
                        right=lambda e: self.popup(e, name))
        f = self.hv(key, hov)
        pr = self.pressed(key)
        sf = round(self.tween("sel:" + name, 1.0 if sel else 0.0, 0.3) * 8) / 8
        live = self.state_.get("active") == name and not m.get("expired")
        if sf > 0:
            self.soft(x, y, x + w, y + 60, 14, ACCENT, alpha=int(80 * sf), spread=10, dy=1,
                      tags=tags)
        elif f > 0:
            self.soft(x, y, x + w, y + 60, 14, "#000000", alpha=int(90 * f), spread=10, dy=4,
                      tags=tags)
        fill = mix(mix(SURFACE, CARD, 0.25), CARD_HI, 0.6 * f)
        if pr:
            fill = mix(fill, SURFACE, 0.4 * pr)
        self.rrect(x + pr, y + pr, x + w - pr, y + 60 - pr, 14, fill=fill,
                   outline=mix(mix(LINE, CARD_HI, f), ACCENT, sf), width=2 if sf > 0.5 else 1,
                   tags=tags, depth=1.0)
        if self.kbd_focus and sel:
            self.rrect(x - 4, y - 4, x + w + 4, y + 64, 17, fill="", depth=0,
                       outline=mix(ACCENT_HI, "#ffffff", 0.35), width=1.5)
        if live:
            self.soft(x + 1, y + 16, x + 4, y + 44, 2, GOOD, alpha=150, spread=5, dy=0, tags=tags)
            self.rrect(x + 1, y + 16, x + 4, y + 44, 1.5, fill=GOOD, depth=0, tags=tags)
        self.account_art(x + 9, y + 9, 42, name, 10, tags)
        if m.get("color"):
            self.rrect(x, y + 12, x + 4, y + 48, 2, fill=m["color"], tags=tags)
        self.text(x + 64, y + 21, name, 11, "bold", maxw=180, tags=tags)
        self.text(x + 64, y + 40, self.rid(m) or ago(self.state_["last_used"].get(name)), 9,
                  fill=MUTED, maxw=180, tags=tags)
        cx = x + 260
        tier = m.get("tier")
        if tier and tier >= 3:
            self.rank_icon(tier, cx + 14, y + 30, 28, tags)
        self.text(cx + 34, y + 30, self.rank_text(m) or "No stats", 10, "bold",
                  mix(ASSETS.tier_color(tier) or MUTED, "#ffffff", 0.35), maxw=170, tags=tags)
        cx += 220
        if w > 760:
            pt = self.playtime(name)
            self.text(cx, y + 30, f"{dur(pt['week'])} this week" if pt["week"] >= 60 else "—",
                      9, fill=MUTED, tags=tags)
            cx += 120
        tx = cx
        show_hk = self.settings.get("hotkeys") and idx < 9
        limit = x + w - (130 if show_hk else 64)
        for lab, fill, fg in self.tile_badges(name)[:2]:
            lab = (lab.replace("Wishlist in store", "In store").replace("Login expired", "Expired")
                   .replace("May need re-login", "Re-login?"))
            pw = self.measure(lab, 8, "bold") + 16
            if tx + pw > limit:
                continue
            tx += self.pill(tx, y + 30, lab, fill=fill, fg=fg, tags=tags) + 6
        rp = self.ranked_pill(name)
        if rp and not m.get("expired"):
            pw = self.measure(rp[0], 8, "bold") + 16
            if tx + pw <= limit:
                tx += self.pill(tx, y + 30, rp[0], fill=rp[1], fg=rp[2],
                                tags=self.hit("rk:" + name, click=lambda: self.select(name),
                                              tip=rp[3])) + 6
        for t in (m.get("tags") or [])[:3]:
            pw = self.measure(t, 8, "bold") + 16
            if tx + pw > limit:
                break
            tx += self.pill(tx, y + 30, t, fill=CARD_HI, fg=SOFT, tags=tags) + 6
        if show_hk and tx < limit + 4:
            self.text(x + w - 64, y + 30, f"Ctrl+Alt+{idx + 1}", 8, "bold", DIM, anchor="e",
                      tags=tags)
        ptags = self.hit(pkey, click=lambda: self.switch(name),
                         right=lambda e: self.popup(e, name))
        pf = self.hv(pkey)
        ppr = self.pressed(pkey)
        if pf > 0:
            self.soft(x + w - 50, y + 12, x + w - 14, y + 48, 18, ACCENT, alpha=int(120 * pf),
                      spread=8, dy=2, tags=ptags)
        self.circle(x + w - 32, y + 30, 18 + 1.5 * pf - 1.5 * ppr,
                    fill=mix(mix(CARD, ACCENT, f), ACCENT_HI, pf), tags=ptags, depth=1.0)
        self.icon(x + w - 31, y + 30, "play", 10, "#ffffff", tags=ptags)

    def draw_add_row(self, x, y, w):
        key = "tile:__add__"
        hov = self.hover == key
        tags = self.hit(key, click=self.add_new)
        f = self.hv(key, hov)
        self.rrect(x, y, x + w, y + 60, 14, fill=mix(SURFACE, CARD, 0.4 + 0.5 * f),
                   outline=mix(LINE, ACCENT, 0.2 + 0.6 * f), tags=tags)
        self.icon(x + 30, y + 30, "add", 13, self.hcol(key, MUTED, TEXT, hov), tags=tags)
        self.text(x + 64, y + 30, "Add account", 11, "bold", self.hcol(key, MUTED, TEXT, hov), tags=tags)

    def draw_add_tile(self, x, y, T):
        key = "tile:__add__"
        hov = self.hover == key
        tags = self.hit(key, click=self.add_new)
        f = self.hv(key, hov)
        pr = self.pressed(key)
        P, IB = self.TILE_PAD, self.TILE_INFO
        lift = round(2 * f - 1.5 * pr, 1)
        x0, y0, x1, y1 = x - P, y - P - lift, x + T + P, y + T + IB - lift
        if f > 0:
            self.soft(x0, y0, x1, y1, 18, ACCENT, alpha=int(70 * f), spread=12, dy=4, tags=tags)
        self.rrect(x0, y0, x1, y1, 18, fill=mix(mix(BG, SURFACE, 0.55), SURFACE, f),
                   outline=mix(mix(LINE, BG, 0.2), ACCENT, 0.15 + 0.55 * f), depth=0.6, tags=tags)
        cx, cy = x + T / 2, y + T / 2 - lift
        self.rrect(x, y - lift, x + T, y + T - lift, 12, fill=mix(BG, CARD, 0.45 + 0.25 * f),
                   depth=0, tags=tags)
        if f > 0:
            self.soft(cx - 26, cy - 26, cx + 26, cy + 26, 26, ACCENT, alpha=int(120 * f),
                      spread=12, dy=0, tags=tags)
        r = 24 + 3 * f - 2 * pr
        self.circle(cx, cy, r, fill=mix(CARD_HI, ACCENT, f), tags=tags, depth=1.0)
        self.icon(cx, cy, "add", 14, TEXT, tags=tags)
        self.text(x + 2, y + T + 20 - lift, "Add account", 11, "bold", tags=tags)
        self.text(x + 2, y + T + 39 - lift, "Sign in a new one", 9, fill=MUTED, tags=tags)

    def draw_drag_ghost(self):
        x, y = self.drag_pos
        idx = self.drop_index()
        if 0 <= idx < len(self.tile_slots):
            _, sx, sy = self.tile_slots[idx]
            if self.settings.get("layout") == "list":
                gy = self.tween("drop:y", sy - 5, 0.16)
                self.rrect(sx, gy - 1.5, sx + 300, gy + 1.5, 1.5, fill=ACCENT, depth=0)
            else:
                gx = self.tween("drop:x", sx - 19, 0.16)
                gy = self.tween("drop:gy", sy, 0.16)
                self.soft(gx - 2, gy, gx + 2, gy + self.TILE, 2, ACCENT, alpha=160, spread=6,
                          dy=0)
                self.rrect(gx - 2, gy, gx + 2, gy + self.TILE, 2, fill=ACCENT, depth=0)
        s = 84
        self.soft(x - s / 2, y - s / 2, x + s / 2, y + s / 2, 14, "#000000", alpha=150,
                  spread=16, dy=12)
        self.account_art(x - s / 2, y - s / 2, s, self.dragging, 12)
        self.rrect(x - s / 2 - 3, y - s / 2 - 3, x + s / 2 + 3, y + s / 2 + 3, 14, fill="",
                   outline=ACCENT, width=2)

    # ------------------------------------------------------------ right panel
    # ------------------------------------------------------------ play (launcher)
    def play_account(self):
        a = self.settings.get("play_account")
        if a in self.accounts():
            return a
        return self.state_.get("active") if self.state_.get("active") in self.accounts() else \
            (self.accounts() or [None])[0]

    def set_play_account(self, n):
        self.set_setting("play_account", n)

    def play_account_menu(self, x, y):
        cur = self.play_account()
        items = [{"label": n + ("  (signed in)" if n == self.state_.get("active") else ""),
                  "icon": "person", "check": n == cur,
                  "fn": lambda n=n: self.set_play_account(n)}
                 for n in self.accounts() if not self.m(n).get("archived")]
        self.popmenu(items, x, y, "n")

    def play_game(self, game):
        """The one-click path: be as fast as the situation allows."""
        prod = GAMES.get(game)
        name = self.play_account()
        if not prod or not name:
            return
        if prod in self.running_games:
            self.toast(f"{game} is already running.", "info", tray=False)
            return
        if self.busy:
            return
        self.launching[prod] = time.time()
        self.state_["game"] = game
        self.redraw()
        tuck = self.settings.get("tuck_client", True)
        if name != self.state_.get("active"):
            self.switch(name, game=game)
            if tuck:
                threading.Thread(target=tuck_riot_client, args=(40,), daemon=True).start()
            return

        def go():
            if read_lockfile() and self.signed_in_as(name) and launch_via_client(prod):
                self.set_status(f"Starting {game}…", "good")
            else:
                self.launch(prod)
                self.set_status(f"Starting {game}…", "info")
                self.call_ui(lambda: self.watch(name, prod))
            self.state_.setdefault("last_played", {})[prod] = time.time()
            save_state(self.state_)
            if tuck:
                tuck_riot_client(30)
        self.run(go, guard=False)

    def _games_tick(self):
        """Keep the launcher's Running / Starting labels honest."""
        on = self.page == "play" and not self.is_hidden()
        self.after(2000 if on or self.launching else 8000, self._games_tick)
        if not (on or self.launching):
            return

        def work():
            procs = running_processes()
            run = {p for p, exe in GAME_EXE.items() if exe.lower() in procs}

            def apply():
                changed = run != self.running_games
                self.running_games = run
                now = time.time()
                for p in list(self.launching):
                    if p in run or now - self.launching[p] > 90:
                        self.launching.pop(p, None)
                        changed = True
                if changed:
                    self.redraw()
            self.call_ui(apply)
        threading.Thread(target=work, daemon=True).start()

    def maybe_welcome(self):
        if not self.accounts() and not self.state_.get("onboarded") and not self.sheets:
            WelcomeSheet(self)

    def update_repo(self):
        return (self.settings.get("update_repo") or UPDATE_REPO or "").strip().strip("/")

    def check_updates(self, loud=False):
        repo = self.update_repo()
        if not repo:
            if loud:
                self.toast("Updates aren't set up for this build.", "info", tray=False)
            return
        if not loud:
            self.after(6 * 3600 * 1000, self.check_updates)

        def work():
            try:
                info = check_for_update(repo)
            except Exception as e:
                if loud:
                    err = describe_err(e)
                    self.call_ui(lambda: self.toast(f"Couldn't check for updates: {err}", "bad"))
                return

            def show():
                self.update_info = info
                if not info:
                    if loud:
                        self.toast(f"You're on the latest version ({VERSION}).", "good",
                                   tray=False)
                    return
                if loud or self.state_.get("skip_version") != info["version"]:
                    UpdateSheet(self, info)
                self.redraw()
            self.call_ui(show)
        threading.Thread(target=work, daemon=True).start()

    def load_news(self):
        key = self.settings.get("henrik_key")
        cache = self.state_.get("news") or {}
        if not key or getattr(self, "_news_busy", False) or \
                time.time() - cache.get("t", 0) < 3 * 3600:
            return
        self._news_busy = True

        def work():
            try:
                items = fetch_news(key)
                self.state_["news"] = {"t": time.time(), "items": items}
                save_state(self.state_)
            except Exception as e:
                print("news failed:", describe_err(e))
            self._news_busy = False
            self.call_ui(self.redraw)
        threading.Thread(target=work, daemon=True).start()

    def capture_thumb(self, path, w, h):
        """Rounded thumbnail of a local screenshot (cached)."""
        if not HAS_PIL:
            return None
        cache = self.__dict__.setdefault("_thumbs", {})
        try:
            k = (str(path), path.stat().st_mtime, w, h)
        except OSError:
            return None
        if k not in cache:
            try:
                im = ImageOps.fit(Image.open(path).convert("RGB"), (w * 2, h * 2),
                                  Image.LANCZOS)
                m = Image.new("L", (w * 2, h * 2), 0)
                ImageDraw.Draw(m).rounded_rectangle((0, 0, w * 2 - 1, h * 2 - 1), 24, fill=255)
                im.putalpha(m)
                cache[k] = ImageTk.PhotoImage(im.resize((w, h), Image.LANCZOS))
            except Exception:
                cache[k] = None
            if len(cache) > 40:
                cache.pop(next(iter(cache)))
        return cache[k]

    def warm_client(self):
        """Have the Riot Client already signed in and waiting (minimised) so Play is instant."""
        a = self.state_.get("active")
        if not (a and self.settings.get("warm_client", True)
                and self.settings.get("open_client", True)) or self.busy:
            return

        def work():
            if read_lockfile() or games_running():
                return
            try:
                self.launch(None)
                self.client_warming = True
                tuck_riot_client(45)
            except Exception as e:
                print("warm start failed:", describe_err(e))
            finally:
                self.client_warming = False
                self.call_ui(self.redraw)
        threading.Thread(target=work, daemon=True).start()

    def draw_play(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 30 - self.scroll()
        top = y
        bw = x1 - x0
        name = self.play_account()
        active = self.state_.get("active")
        self.page_header(x0, x1, y, "play", "Play", None)
        # account selector
        if name:
            lab = name
            tw = self.measure(lab, 10, "bold") + 74
            key = "play:acct"
            tags = self.hit(key, click=lambda: self.play_account_menu(x1 - tw / 2, y + 44),
                            tip="Which account to play on")
            self.rrect(x1 - tw, y, x1, y + 36, 18, fill=self.hcol(key, CARD, CARD_HI), tags=tags)
            self.account_art(x1 - tw + 4, y + 4, 28, name, 14, tags=tags)
            self.text(x1 - tw + 40, y + 18, lab, 10, "bold", tags=tags)
            self.text(x1 - 18, y + 18, "▾", 9, "bold", MUTED, anchor="center", tags=tags)
            ready = bool(read_lockfile()) and name == active
            st = ("Riot Client ready · instant start" if ready else
                  "Starting the Riot Client…" if getattr(self, "client_warming", False) else
                  "Signs in and starts in a few seconds" if name == active else
                  f"Switches to {name}, then starts")
            self.circle(x1 - tw - 18, y + 18, 4, fill=GOOD if ready else
                        (GOLD if name == active else SOFT))
            self.text(x1 - tw - 28, y + 18, st, 9, fill=MUTED, anchor="e")
        y += 62
        if not name:
            self.rrect(x0, y, x1, y + 140, 22, fill=SURFACE, outline=LINE)
            self.text(x0 + 30, y + 54, "Add an account to start playing", 15, "bold")
            self.action_button(x0 + 30, y + 80, "Add account", self.add_new, "play:add", "add")
            self.finish_scroll(top, y + 160, h)
            return
        games = [g for g in installed_games() if GAMES[g]]
        if not games:
            games = ["VALORANT"]
        dflt = self.m(name).get("default_game") or self.state_["game"]
        hero = dflt if dflt in games else games[0]
        others = [g for g in games if g != hero]
        room = h - self.BOTTOM - y - 30
        if others:      # fit the hero and the row of smaller cards in the window when we can
            hh = max(220, min(430, room - 190 - 18))
        else:
            hh = max(260, min(430, room))
        self.game_card(x0, y, x1, y + hh, hero, big=True)
        y += hh + 18
        if others:
            n = len(others)
            cw = (bw - (n - 1) * 16) / n
            ch = 190
            for i, g in enumerate(others):
                cx = x0 + i * (cw + 16)
                self.game_card(cx, y, cx + cw, y + ch, g)
            y += ch + 18
        y = self.draw_news(x0, x1, y + 8, h)
        y = self.draw_captures(x0, x1, y + 8, h)
        self.finish_scroll(top, y + 10, h)

    def draw_news(self, x0, x1, y, h):
        self.load_news()
        items = (self.state_.get("news") or {}).get("items") or []
        if not items:
            return y
        self.section(x0, y, "info", "VALORANT news", "patch notes and announcements")
        y += 44
        n = 3 if x1 - x0 > 760 else 2
        cw = (x1 - x0 - (n - 1) * 16) / n
        for i, a in enumerate(items[:n]):
            cx = x0 + i * (cw + 16)
            key = f"news:{i}"
            f = self.hv(key)
            tags = self.hit(key, click=lambda u=a["url"]: u and webbrowser.open(u),
                            tip="Open on playvalorant.com")
            ly = y - round(3 * f)
            if f > 0:
                self.soft(cx, ly, cx + cw, ly + 200, 16, ACCENT, alpha=int(80 * f), spread=12,
                          dy=6, tags=tags)
            self.rrect(cx, ly, cx + cw, ly + 200, 16, fill=SURFACE, outline=LINE, tags=tags)
            if not self.image(a.get("img"), cx, ly, cw, 118, mode="cover", radius=16,
                              tags=tags):
                self.rrect(cx, ly, cx + cw, ly + 118, 16, fill=CARD, tags=tags)
            self.text(cx + 16, ly + 140, a.get("cat", "").upper(), 8, "bold", SOFT, tags=tags)
            when = ago(a["date"], "").strip() if a.get("date") else ""
            if when:
                self.text(cx + cw - 16, ly + 140, when, 8, fill=DIM, anchor="e", tags=tags)
            self.text(cx + 16, ly + 168, a["title"], 10, "bold", maxw=cw - 32, tags=tags)
        return y + 216

    def draw_captures(self, x0, x1, y, h):
        if not hasattr(self, "_cap_t") or time.time() - self._cap_t > 30:
            self._cap_t = time.time()
            self._cap_dirs = capture_folders()
            self._caps = latest_captures(self._cap_dirs)
        dirs, caps = self._cap_dirs, self._caps
        if not dirs:
            return y
        self.section(x0, y, "film", "Screenshots & clips", "your latest captures")
        bx = x1
        for lab, p in reversed(dirs[:3]):
            key = "capdir:" + str(p)
            bw_ = self.action_button(bx, y - 2, lab, lambda p=p: os.startfile(str(p)), key,
                                     "folder", anchor="e", primary=False, h=30)
            bx -= bw_ + 8
        y += 44
        if not caps:
            self.text(x0, y + 10, "No screenshots yet - they'll show up here.", 9, fill=MUTED)
            return y + 40
        n = len(caps)
        cw = min(260, (x1 - x0 - (4 - 1) * 14) / 4)
        th = int(cw * 9 / 16)
        for i, (mt, f, lab) in enumerate(caps):
            cx = x0 + i * (cw + 14)
            key = f"cap:{i}"
            tags = self.hit(key, click=lambda f=f: os.startfile(str(f)), tip=f"{lab} · {f.name}")
            im = self.capture_thumb(f, int(cw), th)
            if im:
                self.cv.create_image(cx, y, image=im, anchor="nw", tags=tags)
            else:
                self.rrect(cx, y, cx + cw, y + th, 12, fill=CARD, tags=tags)
            self.rrect(cx, y, cx + cw, y + th, 12, fill="",
                       outline=self.hcol(key, LINE, ACCENT), tags=tags)
        return y + th + 20

    def game_art(self, game):
        look = GAME_LOOK.get(game, {})
        if look.get("art"):
            return look["art"]
        if game == "VALORANT" and ASSETS.maps:
            keys = sorted(k for k, v in ASSETS.maps.items() if v.get("splash")
                          and str(k).startswith("/Game"))
            if keys:
                pick = keys[int(time.time() // 86400) % len(keys)]
                return ASSETS.maps[pick]["splash"]
        return None

    def game_card(self, x0, y0, x1, y1, game, big=False):
        prod = GAMES[game]
        look = GAME_LOOK.get(game, {})
        col = look.get("color", ACCENT)
        key = "gcard:" + game
        bkey = "gplay:" + game
        f = self.hv(key, self.hover in (key, bkey))
        tags = self.hit(key, click=lambda: self.play_game(game),
                        tip=f"Play {game}")
        pr = self.pressed(key)
        lift = round(3 * f - 1.5 * pr, 1)
        y0 -= lift
        y1 -= lift
        self.soft(x0, y0, x1, y1, 22, "#000000", alpha=int(80 + 40 * f), spread=16,
                  dy=int(6 + 4 * f), tags=tags)
        if f > 0:
            self.soft(x0, y0, x1, y1, 22, col, alpha=int(90 * f), spread=16, dy=8, tags=tags)
        r = 22 if big else 18
        if not self.image(self.game_art(game), x0, y0, x1 - x0, y1 - y0, mode="cover",
                          radius=r, fade=True, tags=tags):
            self.rrect(x0, y0, x1, y1, r, fill=mix(BG, col, 0.22), tags=tags)
        self.rrect(x0, y0, x1, y1, r, fill="", outline=mix(LINE, col, 0.25 + 0.35 * f),
                   tags=tags)
        running = prod in self.running_games
        starting = prod in self.launching and not running
        pad = 34 if big else 22
        # title block (narrow cards stack the title above the button instead of beside it)
        narrow = not big and (x1 - x0) < self.measure(game, 17, "bold") + 120 + pad * 3
        ty = y1 - (128 if big else (112 if narrow else 92))
        self.text(x0 + pad, ty, look.get("tag", ""), 9 if big else 8, "bold",
                  mix(col, "#ffffff", 0.45), tags=tags)
        self.text(x0 + pad, ty + (34 if big else 26), game, 30 if big else 17, "bold",
                  "#ffffff", tags=tags)
        lp = (self.state_.get("last_played") or {}).get(prod)
        if lp and big:
            self.text(x0 + pad, ty + 66, f"Last played {ago(lp, '').strip()}", 9, fill=SOFT,
                      tags=tags)
        # play button
        bh = 52 if big else 40
        label = "Running" if running else ("Starting…" if starting else "Play")
        bwid = (190 if big else 120)
        bx1, by1 = x1 - pad, y1 - pad
        if narrow:
            by1 = y1 - 16
        bx0, by0 = bx1 - bwid, by1 - bh
        pf = self.hv(bkey)
        bpr = self.pressed(bkey)
        btags = self.hit(bkey, click=lambda: self.play_game(game),
                         tip=("Already running" if running else f"Play {game} on "
                              f"{self.play_account()}"))
        if running:
            fill = mix(SURFACE, GOOD, 0.35)
        elif starting:
            pulse = 0.5 + 0.5 * math.sin(time.time() * 5)
            fill = mix(col, "#ffffff", 0.1 * pulse)
            self._more = True
        else:
            fill = mix(col, mix(col, "#ffffff", 0.25), pf)
        if not running:
            self.soft(bx0, by0, bx1, by1, bh / 2, col, alpha=int(40 + 110 * pf - 30 * bpr),
                      spread=12, dy=4, tags=btags)
        if bpr:
            fill = mix(fill, mix(col, "#000000", 0.3), 0.5 * bpr)
        ins = 1.5 * bpr
        self.rrect(bx0 + ins, by0 + ins, bx1 - ins, by1 - ins, bh / 2, fill=fill, tags=btags,
                   depth=1.0 - 0.5 * bpr)
        icon = "check" if running else "play"
        lw = self.measure(label, 14 if big else 11, "bold")
        cx = (bx0 + bx1) / 2
        self.icon(cx - lw / 2 - 12, (by0 + by1) / 2, icon, 12 if big else 10, "#ffffff",
                  tags=btags)
        self.text(cx + 8, (by0 + by1) / 2, label, 14 if big else 11, "bold", "#ffffff",
                  anchor="center", tags=btags)

    def panel_extras(self, name, m, x0, x1, y, ymax):
        """Fill the middle of the side panel with things worth a glance."""
        now = time.time()
        gw = (x1 - x0 - 10) / 2
        tiles = []
        pk = m.get("peak_tier")
        if pk and pk >= 3:
            tiles.append(("Peak", ASSETS.tier_name(pk), mix(ASSETS.tier_color(pk) or TEXT,
                                                            "#ffffff", 0.3), pk))
        vp = (m.get("wallet") or {}).get(VP)
        if vp is not None:
            tiles.append(("Wallet", "Hidden" if self.streamer() else f"{self.money(vp)} VP",
                          TEXT, None))
        mt = (m.get("matches") or [None])[0]
        if mt:
            won = mt.get("won")
            res = "Win" if won is True else ("Loss" if won is False else "Draw")
            tiles.append(("Last match", f"{res} · {mt['k']}/{mt['d']}/{mt['a']}",
                          GOOD if won is True else (DANGER if won is False else MUTED), None))
        st = m.get("store") or {}
        wish = set(self.state_["wishlist"])
        fresh = st.get("daily_expires", 0) > now
        hit = fresh and any(o["skin"] in wish for o in st.get("daily") or [])
        if st:
            tiles.append(("Shop", "★ Wishlist skin!" if hit else
                          (f"Resets in {dur(st['daily_expires'] - now)}" if fresh else
                           "Log in to refresh"), GOLD if hit else (TEXT if fresh else MUTED),
                          None))
        rows = (len(tiles) + 1) // 2
        if not tiles or y + rows * 62 - 8 > ymax:
            tiles = tiles[:2] if y + 54 <= ymax else []
            rows = 1 if tiles else 0
        for i, (lab, val, col, tier) in enumerate(tiles):
            tx = x0 + (i % 2) * (gw + 10)
            ty = y + (i // 2) * 62
            self.rrect(tx, ty, tx + gw, ty + 54, 12, fill=CARD)
            self.text(tx + 12, ty + 17, lab, 8, "bold", DIM)
            vx = tx + 12
            if tier:
                self.rank_icon(tier, tx + 22, ty + 37, 20)
                vx += 22
            self.text(vx, ty + 37, val, 9, "bold", col, maxw=gw - (vx - tx) - 8)
        y += rows * 62 + 6
        daily = st.get("daily") or []
        if fresh and daily and y + 66 <= ymax and not self.streamer():
            self.text(x0, y + 8, "Today's shop", 8, "bold", DIM)
            y += 20
            n = len(daily)
            cw = (x1 - x0 - (n - 1) * 6) / n
            for i, o in enumerate(daily):
                sk = ASSETS.skins.get(o["skin"]) or {}
                cx = x0 + i * (cw + 6)
                key = f"pshop:{i}"
                tags = self.hit(key, click=(lambda su=o["skin"]: SkinDialog(self, su, name))
                                if sk else None, tip=sk.get("name"))
                ring = GOLD if o["skin"] in wish else (ACCENT if self.hover == key else "")
                self.rrect(cx, y, cx + cw, y + 46, 10, fill=CARD, outline=ring, tags=tags)
                self.image(sk.get("icon"), cx + 4, y + 6, cw - 8, 34, tags=tags)

    def draw_panel(self, w, h):
        px0, px1 = w - self.RIGHT - 18, w - 18
        py0, py1 = 18, h - self.BOTTOM - 10
        self.soft(px0, py0, px1, py1, 20, "#000000", alpha=90, spread=14, dy=6)
        self.rrect(px0, py0, px1, py1, 20, fill=SURFACE, outline=LINE)
        midx = (px0 + px1) / 2
        name = self.selected if self.selected in self.accounts() else None
        if name != getattr(self, "_panel_name", name):
            self._panel_t = time.time()
        self._panel_name = name
        self._panel_mark = (self.cv.find_all() or (0,))[-1]
        if not name:
            cy = (py0 + py1) / 2
            self.circle(midx, cy - 40, 30, fill="", outline=DIM, width=2)
            self.icon(midx, cy - 40, "person", 18, DIM)
            self.text(midx, cy + 12, "No account selected", 13, "bold", anchor="center")
            self.text(midx, cy + 34, "Pick one to log in", 10, fill=MUTED, anchor="center")
            return
        m = self.m(name)
        self.text(px0 + 22, py0 + 26, "Selected", 9, "bold", DIM)
        tools = [("edit", "Edit name, tags, note & region", lambda: self.edit(name)),
                 ("link", "Create desktop shortcut", lambda: self.shortcut(name)),
                 ("sync", "Update with current login", lambda: self.update_login(name)),
                 ("delete", "Delete", lambda: self.delete(name))]
        bx = px1 - 22 - 16
        for ic, tip, fn in reversed(tools):
            key = "tool:" + ic
            hov = self.hover == key
            tags = self.hit(key, click=fn, tip=tip)
            hot = mix(CARD, DANGER, 0.75) if ic == "delete" else CARD_HI
            pr = self.pressed(key)
            self.circle(bx, py0 + 26, 16 - pr, fill=self.hcol(key, CARD, hot, hov), tags=tags,
                        depth=0.8)
            self.icon(bx, py0 + 26, ic, 10, self.hcol(key, SOFT, TEXT, hov), tags=tags)
            bx -= 38

        bottom_reserved = 150
        avail = (py1 - bottom_reserved) - (py0 + 56) - 200
        size = int(max(72, min(150, avail - 120)))
        y = py0 + 56
        self.account_art(midx - size / 2, y, size, name, 20)
        tier = m.get("tier")
        if tier and tier >= 3 and self.images:
            self.circle(midx + size / 2 - 6, y + size - 6, 22, fill=SURFACE)
            self.rank_icon(tier, midx + size / 2 - 6, y + size - 6, 34)
        y += size + 24
        self.text(midx, y, name, 16, "bold", anchor="center", maxw=self.RIGHT - 40)
        y += 22
        self.text(midx, y, self.rid(m) or "Riot ID unknown", 10, fill=MUTED, anchor="center",
                  maxw=self.RIGHT - 40)
        y += 26
        if m.get("expired"):
            self.text(midx, y, "Login expired · sign in again", 10, "bold", DANGER,
                      anchor="center")
        else:
            self.text(midx, y, self.rank_text(m) or "No stats yet", 11, "bold",
                      TEXT if m.get("tier") else MUTED, anchor="center")
        y += 22
        bits = []
        if m.get("level"):
            bits.append(f"Lvl {m['level']}")
        if m.get("region"):
            bits.append(m["region"].upper())
        pt = self.playtime(name)
        if pt["week"] >= 60:
            bits.append(f"{dur(pt['week'])} this week")
        else:
            bits.append(ago(self.state_["last_used"].get(name)))
        self.text(midx, y, "  ·  ".join(bits), 9, fill=DIM, anchor="center")
        y += 24
        tg = (m.get("tags") or [])[:4]
        if tg:
            total = sum(self.measure(t, 8, "bold") + 20 for t in tg) - 4
            tx = midx - total / 2
            for t in tg:
                tx += self.pill(tx, y, t, fill=CARD_HI, fg=SOFT) + 4
            y += 24
        pens = (m.get("penalties") or {}).get("items") or []
        if pens and y < py1 - bottom_reserved - 16:
            p = pens[0]
            when = f"Ends in {dur(p['expires'] - time.time())}" if p.get("expires") else ""
            self.cv.create_text(midx, y - 6, text=f"⚠ {p['label']}", font=(self.UI, 9, "bold"),
                                fill=DANGER, width=self.RIGHT - 50, justify="center", anchor="n")
            lines = 2 if self.measure(p["label"], 9, "bold") > self.RIGHT - 60 else 1
            y += 16 * lines
            if when:
                self.text(midx, y + 2, when, 8, fill=MUTED, anchor="center")
                y += 16
            y += 8
        if m.get("note") and not self.streamer() and y < py1 - bottom_reserved - 16:
            self.cv.create_text(midx, y, text=m["note"], font=(self.UI, 9), fill=MUTED,
                                width=self.RIGHT - 60, justify="center", anchor="n")
            y += 18 * min(3, 1 + self.measure(m["note"], 9) // (self.RIGHT - 60)) + 6
        self.panel_extras(name, m, px0 + 18, px1 - 18, y + 10, py1 - 142)
        self.panel_fade(px0, py0, px1, py1 - 140)

        key = "panel:profile"
        hov = self.hover == key
        tags = self.hit(key, click=lambda: self.open_profile(name))
        by = py1 - 130
        pr = self.pressed(key)
        self.rrect(px0 + 22 + pr, by + pr, px1 - 22 - pr, by + 40 - pr, 20,
                   fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags,
                   outline=mix(LINE, CARD_HI, self.hv(key)), depth=0.8)
        self.text(midx, by + 20 + 0.5 * pr, "Profile, store & inventory", 10, "bold",
                  self.hcol(key, SOFT, TEXT, hov), anchor="center", tags=tags)
        key = "panel:login"
        hov = self.hover == key and not self.busy
        tags = self.hit(key, click=lambda: self.switch(name))
        by = py1 - 80
        f = self.hv(key, hov)
        pr = self.pressed(key) if not self.busy else 0
        if not self.busy:
            self.soft(px0 + 22, by, px1 - 22, by + 46, 23, ACCENT, alpha=int(50 + 90 * f - 30 * pr),
                      spread=12, dy=int(3 + 2 * f), tags=tags)
        self.rrect(px0 + 22 + 1.5 * pr, by + 1.5 * pr, px1 - 22 - 1.5 * pr, by + 46 - 1.5 * pr, 23,
                   fill=mix(DIM, ACCENT, 0.3) if self.busy else (self.hcol(key, ACCENT, ACCENT_HI,
                                                                         hov)),
                   tags=tags, depth=1.0 - 0.5 * pr)
        active = self.state_.get("active") == name
        game = self.m(name).get("default_game") or self.state_["game"]
        playable = bool(GAMES.get(game))
        quiet = not self.settings.get("open_client", True)
        label = "Working…" if self.busy else (
            (f"Play {game}" if playable else "Relaunch") if active else
            ("Switch" if quiet else "Log in"))
        self.icon(midx - self.measure(label, 12, "bold") / 2 - 12, by + 23, "play", 11,
                  "#ffffff", tags=tags)
        self.text(midx + 8, by + 23, label, 12, "bold", anchor="center", tags=tags)
        key = "panel:game"
        hov = self.hover == key
        sub = ("Doesn't open anything" if quiet and not active else
               f"Opens {game}" if playable else "Just signs in") + "  ·  other game ▾"
        tags = self.hit(key, click=lambda: self.popmenu(self.play_menu_items(name), midx - 110,
                                                        by + 72, "sw"),
                        tip="Pick a different game for this login")
        self.text(midx, by + 62, sub, 9, fill=self.hcol(key, DIM, SOFT, hov), anchor="center", tags=tags)

    def panel_fade(self, x0, y0, x1, y1):
        """When a different account is selected, its details glide up and fade in."""
        if not self.settings.get("animations", True):
            return
        age = time.time() - getattr(self, "_panel_t", 0)
        dur = 0.32
        if age >= dur:
            return
        self._more = True
        k = ease_out_quint(age / dur)
        dy = round((1 - k) * 10, 1)
        mk = self._panel_mark
        if dy >= 0.5:
            for item in self.cv.find_all():
                if item > mk:
                    self.cv.move(item, 0, dy)
        a = round((1 - ease_out(age / (dur * 0.8))) * 6) / 6
        if a > 0:
            self.rrect(x0 + 1, y0 + 1, x1 - 1, y1, 19, fill=SURFACE, depth=0, alpha=a)

    # ------------------------------------------------------------ profile
    def draw_profile(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 26 - self.scroll()
        top = y
        name = self.selected if self.selected in self.accounts() else None
        if not name:
            self.text((x0 + x1) / 2, h / 2 - 40, "Select an account first", 14, "bold",
                      anchor="center")
            self.text((x0 + x1) / 2, h / 2 - 14, "Pick one on the Accounts page", 10,
                      fill=MUTED, anchor="center")
            return
        m = self.m(name)
        active = self.state_.get("active") == name
        bw = x1 - x0

        # account switcher strip
        sx = x0
        for n in self.accounts():
            key = "pacc:" + n
            on = n == name
            hov = self.hover == key
            tags = self.hit(key, click=lambda n=n: self.select(n), tip=n)
            tw = min(150, self.measure(n, 9, "bold") + 44)
            if sx + tw > x1:
                break
            self.rrect(sx, y, sx + tw, y + 30, 15,
                       fill=CARD_HI if on else (self.hcol(key, mix(BG, CARD, 0.5), CARD, hov)),
                       outline=ACCENT if on else "", tags=tags)
            self.account_art(sx + 4, y + 4, 22, n, 11, tags)
            self.text(sx + 32, y + 15, n, 9, "bold", TEXT if on else MUTED, maxw=tw - 40,
                      tags=tags)
            sx += tw + 6
        y += 44

        bh = 168
        if not self.image(self.card_url(name, "wide"), x0, y, bw, bh, mode="cover",
                          radius=18, fade=True):
            self.rrect(x0, y, x1, y + bh, 18, fill=mix(BRAND, BG, 0.3))
        self.account_art(x0 + 26, y + 26, 116, name, 16)
        tx = x0 + 166
        self.text(tx, y + 46, name, 22, "bold", maxw=bw - 440)
        self.text(tx, y + 78, self.rid(m) or "Riot ID unknown", 11, fill=SOFT)
        chips = []
        if m.get("level"):
            chips.append(f"Level {m['level']}")
        if m.get("region"):
            chips.append(m["region"].upper())
        if m.get("title") and ASSETS.titles.get(m["title"]):
            chips.append(ASSETS.titles[m["title"]])
        chips += (m.get("tags") or [])
        px = tx
        for t in chips[:6]:
            if px > x1 - 260:
                break
            px += self.pill(px, y + 110, t, fill="#140f24", fg=TEXT) + 6
        if m.get("note") and not self.streamer():
            self.text(tx, y + 140, m["note"], 9, fill=MUTED, maxw=bw - 440)
        if active:
            busy = name in self.fetching
            self.action_button(x1 - 20, y + 22, "Refreshing…" if busy else "Refresh stats",
                               lambda: self.refresh_stats(name), "prof:refresh", "refresh",
                               anchor="e", disabled=busy)
        else:
            self.action_button(x1 - 20, y + 22, "Log in to refresh", lambda: self.switch(name),
                               "prof:login", "play", anchor="e", primary=False)
        last = max(m.get("updated") or 0, m.get("ext_updated") or 0) or None
        self.text(x1 - 20, y + 74, ago(last, "Updated"), 9, fill=MUTED, anchor="e")
        if m.get("tier") and m["tier"] >= 3:
            self.rank_icon(m["tier"], x1 - 64, y + 124, 58, large=True)
            self.text(x1 - 104, y + 116, ASSETS.tier_name(m["tier"]), 12, "bold",
                      mix(ASSETS.tier_color(m["tier"]) or TEXT, "#ffffff", 0.4), anchor="e")
            self.text(x1 - 104, y + 136, f"{m.get('rr', 0)} RR", 9, fill=MUTED, anchor="e")
        y += bh + 18

        tabs = [("overview", "Overview"), ("matches", "Matches"), ("inventory", "Inventory"),
                ("loadout", "Loadout"), ("collections", "Collections"), ("league", "League")]
        self.chips(x0, y, tabs, self.ptab, self.set_ptab, "ptab")
        if self.ptab in ("inventory", "collections"):
            self.place_search(x1, y + 16, hint="Search  (Ctrl+F)")
        y += 50
        self.mark_tab_content(y)

        if self.ptab == "league":
            y = self.draw_league(name, m, x0, x1, y, h, active)
            self.finish_scroll(top, y, h)
            return
        if not m.get("puuid"):
            msg = ("Hit Refresh stats to load rank, store and inventory." if active else
                   "Log into this account with RiotHub and everything loads "
                   "automatically.")
            tone = None
            if ASSETS.error and not ASSETS.ready:
                msg = "Couldn't reach valorant-api.com for game data: " + ASSETS.error
                tone = DANGER
            act = (("Refresh stats", lambda: self.refresh_stats(name), "prof:empty", "refresh")
                   if active else ("Log in", lambda: self.switch(name), "prof:empty", "play"))
            y = self.empty_state(x0, x1, y, "person", "No VALORANT data yet", msg, act, tone)
            self.finish_scroll(top, y + 10, h)
            return

        fn = {"overview": self.draw_overview, "matches": self.draw_matches,
              "inventory": self.draw_inventory, "collections": self.draw_collections,
              "loadout": self.draw_loadout}
        y = fn[self.ptab](name, m, x0, x1, y, h, active)
        self.finish_scroll(top, y, h)

    def rank_card(self, x, y, cw, ch, label, tier, sub):
        self.card_box(x, y, x + cw, y + ch, label)
        if not self.rank_icon(tier, x + 52, y + 66, 58, large=True):
            self.circle(x + 52, y + 66, 24, fill=CARD)
        col = ASSETS.tier_color(tier) or MUTED
        self.text(x + 96, y + 58, ASSETS.tier_name(tier), 15, "bold", mix(col, "#ffffff", 0.4),
                  maxw=cw - 110)
        self.text(x + 96, y + 82, sub, 9, fill=MUTED, maxw=cw - 110)

    def draw_overview(self, name, m, x0, x1, y, h, active):
        bw = x1 - x0
        g = 14
        cw = (bw - 2 * g) / 3
        ch = 112
        act = f" · {ASSETS.current_act_label}" if ASSETS.current_act_label else ""
        sub = f"{m.get('rr') or 0} RR"
        if m.get("games"):
            w_ = m.get('wins') or 0
            sub += f"  ·  {w_}W {max(0, m['games'] - w_)}L"
        self.rank_card(x0, y, cw, ch, "Current rank" + act, m.get("tier"), sub)
        pa = m.get("peak_act") or ""
        self.rank_card(x0 + cw + g, y, cw, ch, "Peak rank",
                       m.get("peak_tier"), f"Reached in {pa}" if pa else "Highest tier with a win")
        cx = x0 + 2 * (cw + g)
        self.card_box(cx, y, cx + cw, y + ch, "Wallet")
        wallet = m.get("wallet") or {}
        for i, (label, cid) in enumerate(CURRENCIES):
            ry = y + 52 + i * 21
            if not self.image(ASSETS.currency_icons.get(cid), cx + 18, ry - 8, 16, 16):
                self.circle(cx + 26, ry, 5, fill=SOFT)
            self.text(cx + 44, ry, self.money(self.count(f"wal:{name}:{cid}",
                                                         wallet.get(cid, 0))), 10, "bold")
            self.text(cx + cw - 18, ry, label, 9, fill=MUTED, anchor="e")
        y += ch + g

        # RR graph + battle pass
        gw = (bw - g) * 0.64
        gh = 230
        self.card_box(x0, y, x0 + gw, y + gh, "RR history · last ranked games", "history")
        self.draw_rr_graph(m.get("rr_history") or [], x0 + 18, y + 56, gw - 36, gh - 76)
        bx = x0 + gw + g
        self.card_box(bx, y, x1, y + gh, "Battle pass", "trophy")
        con = m.get("contracts") or {}
        bp = con.get("bp")
        if bp:
            self.text(bx + 18, y + 56, bp["name"], 11, "bold", maxw=x1 - bx - 36)
            tier_lab = f"Tier {self.count('bp:' + name, bp['level'], 0.7)}"
            self.text(bx + 18, y + 84, tier_lab, 20, "bold", SOFT)
            self.text(bx + 24 + self.measure(tier_lab, 20, "bold"), y + 88,
                      f"/ {bp['total']}", 11, fill=MUTED)
            self.bar(bx + 18, y + 108, x1 - bx - 36, bp["level"] / max(1, bp["total"]), 10)
            if bp.get("need"):
                self.text(bx + 18, y + 132, f"{bp['toward']:,} / {bp['need']:,} XP to next tier",
                          9, fill=MUTED)
            yy = y + 160
            for a in con.get("agents", [])[:2]:
                self.text(bx + 18, yy, a["name"], 9, "bold", maxw=x1 - bx - 110)
                self.text(x1 - 18, yy, f"{a['level']}/{a['total']}", 9, fill=MUTED, anchor="e")
                self.bar(bx + 18, yy + 11, x1 - bx - 36, a["level"] / max(1, a["total"]), 5)
                yy += 30
        else:
            lvl, xp = m.get("level"), m.get("xp")
            if lvl:
                self.text(bx + 18, y + 66, f"Level {lvl}", 20, "bold")
                frac = min(1.0, (xp or 0) / 5000)
                self.bar(bx + 18, y + 96, x1 - bx - 36, frac, 8)
                self.text(bx + 18, y + 120, f"{xp or 0:,} / 5,000 XP to level {lvl + 1}", 9,
                          fill=MUTED)
                self.text(bx + 18, y + 146, "Battle pass progress shows here when Riot "
                          "sends it with your stats.", 8, fill=DIM, maxw=300)
            else:
                self.text(bx + 18, y + 64, "Battle pass shows up after the next refresh.", 10,
                          fill=MUTED)
        y += gh + g

        # value / playtime / health
        self.card_box(x0, y, x0 + cw, y + ch, "Inventory value", "shop")
        val, priced = inventory_value(m) if ASSETS.ready else (0, 0)
        nskins = len(owned_skin_set(m)) if ASSETS.ready else 0
        self.text(x0 + 18, y + 62, f"≈ {self.money(self.count('val:' + name, val, 1.1))} VP"
                  if val else "—", 18, "bold", GOLD)
        free = nskins - priced
        self.text(x0 + 18, y + 88, f"{nskins} skins" + (f" · {free} free / battle pass"
                                                       if free else "")
                  + " · edition prices", 9, fill=MUTED, maxw=cw - 30,
                  tags=self.hit("val:info", tip="Store price where Riot showed it, otherwise the "
                                                "standard price for the skin's edition "
                                                "(Select 875, Deluxe 1275, Premium 1775, "
                                                "Exclusive 2175, Ultra 2475; knives x2)."))
        px = x0 + cw + g
        self.card_box(px, y, px + cw, y + ch, "Playtime", "clock")
        pt = self.playtime(name)
        self.text(px + 18, y + 62, dur(pt["week"]) if pt["week"] else "0m", 18, "bold")
        self.text(px + 24 + self.measure(dur(pt["week"]) if pt["week"] else "0m", 18, "bold"),
                  y + 64, "this week", 9, fill=MUTED)
        self.text(px + 18, y + 88, f"Today {dur(pt['today'])}  ·  Total {dur(pt['total'])}", 9,
                  fill=MUTED, maxw=cw - 30)
        hx = px + cw + g
        self.card_box(hx, y, hx + cw, y + ch, "Account health", "shield")
        hk = "health:" + name
        self.hit(hk, click=lambda: PenaltySheet(self, name), tip="Penalty details",
                 box=(hx, y, hx + cw, y + ch))
        pens = (m.get("penalties") or {}).get("items") or []
        if m.get("expired"):
            self.text(hx + 18, y + 62, "Login expired", 15, "bold", DANGER)
            self.text(hx + 18, y + 88, "Log in to sign it back in", 9, fill=MUTED)
        elif pens:
            p = pens[0]
            self.text(hx + 18, y + 62, "Restricted", 15, "bold", DANGER)
            extra = (f"ends in {dur(p['expires'] - time.time())}" if p.get("expires")
                     else f"{p['games']} games left" if p.get("games") else "")
            self.text(hx + 18, y + 88, f"{p['label']}  {extra}", 9, fill=MUTED, maxw=cw - 30)
            self.text(hx + cw - 18, y + 62, "Details ›", 9, "bold", self.hcol(hk, SOFT, TEXT),
                      anchor="e")
        elif m.get("penalties"):
            self.text(hx + 18, y + 62, "All clear", 15, "bold", GOOD)
            self.text(hx + 18, y + 88, "No queue restrictions or penalties", 9, fill=MUTED)
        else:
            self.text(hx + 18, y + 62, "Unknown", 15, "bold", MUTED)
            self.text(hx + 18, y + 88, "Checked on next refresh", 9, fill=MUTED)
        y += ch + g

        # today / goal / level
        t = today_summary(m)
        self.card_box(x0, y, x0 + cw, y + ch, "Today", "clock")
        if t["games"]:
            self.text(x0 + 18, y + 62, f"{t['w']}W  {t['l']}L", 18, "bold")
            rc = GOOD if t["rr"] > 0 else (DANGER if t["rr"] < 0 else MUTED)
            self.text(x0 + cw - 18, y + 62, f"{self.count('today:' + name, t['rr']):+d} RR", 14,
                      "bold", rc, anchor="e")
        else:
            self.text(x0 + 18, y + 62, "No ranked games yet", 13, "bold", MUTED)
        if t["streak"] >= 2:
            self.text(x0 + 18, y + 88, f"{'🔥 Win' if t['streak_win'] else '❄ Loss'} streak: "
                                       f"{t['streak']}", 9, "bold",
                      GOLD if t["streak_win"] else MUTED)
        gx = x0 + cw + g
        self.card_box(gx, y, gx + cw, y + ch, "Rank goal", "trophy")
        gp = goal_progress(m)
        if gp:
            self.rank_icon(gp["target"], gx + 40, y + 62, 36)
            self.text(gx + 66, y + 56, ASSETS.tier_name(gp["target"]), 12, "bold",
                      GOOD if gp["done"] else TEXT, maxw=cw - 150)
            msg = ("Reached!" if gp["done"] else f"{gp['left']} RR to go" +
                   (f" · ~{max(1, round(gp['games']))} games" if gp.get("games") else ""))
            self.text(gx + 66, y + 74, msg, 8, fill=MUTED, maxw=cw - 150)
            self.bar(gx + 18, y + 92, cw - 36, gp["frac"], 6, GOOD if gp["done"] else ACCENT)
            for i, (lab, stp, tip) in enumerate((("−", -1, "Lower goal"), ("+", 1, "Raise goal"),
                                                 ("✕", 0, "Clear goal"))):
                key = f"goal:{stp}"
                hov = self.hover == key
                tags = self.hit(key, click=lambda s_=stp: self.change_goal(name, s_), tip=tip)
                bx = gx + cw - 86 + i * 26
                self.circle(bx, y + 22, 11, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags)
                self.text(bx, y + 22, lab, 9, "bold", self.hcol(key, MUTED, TEXT, hov), anchor="center",
                          tags=tags)
        else:
            self.text(gx + 18, y + 50, "Pick a target rank and see how many", 9, fill=MUTED,
                      maxw=cw - 36)
            self.text(gx + 18, y + 66, "games it should take to get there.", 9, fill=MUTED,
                      maxw=cw - 36)
            self.action_button(gx + 18, y + 78, "Set goal", lambda: self.change_goal(name, 1),
                               "goal:set", "trophy", h=26)
        lx = gx + cw + g
        self.card_box(lx, y, lx + cw, y + ch, "Account level", "bolt")
        lvl = m.get("level") or 0
        xp = m.get("xp") or 0
        self.text(lx + 18, y + 60, f"Level {self.count('lvl:' + name, lvl, 0.8)}", 18, "bold")
        self.bar(lx + 18, y + 84, cw - 36, xp / 5000, 6)
        self.text(lx + cw - 18, y + 60, f"{xp:,} / 5,000 XP", 9, fill=MUTED, anchor="e")
        y += ch + g

        ls = m.get("last_session")
        if ls and time.time() - ls["t"] < 3 * 86400:
            self.rrect(x0, y, x1, y + 50, 14, fill=mix(SURFACE, ACCENT, 0.08), outline=LINE)
            self.icon(x0 + 22, y + 25, "clock", 11, SOFT)
            self.text(x0 + 42, y + 25, "Last session", 10, "bold", DIM)
            bx = x0 + 150
            col = GOOD if ls["rr"] > 0 else DANGER if ls["rr"] < 0 else MUTED
            for txt, c2 in ((ago(ls["t"], "").strip(), MUTED), (dur(ls["len"]), TEXT),
                            (f"{ls['w']}W {ls['l']}L", TEXT),
                            (f"{ls['rr']:+d} RR" if ls["ranked"] else "unrated", col)):
                self.text(bx, y + 25, txt, 11, "bold", c2)
                bx += max(110, self.measure(txt, 11, "bold") + 36)
            y += 50 + g
        wk = week_summary(m, self.playtime(name)["week"])
        self.rrect(x0, y, x1, y + 56, 14, fill=SURFACE, outline=LINE)
        self.icon(x0 + 22, y + 28, "history", 11, SOFT)
        self.text(x0 + 42, y + 28, "This week", 10, "bold", DIM)
        bits = [(f"{wk['w']}W {wk['l']}L", TEXT),
                (f"{wk['rr']:+d} RR", GOOD if wk["rr"] > 0 else DANGER if wk["rr"] < 0 else MUTED),
                (f"{wk['ranked']} ranked", TEXT), (dur(wk["time"]) + " played", TEXT)]
        bx = x0 + 140
        for txt, col in bits:
            self.text(bx, y + 28, txt, 11, "bold", col)
            bx += max(120, self.measure(txt, 11, "bold") + 40)
        y += 56 + g

        missions = m.get("missions") or []
        if missions:
            dl = [x for x in missions if x["kind"] == "Daily"]
            wk_ = [x for x in missions if x["kind"] == "Weekly"]
            done = sum(1 for x in missions if x["done"])
            mh = 44 + 30 * min(6, len(missions))
            self.card_box(x0, y, x1, y + mh, f"Missions  ·  {done}/{len(missions)} done", "check")
            if done == len(missions):
                self.text(x1 - 18, y + 22, "All missions complete", 9, "bold", GOOD, anchor="e")
            for i, mi in enumerate((dl + wk_)[:6]):
                ry = y + 52 + i * 30
                self.pill(x0 + 18, ry, mi["kind"], fill=mix(SURFACE, ACCENT if mi["kind"] ==
                                                             "Daily" else GOLD, 0.35),
                          fg=TEXT, size=7)
                self.text(x0 + 82, ry, mi["title"], 9, "bold", MUTED if mi["done"] else TEXT,
                          maxw=bw * 0.5)
                frac = min(1, mi["progress"] / max(1, mi["target"]))
                self.bar(x0 + bw * 0.62, ry - 3, bw * 0.2, 1 if mi["done"] else frac, 6,
                         GOOD if mi["done"] else ACCENT)
                self.text(x1 - 18, ry, "✓" if mi["done"] else
                          f"{int(mi['progress'])}/{mi['target']}", 9, "bold",
                          GOOD if mi["done"] else MUTED, anchor="e")
            y += mh + g

        acts = [a for a in m.get("acts") or [] if not a.get("old")][-8:]
        if acts:
            self.card_box(x0, y, x1, y + 120, "Act history", "history")
            n = len(acts)
            aw = (bw - 36) / max(n, 1)
            for i, a in enumerate(acts):
                ax = x0 + 18 + i * aw + aw / 2
                if not self.rank_icon(a["tier"], ax, y + 62, 40):
                    self.circle(ax, y + 62, 16, fill=CARD)
                self.text(ax, y + 94, ASSETS.act_label.get(a["id"], ""), 8, "bold", MUTED,
                          anchor="center", maxw=aw - 6)
                self.text(ax, y + 108, f"{a['wins']}W / {max(0, a['games'] - a['wins'])}L", 8,
                          fill=DIM,
                          anchor="center")
            y += 120 + g
        return y

    def draw_rr_graph(self, hist, x, y, w, h):
        pts = [p for p in hist if p.get("tier", 0) >= 3]
        if len(pts) < 2:
            self.text(x + w / 2, y + h / 2, "Play a couple of ranked games to see your RR graph.",
                      10, fill=MUTED, anchor="center")
            return
        vals = [p["tier"] * 100 + p["rr"] for p in pts]
        lo, hi = min(vals), max(vals)
        lo_t, hi_t = lo // 100, hi // 100 + 1
        lo, hi = lo_t * 100, hi_t * 100
        if hi - lo < 200:
            hi = lo + 200
        gx0 = x + 74
        gw = w - 80

        def py(v):
            return y + h - (v - lo) / (hi - lo) * h

        for t in range(int(lo // 100), int(hi // 100) + 1):
            yy = py(t * 100)
            if y - 2 <= yy <= y + h + 2:
                self.cv.create_line(gx0, yy, gx0 + gw, yy, fill=mix(SURFACE, LINE, 0.8), dash=(2, 4))
                self.text(gx0 - 10, yy - 9, ASSETS.tier_name(t), 8, fill=DIM, anchor="e",
                          maxw=70)
        n = len(vals)
        coords = []
        for i, v in enumerate(vals):
            coords += [gx0 + gw * i / (n - 1), py(v)]
        reveal = 1.0          # no left-to-right reveal: it re-rendered the graph every frame
        if HAS_PIL:
            self.graph_image(coords, int(gx0), int(y), int(gw), int(h), reveal)
        else:
            poly = coords + [gx0 + gw, y + h, gx0, y + h]
            self.cv.create_polygon(poly, fill=mix(SURFACE, ACCENT, 0.16), outline="")
            self.cv.create_line(coords, fill=ACCENT, width=3, smooth=True, capstyle="round")
        for i, p in enumerate(pts):
            cx, cy = coords[2 * i], coords[2 * i + 1]
            if (cx - gx0) / max(1, gw) > reveal + 0.001:
                continue
            col = GOOD if p["delta"] > 0 else (DANGER if p["delta"] < 0 else MUTED)
            key = f"rr:{i}"
            tags = self.hit(key, tip=f"{ASSETS.tier_name(p['tier'])} {p['rr']} RR  "
                                     f"({p['delta']:+d})  ·  "
                                     f"{ASSETS.maps.get(p['map'], {}).get('name', '')}")
            self.circle(cx, cy, 6 if self.hover == key else 4, fill=col, tags=tags)
        last = pts[-1]
        self.text(gx0 + gw, y - 14, f"{last['rr']} RR", 10, "bold", SOFT, anchor="e")

    def graph_image(self, coords, gx, gy, gw, gh, reveal=1.0):
        """Anti-aliased line + gradient fill for the RR graph (revealed left to right)."""
        step = max(1, min(12, round(reveal * 12)))
        # keyed on the shape relative to the graph's corner, so scrolling reuses the image
        rel = tuple(round(c - (gx if i % 2 == 0 else gy)) for i, c in enumerate(coords))
        base_key = ("graph", rel, gw, gh, ACCENT, SURFACE)
        key = base_key + (step,)
        im = self._shapes.get(key)
        if im is None and step < 12:
            full = self.__dict__.setdefault("_graph_pil", {}).get(base_key)
            if full is None:
                self.graph_image(coords, gx, gy, gw, gh, 1.0)
                full = self._graph_pil.get(base_key)
            if full is not None:
                cw = max(1, int(full.width * step / 12))
                part = Image.new("RGBA", full.size, (0, 0, 0, 0))
                part.paste(full.crop((0, 0, cw, full.height)), (0, 0))
                im = ImageTk.PhotoImage(part)
                self._shapes[key] = im
        if im is None:
            s_ = 3
            pad = 6
            W, H = (gw + pad * 2) * s_, (gh + pad * 2) * s_
            pts = [((coords[i] - gx + pad) * s_, (coords[i + 1] - gy + pad) * s_)
                   for i in range(0, len(coords), 2)]
            fill = Image.new("RGBA", (W, H), (0, 0, 0, 0))
            ImageDraw.Draw(fill).polygon(pts + [(pts[-1][0], H - pad * s_), (pts[0][0], H - pad * s_)],
                                         fill=(255, 255, 255, 255))
            acc = tuple(int(ACCENT[i:i + 2], 16) for i in (1, 3, 5))
            grad = Image.new("L", (1, 256))
            grad.putdata([int(95 * (1 - i / 255) ** 1.4) for i in range(256)])
            alpha = Image.composite(grad.resize((W, H)), Image.new("L", (W, H), 0),
                                    fill.getchannel("A"))
            layer = Image.new("RGBA", (W, H), acc + (0,))
            layer.putalpha(alpha)
            d = ImageDraw.Draw(layer)
            d.line(pts, fill=acc + (255,), width=3 * s_, joint="curve")
            for px_, py_ in (pts[0], pts[-1]):
                d.ellipse((px_ - 1.5 * s_, py_ - 1.5 * s_, px_ + 1.5 * s_, py_ + 1.5 * s_),
                          fill=acc + (255,))
            small = layer.resize((W // s_, H // s_), Image.LANCZOS)
            gp = self.__dict__.setdefault("_graph_pil", {})
            if len(gp) > 8:
                gp.clear()
            gp[base_key] = small
            im = ImageTk.PhotoImage(small)
            self._shapes[key] = im
        self.cv.create_image(gx - 6, gy - 6, image=im, anchor="nw")

    def draw_matches(self, name, m, x0, x1, y, h, active):
        matches = m.get("matches") or []
        if not matches:
            return self.empty_state(x0, x1, y, "history", "No recent matches yet",
                                    "Play a game and refresh stats - your last matches, "
                                    "scoreboards and round-by-round results show up here.")
        wins = sum(1 for mt in matches if mt.get("won") is True)
        losses = sum(1 for mt in matches if mt.get("won") is False)
        kd_k = sum(mt["k"] for mt in matches)
        kd_d = max(1, sum(mt["d"] for mt in matches))
        acs = round(sum(mt["acs"] for mt in matches) / len(matches))
        hs = [mt["hs"] for mt in matches if mt.get("hs") is not None]
        adr = [mt["adr"] for mt in matches if mt.get("adr") is not None]
        fb = sum(mt.get("fb") or 0 for mt in matches)
        summary = [("Record", f"{wins}W  {losses}L"), ("K/D", f"{kd_k / kd_d:.2f}"),
                   ("Avg ACS", str(acs)),
                   ("Headshot %", f"{sum(hs) / len(hs):.1f}%" if hs else "—"),
                   ("Damage / round", str(round(sum(adr) / len(adr))) if adr else "—"),
                   ("First bloods", str(fb) if hs else "—")]
        cw = (x1 - x0 - (len(summary) - 1) * 14) / len(summary)
        for i, (lab, val) in enumerate(summary):
            cx = x0 + i * (cw + 14)
            self.card_box(cx, y, cx + cw, y + 74, lab)
            self.text(cx + 18, y + 50, val, 16, "bold")
        y += 90
        bw = x1 - x0
        half = (bw - 14) / 2
        for ci, (title, key, lookup) in enumerate((("By map", "map", ASSETS.maps),
                                                   ("By agent", "agent", ASSETS.agents))):
            cx = x0 + ci * (half + 14)
            rows = match_breakdown(matches, key)[:5]
            ch = 44 + 26 * max(1, len(rows))
            self.card_box(cx, y, cx + half, y + ch, title)
            for ri, (k, e) in enumerate(rows):
                ry = y + 50 + ri * 26
                info = lookup.get(k, {})
                if key == "agent":
                    self.image(info.get("icon"), cx + 18, ry - 10, 20, 20, radius=5)
                self.text(cx + (46 if key == "agent" else 18), ry, info.get("name") or "?", 9,
                          "bold", maxw=half * 0.35)
                wr = e["w"] / e["n"]
                self.bar(cx + half * 0.42, ry - 3, half * 0.26, wr, 6,
                         GOOD if wr >= 0.5 else DANGER)
                self.text(cx + half * 0.72, ry, f"{round(wr * 100)}%", 9, "bold")
                self.text(cx + half - 18, ry, f"{e['n']} games · {e['k'] / max(1, e['d']):.2f} K/D",
                          8, fill=MUTED, anchor="e")
            if ci == 1:
                y += max(ch, 44 + 26 * max(1, len(match_breakdown(matches, "map")[:5]))) + 16
        # duo partners + time of day
        if self.duos is None and m.get("puuid"):
            self.duos = {}
            me = m["puuid"]
            threading.Thread(target=lambda: self.call_ui(
                lambda r=duo_partners(me): (setattr(self, "duos", r), self.redraw())),
                daemon=True).start()
        duos = [(p_, e) for p_, e in (self.duos or {}).items() if e["n"] >= 2][:4]
        names = m.get("duo_names") or {}
        self.card_box(x0, y, x0 + half, y + 44 + 26 * max(1, len(duos)),
                      "Who you win with (queued together)")
        if not duos:
            self.text(x0 + 18, y + 54, "Queue with friends a few times to see this.", 9,
                      fill=MUTED)
        for ri, (pu, e) in enumerate(duos):
            ry = y + 50 + ri * 26
            nm = "Hidden" if self.streamer() else names.get(pu) or f"Party member {ri + 1}"
            self.text(x0 + 18, ry, nm, 9, "bold", maxw=half * 0.4)
            wr = e["w"] / e["n"]
            self.bar(x0 + half * 0.45, ry - 3, half * 0.25, wr, 6, GOOD if wr >= 0.5 else DANGER)
            self.text(x0 + half - 18, ry, f"{round(wr * 100)}% · {e['n']} games", 8, fill=MUTED,
                      anchor="e")
        tx = x0 + half + 14
        tod = time_of_day(matches)
        self.card_box(tx, y, x1, y + 44 + 26 * 4, "When you play best")
        for ri, (k, e) in enumerate(tod.items()):
            ry = y + 50 + ri * 26
            self.text(tx + 18, ry, k, 9, "bold")
            if e["n"]:
                wr = e["w"] / e["n"]
                self.bar(tx + half * 0.3, ry - 3, half * 0.4, wr, 6,
                         GOOD if wr >= 0.5 else DANGER)
                self.text(tx + half - 18, ry, f"{round(wr * 100)}% · {e['n']}", 8, fill=MUTED,
                          anchor="e")
            else:
                self.text(tx + half - 18, ry, "—", 8, fill=DIM, anchor="e")
        y += 44 + 26 * max(4, len(duos)) + 16
        for i, mt in enumerate(matches):
            rh = 66
            ry = y + i * (rh + 8)
            if ry > h or ry < -rh:
                continue
            won = mt.get("won")
            col = GOOD if won is True else (DANGER if won is False else MUTED)
            mkey = f"match:{mt.get('id')}"
            mhov = self.hover == mkey
            mtags = self.hit(mkey, click=lambda mt=mt: self.open_match(m, mt),
                             tip="Open the full scoreboard")
            self.rrect(x0, ry, x1, ry + rh, 14, fill=mix(SURFACE, col, 0.13 if mhov else 0.07),
                       outline=mix(LINE, col, 0.5) if mhov else LINE, tags=mtags)
            self.rrect(x0, ry + 10, x0 + 4, ry + rh - 10, 2, fill=col)
            mp = ASSETS.maps.get(mt["map"], {})
            if not self.image(mp.get("icon"), x0 + 14, ry + 9, 132, 48, mode="cover", radius=8):
                self.rrect(x0 + 14, ry + 9, x0 + 146, ry + 57, 8, fill=CARD)
            self.text(x0 + 24, ry + 33, mp.get("name", ""), 10, "bold", "#ffffff")
            ag = ASSETS.agents.get(mt["agent"], {})
            if not self.image(ag.get("icon"), x0 + 160, ry + 11, 44, 44, radius=10):
                self.rrect(x0 + 160, ry + 11, x0 + 204, ry + 55, 10, fill=CARD)
            self.text(x0 + 218, ry + 23, mt["queue"], 10, "bold")
            self.text(x0 + 218, ry + 43, f"{ag.get('name', '')}  ·  {ago(mt['start'], '')}"
                      .replace("  ·   ", "  ·  "), 9, fill=MUTED)
            res = "Victory" if won is True else ("Defeat" if won is False else "Draw")
            cx = x0 + bw * 0.42
            self.text(cx, ry + 23, res, 11, "bold", col)
            self.text(cx, ry + 43, mt.get("score", ""), 9, fill=MUTED)
            cx = x0 + bw * 0.58
            self.text(cx, ry + 23, f"{mt['k']} / {mt['d']} / {mt['a']}", 11, "bold")
            self.text(cx, ry + 43, "K / D / A", 8, fill=DIM)
            cx = x0 + bw * 0.71
            self.text(cx, ry + 23, str(mt["acs"]), 11, "bold")
            self.text(cx, ry + 43, "ACS", 8, fill=DIM)
            if mt.get("hs") is not None:
                cx = x0 + bw * 0.80
                self.text(cx, ry + 23, f"{mt['hs']:.0f}%", 11, "bold")
                self.text(cx, ry + 43, "HS", 8, fill=DIM)
            if mt.get("rr") is not None and mt["queue"] == "Competitive":
                d = mt["rr"]
                self.pill(x1 - 18, ry + 33, f"{d:+d} RR", fill=mix(SURFACE, col, 0.25),
                          fg=col, size=9, anchor="e")
            elif mt.get("tier") and mt["tier"] >= 3:
                self.rank_icon(mt["tier"], x1 - 40, ry + 33, 30)
        return y + len(matches) * 74

    def draw_inventory(self, name, m, x0, x1, y, h, active):
        tabs = [("skins", "Skins"), ("buddies", "Buddies"), ("cards", "Cards"),
                ("sprays", "Sprays"), ("titles", "Titles")]
        items_all = {t: owned_items(m, t) for t, _ in tabs} if ASSETS.ready else \
            {t: [] for t, _ in tabs}
        self.chips(x0, y, [(t, f"{lab}  {len(items_all[t])}") for t, lab in tabs],
                   self.inv_tab, self.set_inv_tab, "inv", size=9, h=28)
        y += 42
        self.mark_tab_content(y)
        items = items_all[self.inv_tab]
        if self.inv_tab == "skins" and items:
            weapons = ["All"] + list(dict.fromkeys(s["weapon"] for s in items))
            wx = x0
            for wpn in weapons:
                key = "wpn:" + wpn
                on = self.weapon == wpn
                hov = self.hover == key
                tags = self.hit(key, click=lambda wpn=wpn: self.set_weapon(wpn))
                ww = self.measure(wpn, 9, "bold") + 22
                if wx + ww > x1:
                    wx = x0
                    y += 30
                self.rrect(wx, y, wx + ww, y + 24, 12,
                           fill=CARD_HI if on else (self.hcol(key, mix(BG, CARD, 0.5), CARD, hov)),
                           outline=ACCENT if on else "", tags=tags)
                self.text(wx + ww / 2, y + 12, wpn, 9, "bold", TEXT if on else MUTED,
                          anchor="center", tags=tags)
                wx += ww + 6
            y += 38
            if self.weapon != "All":
                items = [s for s in items if s["weapon"] == self.weapon]
            self.text(x0, y + 12, "Sort", 9, "bold", DIM)
            self.chips(x0 + 40, y, [("weapon", "Weapon"), ("rarity", "Rarity"),
                                    ("price", "Price"), ("name", "A–Z")], self.inv_sort,
                       self.set_inv_sort, "isort", size=8, h=24)
            val, _ = inventory_value(m)
            ew = self.action_button(x1, y - 4, "Export CSV", lambda: self.export_csv(name),
                                    "inv:csv", "download", primary=False, anchor="e", h=30)
            if val:
                self.text(x1 - ew - 16, y + 12, f"Worth ≈ {self.money(val)} VP", 10, "bold", GOLD,
                          anchor="e")
            y += 38
            if self.inv_sort == "rarity":
                items = sorted(items, key=lambda s: (-s["rank"], s["name"]))
            elif self.inv_sort == "price":
                items = sorted(items, key=lambda s: (-(s.get("price") or 0), s["name"]))
            elif self.inv_sort == "name":
                items = sorted(items, key=lambda s: s["name"].lower())
        q = self.search_var.get().strip().lower()
        if q:
            items = [s for s in items if q in s["name"].lower() or q in s["sub"].lower()]
        if not items:
            if not ASSETS.ready:
                return self.skeleton_cards(x0, x1, y, 6, 130, cols=3)
            if q:
                return self.empty_state(x0, x1, y, "search", "No matches",
                                        f"Nothing in this tab matches \"{q}\".")
            return self.empty_state(x0, x1, y, "shop", "Nothing here yet",
                                    "Refresh stats while logged in to load what this account "
                                    "owns.")
        eq_skins = {v.get("skin") for v in (m.get("loadout") or {}).values()}
        return self.item_grid(items, x0, x1, y, h, owner=name, equipped=eq_skins | {
            m.get("card"), m.get("title")}, kind=self.inv_tab)

    def item_grid(self, items, x0, x1, y, h, owner=None, equipped=(), kind="skins",
                  missing=()):
        bw = x1 - x0
        if kind == "skins":
            cw, chh, iw, ih = 226, 154, 196, 78
        elif kind == "cards":
            cw, chh, iw, ih = 142, 192, 118, 118
        elif kind == "titles":
            cw, chh, iw, ih = 220, 70, 0, 0
        else:
            cw, chh, iw, ih = 142, 168, 96, 96
        gap = 14
        cols = max(1, int((bw + gap) // (cw + gap)))
        cw = (bw - (cols - 1) * gap) / cols
        view_bot = h - self.BOTTOM
        wish = set(self.state_["wishlist"])
        for i, it in enumerate(items):
            cx = x0 + (i % cols) * (cw + gap)
            cy = y + (i // cols) * (chh + gap)
            if cy > view_bot or cy < -chh:
                continue
            key = f"item:{kind}:{it['id']}:{i}"
            hov = self.hover == key
            tags = self.hit(key, click=lambda it=it: self.open_item(it, owner))
            col = it.get("color")
            miss = it["id"] in missing
            fill = mix(SURFACE, col, 0.16) if col and not miss else SURFACE
            if hov:
                fill = mix(fill, "#ffffff", 0.04)
                self.glow(cx, cy, cx + cw, cy + chh, 14, col or ACCENT, tags)
            self.rrect(cx, cy, cx + cw, cy + chh, 14, fill=fill,
                       outline=self.hcol(key, LINE, ACCENT, hov), tags=tags)
            if col and not miss:
                self.rrect(cx + 14, cy, cx + cw - 14, cy + 3, 1, fill=col)
            if kind == "titles":
                self.text(cx + 16, cy + 26, it["name"], 11, "bold", maxw=cw - 32, tags=tags)
                self.text(cx + 16, cy + 48, "Equipped" if it["id"] in equipped else "Title",
                          9, fill=GOOD if it["id"] in equipped else MUTED, tags=tags)
                continue
            ix = cx + (cw - iw) / 2
            iy = cy + 16
            mode = "cover" if kind == "cards" else "contain"
            if not self.image(it.get("icon"), ix, iy, iw, ih, mode=mode, tags=tags,
                              radius=10 if kind == "cards" else 0, gray=miss):
                self.rrect(ix + iw / 2 - 18, iy + ih / 2 - 18, ix + iw / 2 + 18,
                           iy + ih / 2 + 18, 8, fill=CARD, tags=tags)
            ty = iy + ih + 18
            self.text(cx + 14, ty, it["name"], 10, "bold", DIM if miss else TEXT,
                      maxw=cw - 28, tags=tags)
            sub = it["sub"]
            if kind == "skins" and it.get("price"):
                sub += f"  ·  {it['price']:,} VP"
            self.text(cx + 14, ty + 19, sub, 9, fill=MUTED, maxw=cw - 52, tags=tags)
            if it.get("tier_icon"):
                self.image(it["tier_icon"], cx + cw - 30, ty + 11, 16, 16, tags=tags)
            if it["id"] in equipped:
                self.pill(cx + 10, cy + 18, "Equipped", fill=GOOD, fg=BG, tags=tags)
            if kind == "skins":
                skey = f"star:{it['id']}:{i}"
                on = it["id"] in wish
                st = self.hit(skey, click=lambda s=it["id"]: self.toggle_wish(s),
                              tip="Remove from wishlist" if on else "Add to wishlist")
                if on or hov or self.hover == skey:
                    self.circle(cx + cw - 20, cy + 20, 13, fill=mix(SURFACE, GOLD, 0.2) if on
                                else CARD, tags=st)
                    self.icon(cx + cw - 20, cy + 20, "star_on" if on else "star", 10,
                              GOLD if on else MUTED, tags=st)
        rows = (len(items) - 1) // cols + 1
        return y + rows * (chh + gap)

    def draw_league(self, name, m, x0, x1, y, h, active):
        lg = m.get("league")
        bw = x1 - x0
        bx = x0
        if active:
            busy = self.league_busy
            bx += self.action_button(x0, y, "Reading…" if busy else "Load from League client",
                                     self.refresh_league, "lg:load", "refresh", disabled=busy) + 10
        for key, lab in (("lol_auto_accept", "Auto-accept matches"),
                         ("lol_random_skin", "Random skin on lock-in")):
            on = self.settings.get(key)
            bx += self.action_button(bx, y, ("✓ " if on else "") + lab,
                                     lambda k=key: self.toggle(k), "lgt:" + key,
                                     primary=bool(on)) + 10
        y += 48
        if not lg:
            return self.empty_state(x0, x1, y, "game", "No League data yet",
                                    "Open League of Legends on this account and it loads "
                                    "automatically (rank, TFT rank and champion mastery).") + 10
        DDRAGON.ensure() if DDRAGON.version else threading.Thread(
            target=lambda: (DDRAGON.ensure(), self.call_ui(self.redraw)), daemon=True).start()
        self.rrect(x0, y, x1, y + 96, 16, fill=SURFACE, outline=LINE)
        if not self.image(DDRAGON.profile_icon(lg.get("icon")), x0 + 18, y + 16, 64, 64,
                          radius=14):
            self.rrect(x0 + 18, y + 16, x0 + 82, y + 80, 14, fill=CARD)
        rid = "Hidden#•••" if self.streamer() else f"{lg.get('name') or '?'}#{lg.get('tag') or ''}"
        self.text(x0 + 100, y + 36, rid, 14, "bold")
        self.text(x0 + 100, y + 62, f"Summoner level {lg.get('level') or '?'}  ·  "
                                    f"{ago(lg.get('updated'), 'Updated')}", 9, fill=MUTED)
        y += 110
        qs = lg.get("queues") or {}
        if qs:
            n = len(qs)
            cw = (bw - (n - 1) * 14) / n
            for i, (q, e) in enumerate(qs.items()):
                cx = x0 + i * (cw + 14)
                col = LEAGUE_COLORS.get(e["tier"], SOFT)
                self.card_box(cx, y, cx + cw, y + 110, q, "trophy")
                self.circle(cx + 40, y + 66, 20, fill=mix(SURFACE, col, 0.35), outline=col, width=2)
                self.text(cx + 40, y + 66, e["tier"][:1], 13, "bold", col, anchor="center")
                self.text(cx + 72, y + 58, f"{e['tier']} {e['div']}".strip(), 13, "bold",
                          mix(col, "#ffffff", 0.3), maxw=cw - 86)
                wr = e["w"] / max(1, e["w"] + e["l"])
                self.text(cx + 72, y + 82, f"{e['lp']} LP · {e['w']}W {e['l']}L · {round(wr * 100)}%",
                          9, fill=MUTED, maxw=cw - 86)
            y += 124
        else:
            self.text(x0, y + 10, "Unranked in every queue this split.", 10, fill=MUTED)
            y += 36
        ms = lg.get("mastery") or []
        if ms:
            self.text(x0, y + 10, "Top champions", 11, "bold")
            y += 30
            cw, gap = 132, 12
            for i, c in enumerate(ms):
                cx = x0 + i * (cw + gap)
                if cx + cw > x1:
                    break
                info = DDRAGON.champs.get(c["id"], {})
                self.rrect(cx, y, cx + cw, y + 150, 14, fill=SURFACE, outline=LINE)
                if not self.image(DDRAGON.champ_icon(c["id"]), cx + 26, y + 14, 80, 80, radius=40):
                    self.circle(cx + 66, y + 54, 40, fill=CARD)
                self.text(cx + cw / 2, y + 112, info.get("name", f"#{c['id']}"), 10, "bold",
                          anchor="center", maxw=cw - 16)
                self.text(cx + cw / 2, y + 132, f"M{c.get('level')} · {c.get('points', 0):,}", 8,
                          fill=MUTED, anchor="center")
            y += 166
        return y

    def draw_loadout(self, name, m, x0, x1, y, h, active):
        bw = x1 - x0
        bx = x0
        if active:
            bx += self.action_button(bx, y, "Shuffle (skin roulette)", self.shuffle_loadout,
                                     "lo:shuffle", "sync", disabled=self.busy) + 10
        bx += self.action_button(bx, y, "Save as preset", self.save_preset, "lo:save", "save",
                                 primary=False) + 10
        if m.get("roulette"):
            self.text(bx + 6, y + 17, "Roulette runs every time you switch to this account",
                      9, fill=GOLD)
        y += 50
        presets = self.state_.get("presets") or []
        if presets:
            self.text(x0, y + 8, "Presets  ·  apply to the logged-in account (skins it doesn't "
                                 "own are skipped)", 9, "bold", DIM)
            y += 24
            px = x0
            for pr in presets:
                lab = pr["name"]
                tw = self.measure(lab, 9, "bold") + 64
                if px + tw > x1:
                    px = x0
                    y += 40
                key = "preset:" + lab
                hov = self.hover == key
                tags = self.hit(key, click=lambda pr=pr: self.apply_preset(pr),
                                tip=f"Apply '{lab}' (saved from {pr.get('from', '?')})")
                self.rrect(px, y, px + tw, y + 32, 16, fill=self.hcol(key, CARD, CARD_HI, hov),
                           outline=LINE, tags=tags)
                self.icon(px + 16, y + 16, "play", 8, SOFT, tags=tags)
                self.text(px + 30, y + 16, lab, 9, "bold", tags=tags)
                dkey = "pdel:" + lab
                dt = self.hit(dkey, click=lambda pr=pr: self.delete_preset(pr), tip="Delete preset")
                self.text(px + tw - 16, y + 16, "✕", 9, "bold",
                          DANGER if self.hover == dkey else DIM, anchor="center", tags=dt)
                px += tw + 8
            y += 50
        eq = {str(k).lower(): v for k, v in (m.get("loadout") or {}).items()}
        if not eq:
            return self.empty_state(x0, x1, y, "shield", "No loadout loaded yet",
                                    "Refresh stats while logged in to see what's equipped on "
                                    "every weapon.")
        weapons = sorted(ASSETS.weapons.items(), key=lambda kv: (
            WEAPON_ORDER.index(kv[1]["name"]) if kv[1]["name"] in WEAPON_ORDER else 99))
        cw, ch, gap = 200, 128, 12
        cols = max(1, int((bw + gap) // (cw + gap)))
        cw = (bw - (cols - 1) * gap) / cols
        for i, (wid, wpn) in enumerate(weapons):
            cx = x0 + (i % cols) * (cw + gap)
            cy = y + (i // cols) * (ch + gap)
            if cy > h or cy < -ch:
                continue
            cur = eq.get(wid.lower()) or {}
            s = ASSETS.skins.get(cur.get("skin") or "")
            key = "lw:" + wid
            hov = self.hover == key
            tags = self.hit(key, click=lambda wid=wid: self.pick_skin_for(wid, name),
                            tip="Pick a skin")
            ct = ASSETS.ctiers.get((s or {}).get("tier") or "", {})
            col = ct.get("color")
            fill = mix(SURFACE, col, 0.16) if col else SURFACE
            self.rrect(cx, cy, cx + cw, cy + ch, 14, fill=mix(fill, "#ffffff", 0.04) if hov
                       else fill, outline=self.hcol(key, LINE, ACCENT, hov), tags=tags)
            icon = None
            if s:
                chroma = next((c for c in s["chromas"] if c["uuid"] == cur.get("chroma")), None)
                icon = (chroma or {}).get("render") or s["icon"]
            self.image(icon or wpn.get("icon"), cx + 14, cy + 14, cw - 28, 62, tags=tags)
            self.text(cx + 14, cy + 94, wpn["name"], 9, "bold", DIM, tags=tags)
            self.text(cx + 14, cy + 112, s["name"] if s else "Default", 10, "bold",
                      maxw=cw - 28, tags=tags)
        rows = (len(weapons) - 1) // cols + 1
        return y + rows * (ch + gap)

    def draw_agent_select(self, d, x0, x1, y, h):
        if not self.settings.get("agent_grid", True):
            return self.draw_agent_select_view(d, x0, x1, y, h)
        a = self.state_.get("active")
        m = self.m(a)
        locked = d.get("my_locked")
        cur = d.get("my_agent")
        owned = owned_ids(m, "agents")
        favs = list(self.settings.get("fav_agents") or [])
        agents = sorted(ASSETS.agents.items(),
                        key=lambda kv: (kv[0] not in favs,
                                        favs.index(kv[0]) if kv[0] in favs else 0, kv[1]["name"]))
        taken = {p["agent"] for p in d.get("players") or [] if p.get("locked") and not p["me"]}
        bw = x1 - x0
        self.card_box(x0, y, x1, y + 52, None)
        if locked:
            ag = ASSETS.agents.get(cur, {})
            self.text(x0 + 20, y + 26, f"Locked in as {ag.get('name', '?')}", 12, "bold", GOOD)
        else:
            self.text(x0 + 20, y + 26, "Pick your agent here, then lock in", 11, "bold")
            if cur:
                self.action_button(x1 - 16, y + 9, f"Lock {ASSETS.agents.get(cur, {}).get('name', '')}",
                                   lambda: self.agent_action(cur, True), "as:lock", "lock",
                                   anchor="e", disabled=self.busy)
        y += 62
        if not locked:
            size, gap = 52, 8
            cols = max(1, int((bw + gap) // (size + gap)))
            for i, (aid, info) in enumerate(agents):
                cx = x0 + (i % cols) * (size + gap)
                cy = y + (i // cols) * (size + gap)
                have = info.get("base") or aid in {o.lower() for o in owned} or not owned
                gone = aid in taken
                key = "as:" + aid
                hov = self.hover == key
                tags = self.hit(key, click=(lambda aid=aid: self.agent_action(aid, False))
                                if have and not gone else None,
                                dbl=(lambda aid=aid: self.agent_action(aid, True))
                                if have and not gone else None,
                                right=lambda e=None, aid=aid: self.toggle_fav_agent(aid),
                                tip=info["name"] + (" (taken)" if gone else "" if have else
                                                    " (not unlocked)")
                                + "  ·  double-click to lock · right-click to favourite")
                sel = aid == cur
                if sel or hov:
                    self.rrect(cx - 3, cy - 3, cx + size + 3, cy + size + 3, 12, fill="",
                               outline=ACCENT if sel else SOFT, width=2, tags=tags)
                if not self.image(info.get("icon"), cx, cy, size, size, radius=10, tags=tags,
                                  gray=not have or gone):
                    self.rrect(cx, cy, cx + size, cy + size, 10, fill=CARD, tags=tags)
                if aid in favs:
                    self.circle(cx + size - 6, cy + 6, 8, fill=GOLD, tags=tags)
                    self.text(cx + size - 6, cy + 6, "★", 7, "bold", BG, anchor="center",
                              tags=tags)
            y += ((len(agents) - 1) // cols + 1) * (size + gap) + 8
        return self.draw_presets_row(x0, x1, y)

    def draw_agent_select_view(self, d, x0, x1, y, h):
        cur = d.get("my_agent")
        ag = ASSETS.agents.get(cur or "", {})
        self.card_box(x0, y, x1, y + 52, None)
        if d.get("my_locked"):
            self.text(x0 + 20, y + 26, f"Locked in as {ag.get('name', '?')}", 12, "bold", GOOD)
        elif cur:
            self.text(x0 + 20, y + 26, f"Hovering {ag.get('name', '?')}  ·  lock in from the game",
                      11, "bold")
        else:
            self.text(x0 + 20, y + 26, "Pick your agent in the game", 11, "bold", MUTED)
        y += 62
        return self.draw_presets_row(x0, x1, y)

    def draw_presets_row(self, x0, x1, y):
        presets = self.state_.get("presets") or []
        if presets:
            self.text(x0, y + 12, "Quick loadout", 9, "bold", DIM)
            px = x0 + 100
            for pr in presets[:8]:
                lab = pr["name"]
                tw = self.measure(lab, 9, "bold") + 30
                if px + tw > x1:
                    break
                key = "lpre:" + lab
                hov = self.hover == key
                tags = self.hit(key, click=lambda pr=pr: self.apply_preset(pr),
                                tip="Apply this loadout now")
                self.rrect(px, y, px + tw, y + 26, 13, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags)
                self.text(px + tw / 2, y + 13, lab, 9, "bold", self.hcol(key, MUTED, TEXT, hov),
                          anchor="center", tags=tags)
                px += tw + 8
            y += 40
        return y + 6

    def draw_collections(self, name, m, x0, x1, y, h, active):
        if not ASSETS.ready:
            return self.skeleton_cards(x0, x1, y, 6, 150)
        cols = collections(m)
        q = self.search_var.get().strip().lower()
        if q:
            cols = [c for c in cols if q in c["name"].lower()]
        done = sum(1 for c in cols if c["have"] == c["total"])
        self.text(x0, y + 10, f"{len(cols)} collections started  ·  {done} complete", 10,
                  fill=MUTED)
        y += 32
        owned = owned_skin_set(m)
        for c in cols:
            key = "col:" + c["id"]
            hov = self.hover == key
            exp = self.expanded == c["id"]
            rh = 64
            if -rh < y < h:
                tags = self.hit(key, click=lambda c=c: self.toggle_expand(c["id"]))
                self.rrect(x0, y, x1, y + rh, 14, fill=CARD_HI if hov or exp else SURFACE,
                           outline=ACCENT if exp else LINE, tags=tags)
                self.text(x0 + 18, y + 22, c["name"], 11, "bold", maxw=200, tags=tags)
                frac = c["have"] / c["total"]
                self.text(x0 + 18, y + 44, f"{c['have']} / {c['total']}" +
                          ("  ·  Complete" if frac >= 1 else ""), 9,
                          fill=GOOD if frac >= 1 else MUTED, tags=tags)
                self.bar(x0 + 230, y + 28, 180, frac, 8, GOOD if frac >= 1 else ACCENT)
                ix = x0 + 440
                for su in c["skins"][:10]:
                    if ix + 70 > x1 - 40:
                        break
                    s = ASSETS.skins[su]
                    self.image(s["icon"], ix, y + 12, 64, 40, tags=tags, gray=su not in owned)
                    ix += 72
                self.icon(x1 - 24, y + 32, "chevron", 10, MUTED, tags=tags)
                if exp and active:
                    self.action_button(x1 - 44, y + 15, "Equip owned", lambda c=c:
                                       self.equip_collection(c), "coleq:" + c["id"], "check",
                                       anchor="e", h=30)
            y += rh + 8
            if exp:
                items = [ASSETS.skin_view(su) for su in c["skins"]]
                items = [i for i in items if i]
                miss = {i["id"] for i in items if i["id"] not in owned}
                y = self.item_grid(items, x0 + 12, x1 - 12, y + 4, h, owner=name,
                                   kind="skins", missing=miss) + 10
        return y

    # ------------------------------------------------------------ live match
    def draw_live(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 30 - self.scroll()
        top = y
        bw = x1 - x0
        active = self.state_.get("active")
        self.page_header(x0, x1, y, "game", "Live match",
                         "Lobby ranks in agent select and in game  ·  hidden names stay hidden")
        if active:
            rw = self.action_button(x1, y + 2, "Updating…" if self.live_busy else "Refresh",
                                    self.refresh_live, "live:refresh", "refresh", anchor="e",
                                    disabled=self.live_busy)
            fm = self.settings.get("focus_mode")
            self.action_button(x1 - rw - 10, y + 2, "Focus mode on" if fm else "Focus mode",
                               lambda: self.toggle("focus_mode"), "live:focus",
                               "eye_off" if fm else "eye", anchor="e", primary=bool(fm),
                               tip="Hide other players' ranks so you just play")
        y += 62
        if not active:
            self.empty_state(x0, x1, y, "game", "Nobody's logged in",
                             "Log into an account and your party, queue and lobby ranks show "
                             "up here.", ("Go to accounts", lambda: self.set_page("home"),
                                          "live:go", "person"))
            return
        d = self.live
        if self.live_error and not d:
            y = self.empty_state(x0, x1, y, "warning", "Couldn't reach the live game service",
                                 self.live_error, ("Try again", self.refresh_live, "live:retry",
                                                   "refresh"), tone=GOLD)
            self.finish_scroll(top, y + 10, h)
            return
        if not d:
            self.rrect(x0, y, x1, y + 120, 18, fill=SURFACE, outline=LINE)
            self.skel(x0 + 24, y + 24, x0 + 150, y + 40, 8)
            self.skel(x0 + 24, y + 54, x0 + 260, y + 78, 8, 1)
            self.skel(x0 + 24, y + 90, x0 + 180, y + 102, 6, 2)
            self.skeleton_rows(x0, x1, y + 140, 3)
            if not self.live_busy:
                self.after(10, self.refresh_live)
            return
        phase = d.get("phase")
        mp = ASSETS.maps.get(d.get("map") or "", {})
        bh = 120
        if phase != "none":
            if not self.image(mp.get("splash") or mp.get("icon"), x0, y, bw, bh, mode="cover",
                              radius=18, fade=True):
                self.rrect(x0, y, x1, y + bh, 18, fill=mix(BRAND, BG, 0.3))
            label = "Agent select" if phase == "pregame" else "In game"
            self.pill(x0 + 24, y + 30, label, fill=ACCENT if phase == "pregame" else GOOD,
                      fg=TEXT if phase == "pregame" else BG, size=9)
            self.text(x0 + 24, y + 66, mp.get("name") or "Unknown map", 22, "bold")
            q = d.get("queue") or ""
            self.text(x0 + 24, y + 96, QUEUES.get(q, q.title() or "Custom"), 11, fill=SOFT)
            if d.get("side"):
                atk = d["side"] == "Attack"
                self.pill(x0 + 24 + self.measure(label, 9, "bold") + 30, y + 30,
                          f"You start on {d['side']}", fill=mix(SURFACE, DANGER if atk else
                                                                 "#2fb7ff", 0.5),
                          fg=TEXT, size=9)
            if phase == "pregame" and d.get("timer"):
                left = max(0, d["timer"] - (time.time() - d.get("timer_t", time.time())))
                self.text(x1 - 24, y + 40, f"{int(left)}s", 22, "bold",
                          DANGER if left < 10 else TEXT, anchor="e")
                self.text(x1 - 24, y + 66, "to lock in", 9, fill=MUTED, anchor="e")
            if phase == "pregame":
                self.action_button(x1 - 20, y + bh - 42, "Leave match", self.leave_pregame,
                                   "live:dodge", "close", primary=False, anchor="e", h=30,
                                   disabled=self.busy, tip="Dodge - same penalty as in game")
                self._more = self._more or self.settings.get("animations", True)
        else:
            bh = self.draw_party_card(d, x0, x1, y)
        if phase == "pregame":
            self.text(x0 + 24, y + bh + 12, ago(d.get("t"), "Updated"), 8, fill=DIM)
        else:
            self.text(x1 - 20, y + bh - 18, ago(d.get("t"), "Updated"), 9, fill=DIM, anchor="e")
        y += bh + 18

        players = d.get("players") or []
        if phase == "none":
            groups = [("Your party", players)] if len(players) > 1 else []
        elif phase == "pregame":
            groups = [("Your team", players)]
        else:
            groups = [("Your team", [p for p in players if p["ally"]]),
                      ("Enemy team", [p for p in players if not p["ally"]])]
        if not groups:
            self.text(x0, y + 10, "Party up or queue to see ranks here.", 10, fill=DIM)
            self.finish_scroll(top, y + 30, h)
            return
        if phase == "pregame" and d.get("match_id"):
            y = self.draw_agent_select(d, x0, x1, y, h)
        if phase in ("pregame", "ingame"):
            me_meta = self.m(active)
            gap = 0 if self.settings.get("focus_mode") else team_gap(players)
            tips = agent_tips(me_meta.get("matches"), d.get("map"))
            cw = (bw - 14) / 2
            self.card_box(x0, y, x0 + cw, y + 96, "Team rank spread", "compare")
            if gap >= 6:
                self.text(x0 + 18, y + 54, "Big rank gap on your team", 12, "bold", GOLD)
                self.text(x0 + 18, y + 76, f"About {gap // 3} ranks between the highest and "
                                           "lowest teammate. Expect uneven games.", 9,
                          fill=MUTED, maxw=cw - 36)
            else:
                self.text(x0 + 18, y + 54, "Evenly matched team", 12, "bold", GOOD)
                self.text(x0 + 18, y + 76, "Everyone's within a couple of ranks.", 9, fill=MUTED)
            tx = x0 + cw + 14
            rows = tips["map"] or tips["all"]
            label = (f"Your best agents on {mp.get('name')}" if tips["map"] and mp.get("name")
                     else "Your best agents lately")
            self.card_box(tx, y, x1, y + 96, label, "trophy")
            if rows:
                ax = tx + 18
                for aid, e in rows:
                    ag = ASSETS.agents.get(aid, {})
                    self.image(ag.get("icon"), ax, y + 40, 36, 36, radius=8)
                    self.text(ax + 44, y + 50, ag.get("name", "?"), 9, "bold")
                    self.text(ax + 44, y + 68, f"{round(100 * e['w'] / e['n'])}% · {e['n']}g", 8,
                              fill=MUTED)
                    ax += (x1 - tx - 36) / 3
            else:
                self.text(tx + 18, y + 58, "Play a few games to get agent tips.", 9, fill=MUTED)
            y += 110
        two_col = len(groups) == 2 and bw > 900
        colw = (bw - 18) / 2 if two_col else bw
        ys = []
        for gi, (title, ps) in enumerate(groups):
            gx = x0 + (gi * (colw + 18) if two_col else 0)
            gy = y if two_col else (ys[-1] if ys else y)
            avg = [p["tier"] for p in ps if p["tier"] >= 3]
            avg_t = round(sum(avg) / len(avg)) if avg else 0
            self.text(gx, gy + 10, title, 13, "bold",
                      GOOD if "Your" in title else DANGER if "Enemy" in title else TEXT)
            if avg_t and not self.settings.get("focus_mode"):
                self.text(gx + colw, gy + 10, f"avg {ASSETS.tier_name(avg_t)}", 10, "bold",
                          MUTED, anchor="e")
            gy += 30
            for p in ps:
                self.live_row(gx, gy, colw, p)
                gy += 66
            ys.append(gy + 14)
        self.text(x0, max(ys) + 4, "Players with 'Hide my name' on stay hidden. Ranks are the "
                                   "same ones the in-game scoreboard shows.", 9, fill=DIM,
                  maxw=bw)
        self.finish_scroll(top, max(ys) + 30, h)

    def draw_party_card(self, d, x0, x1, y):
        """Lobby controls like the game menu: queue, mode, open/closed party, invites."""
        bw = x1 - x0
        pid = d.get("party_id")
        queueing = str(d.get("party_state", "")).upper() == "MATCHMAKING"
        bh = 176 if pid else 120
        self.rrect(x0, y, x1, y + bh, 18, fill=SURFACE, outline=ACCENT if queueing else LINE,
                   width=2 if queueing else 1)
        n = len(d.get("party") or [])
        q = d.get("queue") or ""
        if queueing:
            since = queue_elapsed(d)
            self.text(x0 + 24, y + 40, f"Finding a match · {int(since // 60)}:{int(since % 60):02d}",
                      18, "bold", ACCENT_HI)
            self._more = self._more or self.settings.get("animations", True)
        else:
            self.text(x0 + 24, y + 40, "Not in a match", 18, "bold")
        sub = QUEUES.get(q, q.title() or "Custom") if (pid or q) else "VALORANT isn't open"
        if pid:
            sub += f"  ·  party of {n}" if n > 1 else "  ·  solo"
            sub += "  ·  open" if d.get("party_open") else "  ·  closed"
        self.text(x0 + 24, y + 68, sub, 10, fill=MUTED)
        if not pid:
            self.text(x0 + 24, y + 94, "Start VALORANT from the Play page and your party, "
                      "queue and lobby ranks show up here.", 9, fill=DIM, maxw=bw - 48)
            return bh
        bx = x0 + 24
        by = y + 92
        if queueing:
            bx += self.action_button(bx, by, "Stop queue", lambda: self.party_do("leave"),
                                     "pty:leave", "close") + 10
        else:
            bx += self.action_button(bx, by, "Start queue", lambda: self.party_do("join"),
                                     "pty:join", "play") + 10
        bx += self.action_button(bx, by, "Invite by Riot ID", lambda: self.party_do("invite"),
                                 "pty:inv", "add", primary=False) + 10
        op = bool(d.get("party_open"))
        self.action_button(bx, by, "Party open" if op else "Party closed",
                           lambda: self.party_do("access", not op), "pty:acc",
                           "eye" if op else "lock", primary=False,
                           tip="Open lets friends join without an invite")
        qs = [x for x in (d.get("queues") or []) if x in QUEUES] or []
        qx = x0 + 24
        qy = y + 148
        for qid in sorted(qs, key=lambda k: list(QUEUES).index(k)):
            label = QUEUES[qid]
            key = "pty:q:" + qid
            hov = self.hover == key
            cur = qid == q
            w = self.measure(label, 8, "bold") + 18
            if qx + w > x1 - 150:
                break
            tags = self.hit(key, click=None if cur or queueing else
                            (lambda qid=qid: self.party_do("queue", qid)))
            self.rrect(qx, qy - 11, qx + w, qy + 11, 11,
                       fill=ACCENT if cur else (self.hcol(key, CARD, CARD_HI, hov)), tags=tags)
            self.text(qx + w / 2, qy, label, 8, "bold", TEXT if cur else self.hcol(key, MUTED, TEXT, hov),
                      anchor="center", tags=tags)
            qx += w + 6
        return bh

    def party_do(self, action, arg=None):
        d = self.live or {}
        pid = d.get("party_id")
        if not pid:
            self.toast("No party found. Is VALORANT open?")
            return
        if action == "invite" and arg is None:
            rid = Modal(self, "Invite to party", "Type their Riot ID, like name#tag.",
                        entry="", ok="Send invite").result
            if not rid:
                return
            if "#" not in rid:
                self.notify("Riot ID needs a tag", "Use the full Riot ID, like name#EUW.")
                return
            nm, tg = rid.rsplit("#", 1)
            arg = (nm.strip(), tg.strip())
        msgs = {"join": "Queue started.", "leave": "Queue stopped.",
                "queue": f"Mode set to {QUEUES.get(arg, arg) if isinstance(arg, str) else ''}.",
                "access": "Party is now " + ("open." if arg else "closed."),
                "invite": f"Invite sent to {arg[0]}#{arg[1]}." if isinstance(arg, tuple) else ""}

        def go():
            vc, region = self.get_vc()
            try:
                party_action(vc, region, pid, action, arg)
            except Exception as e:
                raise RuntimeError(describe_err(e))
            self.call_ui(lambda: (self.toast(msgs.get(action) or "Done.", "good"),
                                  self.refresh_live()))
        self.run(go, guard=False)

    def agent_action(self, agent_id, lock):
        d = self.live or {}
        mid = d.get("match_id")
        if not mid:
            return
        if not self.settings.get("agent_grid_ok"):
            if not self.confirm("Heads up", "Picking agents from outside the game is what Riot "
                                            "shut down Recon Bolt for. It's manual here, but it "
                                            "could still get flagged. Use it anyway?",
                                ok="Use it", danger=True):
                return
            self.settings["agent_grid_ok"] = True
            save_state(self.state_)

        def go():
            vc, region = self.get_vc()
            pregame_action(vc, region, mid, agent_id, lock)
            self.call_ui(lambda: (self.live.update({"my_agent": agent_id, "my_locked": lock}),
                                  self.refresh_live()))
            if lock:
                self.set_status(f"Locked in {ASSETS.agents.get(agent_id, {}).get('name', '')}.",
                                "good")
        self.run_soon(go, lock)

    def run_soon(self, fn, retry, tries=10):
        """run(), but a lock request made while a pick is still in flight waits its turn."""
        if not self.run(fn, guard=False) and retry and tries > 0:
            self.after(200, lambda: self.run_soon(fn, retry, tries - 1))

    PARTY_COLORS = ["#f5c451", "#2fb7ff", "#e0458f", "#3ddc97", "#ff9a3c"]

    def player_display_name(self, p):
        ag = ASSETS.agents.get(p.get("agent") or "", {})
        name = p["name"] if p.get("name") else (ag.get("name") or "Player")
        if self.streamer() and not p.get("me"):
            name = ag.get("name") or "Player"
        return name

    def open_player(self, p):
        PlayerLayer(self, p, self.player_display_name(p))

    def open_match(self, m, mt):
        f = MATCH_DIR / f"{mt.get('id')}.json"
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            d = None
        tried = self.__dict__.setdefault("_match_tried", set())
        if (d is None or not d.get("v")) and not getattr(self, "_match_fetch", None) \
                and mt.get("id") not in tried:
            tried.add(mt.get("id"))
            # older cache files only kept your own numbers - grab the full match once
            if self.state_.get("active") and m.get("puuid") == self.m(
                    self.state_.get("active")).get("puuid"):
                self._match_fetch = mt.get("id")
                self.toast("Loading the full scoreboard…", "info", tray=False)

                def work():
                    try:
                        vc, _ = self.get_vc()
                        full = slim_match(vc.pd(f"/match-details/v1/matches/{mt['id']}",
                                                timeout=20))
                        MATCH_DIR.mkdir(parents=True, exist_ok=True)
                        f.write_text(json.dumps(full), encoding="utf-8")
                    except Exception:
                        pass
                    self.call_ui(lambda: (setattr(self, "_match_fetch", None),
                                          self.open_match(m, mt) if f.exists() else
                                          self.toast("Couldn't load that match.", "bad")))
                threading.Thread(target=work, daemon=True).start()
                return
        if d is None:
            self.toast("That match isn't cached any more - refresh stats to load it again.",
                       "bad")
            return
        known = {mm.get("puuid"): (f"{mm['game_name']}#{mm.get('tag', '')}"
                                   if mm.get("game_name") else n)
                 for n, mm in ((n, self.m(n)) for n in self.accounts()) if mm.get("puuid")}
        try:
            det = match_detail(d, m.get("puuid"), known)
        except Exception as e:
            self.toast(f"Couldn't read that match: {describe_err(e)}", "bad")
            return
        if self.streamer():
            for t in det["teams"]:
                for r in t["rows"]:
                    if not r["me"]:
                        r["name"] = (ASSETS.agents.get(r["agent"]) or {}).get("name") or "Player"
        MatchLayer(self, det)

    # ---- agent picker / tab overlay
    def open_picker(self):
        if self.picker:
            try:
                if self.picker.winfo_exists():
                    self.picker.locked_at = None
                    self.picker.render()
                    return
            except tk.TclError:
                pass
        self.picker = AgentPicker(self)

    def close_picker(self):
        if self.picker:
            self.picker.destroy()
        self.picker = None

    def toggle_fav_agent(self, aid):
        favs = list(self.settings.get("fav_agents") or [])
        if aid in favs:
            favs.remove(aid)
        else:
            favs.append(aid)
        self.set_setting("fav_agents", favs)
        name = ASSETS.agents.get(aid, {}).get("name", "")
        self.toast(f"{name} {'added to' if aid in favs else 'removed from'} favourites",
                   "info", tray=False)
        if self.picker:
            self.picker.render()
        self.redraw()

    def picker_pick(self, aid, lock):
        d = self.live or {}
        mid = d.get("match_id")
        if not mid or d.get("phase") != "pregame" or d.get("my_locked"):
            return

        def go():
            vc, region = self.get_vc()
            pregame_action(vc, region, mid, aid, False)
            if lock:
                pregame_action(vc, region, mid, aid, True)

            def done():
                self.live.update({"my_agent": aid, "my_locked": lock})
                if self.picker:
                    self.picker.render()
                self.redraw()
                self.after(400, self.refresh_live)
            self.call_ui(done)
        self.run_soon(go, lock)

    def open_leaderboard(self):
        self.soc_tab = "leaderboard"
        self.set_page("social")

    def leave_pregame(self):
        mid = (self.live or {}).get("match_id")
        if not mid or (self.live or {}).get("phase") != "pregame":
            return
        if not self.confirm("Leave this match?", "This is the same as dodging in the game: "
                            "you get the usual dodge penalty (lost RR in competitive and a short "
                            "queue lockout).", ok="Leave match", danger=True):
            return

        def go():
            vc, region = self.get_vc()
            pregame_quit(vc, region, mid)
            self.set_status("Left the match.", "good")
            self.call_ui(self.refresh_live)
        self.run(go, guard=False)

    def live_row(self, x, y, w, p):
        col = SOFT if p["me"] else (ACCENT if p["party"] else LINE)
        rkey = f"lrow:{p['puuid']}"
        hov = self.hover == rkey
        rtags = self.hit(rkey, click=lambda p=p: self.open_player(p),
                         tip="See their loadout")
        base = mix(SURFACE, ACCENT, 0.12) if p["me"] else SURFACE
        self.rrect(x, y, x + w, y + 58, 12, fill=mix(base, CARD_HI, 0.5) if hov else base,
                   outline=col, width=2 if p["party"] or p["me"] else 1, tags=rtags)
        if p.get("group") is not None:
            gc = self.PARTY_COLORS[p["group"] % len(self.PARTY_COLORS)]
            self.rrect(x + 2, y + 10, x + 6, y + 48, 2, fill=gc)
        sk = p.get("skins") or {}
        for wi, wname in enumerate(("Vandal", "Phantom")):
            wid = (ASSETS.weapon_by_name.get(wname) or "").lower()
            su = sk.get(wid)
            info = ASSETS.skins.get(su or "")
            if info and w > 620:
                tags = self.hit(f"lsk:{p['puuid']}:{wi}", click=lambda su=su: SkinDialog(self, su),
                                tip=info["name"]) + rtags
                self.image(info["icon"], x + w * 0.40, y + 8 + wi * 22, 74, 20,
                           tags=tags)
        ag = ASSETS.agents.get(p["agent"], {})
        if not self.image(ag.get("icon"), x + 9, y + 9, 40, 40, radius=10, tags=rtags):
            self.rrect(x + 9, y + 9, x + 49, y + 49, 10, fill=CARD)
            if not p["agent"]:
                self.text(x + 29, y + 29, "?", 12, "bold", DIM, anchor="center")
        name = self.player_display_name(p)
        nm_col = TEXT if p["name"] else MUTED
        self.text(x + 62, y + 21, name + ("  (you)" if p["me"] else ""), 10, "bold", nm_col,
                  maxw=w * 0.28, tags=rtags)
        bits = []
        if p.get("level"):
            bits.append(f"Lvl {p['level']}")
        if p["hidden"]:
            bits.append("Hidden name")
        if p["party"] and not p["me"]:
            bits.append("Your party")
        if p.get("locked"):
            bits.append("Locked in")
        if p.get("group") is not None and not p["party"]:
            bits.append(f"Party {chr(65 + p['group'])}")
        enc = (self.enc or {}).get(p["puuid"])
        if enc and not p["me"]:
            bits.append(f"Played with {enc['n']}×")
        self.text(x + 62, y + 40, "  ·  ".join(bits) or ag.get("name", ""), 8,
                  fill=GOLD if enc and not p["me"] else MUTED, maxw=w * 0.29, tags=rtags)
        rx = x + w * 0.52
        if self.settings.get("focus_mode") and not p["me"]:
            self.text(rx + 14, y + 29, "Ranks hidden (focus mode)", 8, fill=DIM)
            return
        if p["tier"] >= 3:
            self.rank_icon(p["tier"], rx + 14, y + 29, 30, tags=rtags)
        tc = ASSETS.tier_color(p["tier"]) or MUTED
        self.text(rx + 34, y + 21, ASSETS.tier_name(p["tier"]), 10, "bold",
                  mix(tc, "#ffffff", 0.35), maxw=w * 0.22, tags=rtags)
        self.text(rx + 34, y + 40, f"{p['rr']} RR" if p["tier"] >= 3 else "", 8, fill=MUTED,
                  tags=rtags)
        px = x + w * 0.78
        if p["peak"] >= 3:
            self.rank_icon(p["peak"], px + 12, y + 29, 24)
            self.text(px + 28, y + 21, "Peak", 8, "bold", DIM)
            self.text(px + 28, y + 39, ASSETS.tier_name(p["peak"]), 8, "bold", MUTED,
                      maxw=w * 0.2)

    # ------------------------------------------------------------ friends & status
    def my_region(self):
        return (self.m(self.state_.get("active")).get("region")
                or next((self.m(n).get("region") for n in self.accounts()
                         if self.m(n).get("region")), None) or "eu")

    def draw_social(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 30 - self.scroll()
        top = y
        self.page_header(x0, x1, y, "chat", "Social", "friends, leaderboard and server status")
        # little live server indicator, top right
        reg = self.srv["region"] or self.my_region()
        if not self.srv["data"] and not self.srv["busy"]:
            self.load_server_status(reg)
        val = (self.srv["data"].get(reg) or {}).get("val")
        live = status_issues(val)
        col = MUTED if val is None else (self.LEVEL_LOOK[live[0]["level"]][1] if live else GOOD)
        lab = ("Checking servers…" if val is None else
               f"{len(live)} issue{'s' if len(live) != 1 else ''} · {reg.upper()}" if live else
               f"Servers OK · {reg.upper()}")
        tw = self.measure(lab, 9, "bold") + 40
        key = "soc:srvpill"
        tags = self.hit(key, click=lambda: self.set_soc_tab("servers"),
                        tip="VALORANT server status for your region")
        self.rrect(x1 - tw, y + 2, x1, y + 32, 15,
                   fill=mix(CARD, col, 0.2 if self.hover == key else 0.12), outline=mix(LINE, col, 0.5),
                   tags=tags)
        self.circle(x1 - tw + 18, y + 17, 5, fill=col, tags=tags)
        self.text(x1 - tw + 30, y + 17, lab, 9, "bold", tags=tags)
        y += 58
        self.chips(x0, y, [("friends", "Friends"), ("leaderboard", "Leaderboard"),
                           ("servers", "Server status")], self.soc_tab, self.set_soc_tab, "soct",
                   size=10, h=34)
        y += 54
        self.mark_tab_content(y)
        if self.soc_tab == "leaderboard":
            y = self.draw_leaderboard(x0, x1, y, h)
        elif self.soc_tab == "servers":
            y = self.draw_servers(x0, x1, y, h)
        else:
            y = self.draw_friends(x0, x1, y, h)
        self.finish_scroll(top, y + 10, h)

    def set_soc_tab(self, t):
        if t != self.soc_tab:
            order = ["friends", "leaderboard", "servers"]
            self.tab_switched((order.index(t) if t in order else 0)
                              - (order.index(self.soc_tab) if self.soc_tab in order else 0))
        self.soc_tab = t
        self.reset_scroll()
        self.redraw()

    # ---- friends
    def draw_friends(self, x0, x1, y, h):
        bw = x1 - x0
        now = time.time()
        stale = now - getattr(self, "friends_t", 0) > (15 if (self.friends_err or
                                                               self.friends is None) else 60)
        if stale and not getattr(self, "friends_busy", False):
            self.friends_t = now
            self.refresh_social()
        if (self.friends is None or self.friends_err) and not getattr(self, "_fr_retry", None):
            self._fr_retry = self.after(15500, lambda: (setattr(self, "_fr_retry", None),
                                                        self.redraw()))
        fr = self.friends or []
        online = [f for f in fr if f["online"]]
        self.section(x0, y, "person", "Friends", f"{len(online)} online of {len(fr)}  ·  "
                     "star someone to get an alert when they come online")
        self.action_button(x1, y - 2, "Refresh", self.refresh_social, "soc:refresh", "refresh",
                           anchor="e", primary=False, h=30)
        y += 44
        if self.friends is None and not self.friends_err:
            self.skeleton_rows(x0, x1, y, 4)
            return y + 4 * 58 + 12
        if self.friends_err and not fr:
            y = self.empty_state(x0, x1, y, "chat", "Friends aren't available right now",
                                 self.friends_err, ("Refresh", self.refresh_social,
                                                    "soc:retry", "refresh")) + 14
        elif self.friends_err:
            self.rrect(x0, y, x1, y + 56, 14, fill=SURFACE, outline=LINE)
            self.icon(x0 + 24, y + 28, "info", 12, MUTED)
            self.text(x0 + 46, y + 28, self.friends_err, 10, fill=MUTED, maxw=bw - 70)
            y += 70
        stars = set(self.state_.get("star_friends") or [])
        fr = sorted(fr, key=lambda f: (not f["online"], f["puuid"] not in stars,
                                       f["name"].lower()))
        cols = 3 if bw > 1100 else (2 if bw > 700 else 1)
        cw = (bw - (cols - 1) * 12) / cols
        for i, f in enumerate(fr):
            cx = x0 + (i % cols) * (cw + 12)
            cy = y + (i // cols) * 60
            if -60 < cy < h:
                col = GOOD if f["online"] and f["state"] in ("chat", "dnd") else (
                    GOLD if f["online"] else DIM)
                rk = "frow:" + str(f["puuid"])
                rt = self.hit(rk, click=lambda f=f: FriendLayer(self, f),
                              tip="Profile and messages", box=(cx, cy, cx + cw, cy + 50))
                base = SURFACE if f["online"] else mix(SURFACE, BG, 0.4)
                self.rrect(cx, cy, cx + cw, cy + 50, 14, fill=self.hcol(rk, base, CARD),
                           outline=LINE, tags=rt)
                self.letter_avatar(cx + 12, cy + 9, 32, f["name"], radius=10)
                self.circle(cx + 40, cy + 38, 5, fill=col)
                name = "Hidden" if self.streamer() else f["name"].split("#")[0]
                self.text(cx + 56, cy + 18, name, 10, "bold", TEXT if f["online"] else MUTED,
                          maxw=cw - 100)
                self.text(cx + 56, cy + 35, f["detail"] or ("Online" if f["online"] else
                                                            "Offline"), 8, fill=MUTED,
                          maxw=cw - 100)
                key = "fstar:" + str(f["puuid"])
                on = f["puuid"] in stars
                tg = self.hit(key, click=lambda pu=f["puuid"]: self.toggle_star_friend(pu),
                              tip="Alert me when they come online",
                              box=(cx + cw - 36, cy + 10, cx + cw - 8, cy + 40))
                self.icon(cx + cw - 22, cy + 25, "star_on" if on else "star", 11,
                          GOLD if on else self.hcol(key, DIM, SOFT), tags=tg)
                if f.get("pid"):
                    mk = "fmsg:" + str(f["puuid"])
                    mt = self.hit(mk, click=lambda f=f: FriendLayer(self, f, "chat"),
                                  tip="Message", box=(cx + cw - 68, cy + 10, cx + cw - 40,
                                                      cy + 40))
                    self.circle(cx + cw - 54, cy + 25, 14, fill=self.hcol(mk, SURFACE, CARD_HI),
                                tags=mt)
                    self.icon(cx + cw - 54, cy + 25, "chat", 10, self.hcol(mk, MUTED, TEXT),
                              tags=mt)
        y += ((len(fr) - 1) // cols + 1) * 60 + 10 if fr else 0
        others = [n for n in self.accounts() if n != self.state_.get("active")
                  and self.m(n).get("friends")]
        if others and self.state_.get("active"):
            self.section(x0, y, "copy", "Copy friends",
                         f"send requests from {self.state_.get('active')} to another account's "
                         "friends")
            y += 40
            cx = x0
            for n in others:
                lab = f"From {n}  ·  {len(self.m(n)['friends'])}"
                key = "cpf:" + n
                hov = self.hover == key
                tags = self.hit(key, click=lambda n=n: self.copy_friends(n),
                                tip=f"Add {n}'s friends to {self.state_.get('active')}")
                tw = self.measure(lab, 9, "bold") + 30
                if cx + tw > x1:
                    cx = x0
                    y += 36
                self.rrect(cx, y, cx + tw, y + 28, 14, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags)
                self.text(cx + tw / 2, y + 14, lab, 9, "bold", self.hcol(key, MUTED, TEXT, hov),
                          anchor="center", tags=tags)
                cx += tw + 8
            y += 46
        return y

    # ---- servers
    def load_server_status(self, region):
        self.srv["busy"] = True
        self.srv["region"] = region

        def work():
            res = {}
            for g in ("val", "lol"):
                try:
                    res[g] = game_status(g, region)
                except Exception:
                    res[g] = None

            def done():
                self.srv["busy"] = False
                self.srv["data"][region] = res
                self.srv["t"] = time.time()
                self.status_items = res.get("val")
                self.redraw()
            self.call_ui(done)
        threading.Thread(target=work, daemon=True).start()

    LEVEL_LOOK = {"critical": ("Outage", "#ff5c7a"), "warning": ("Issue", "#ffb547"),
                  "maint": ("Maintenance", "#ffb547"), "info": ("Notice", "#5aa9ff")}

    def draw_servers(self, x0, x1, y, h):
        reg = self.srv["region"] or self.my_region()
        self.chips(x0, y, [(k, v) for k, v in STATUS_REGIONS.items()], reg,
                   lambda r: self.load_server_status(r), "sreg", size=9, h=30)
        self.action_button(x1, y - 2, "Refresh", lambda: self.load_server_status(reg),
                           "srv:refresh", "refresh", anchor="e", primary=False, h=30)
        y += 50
        data = self.srv["data"].get(reg)
        if data is None:
            self.text(x0 + 4, y + 8, "Checking Riot's status pages…", 9, "bold", DIM)
            return self.skeleton_rows(x0, x1, y + 24, 2, 64, avatar=False) + 10
        for g, title in (("val", "VALORANT"), ("lol", "League of Legends / TFT")):
            items = data.get(g)
            issues = status_issues(items)
            mine = [e for e in items or [] if e.get("pc", True) and not e.get("old")]
            notes = [e for e in mine if e not in issues]
            later = [e for e in items or [] if e not in mine]
            worst = issues[0]["level"] if issues else None
            col = MUTED if items is None else (self.LEVEL_LOOK[worst][1] if worst else GOOD)
            head = ("Couldn't reach the status page" if items is None else
                    "All systems normal" if not issues else
                    f"{len(issues)} issue{'s' if len(issues) != 1 else ''} affecting PC")
            self.rrect(x0, y, x1, y + 64, 16, fill=mix(SURFACE, col, 0.07),
                       outline=mix(LINE, col, 0.4))
            self.circle(x0 + 30, y + 32, 9, fill=mix(SURFACE, col, 0.3))
            self.circle(x0 + 30, y + 32, 5, fill=col)
            self.text(x0 + 52, y + 22, title, 12, "bold")
            self.text(x0 + 52, y + 43, head, 9, fill=col if issues else MUTED)
            self.text(x1 - 20, y + 32, STATUS_REGIONS.get(reg, reg.upper()), 9, "bold", DIM,
                      anchor="e")
            y += 74
            for e in issues + notes:
                y = self.status_row(x0 + 18, x1, y, e)
            if later:
                k = f"srv:more:{g}"
                opened = k in self.srv.setdefault("open", set())
                lab = (f"{'Hide' if opened else 'Show'} {len(later)} older or other-platform "
                       f"notice{'s' if len(later) != 1 else ''}")
                tw = self.measure(lab, 8, "bold") + 26
                tags = self.hit(k, click=lambda k=k: (self.srv["open"].symmetric_difference_update(
                    {k}), self.redraw()), box=(x0 + 18, y, x0 + 18 + tw, y + 26))
                self.rrect(x0 + 18, y, x0 + 18 + tw, y + 26, 13,
                           fill=self.hcol(k, CARD, CARD_HI), tags=tags)
                self.text(x0 + 31, y + 13, lab, 8, "bold", self.hcol(k, DIM, TEXT), tags=tags)
                y += 34
                if opened:
                    for e in later:
                        y = self.status_row(x0 + 18, x1, y, e, faded=True)
            y += 14
        return y

    def status_row(self, x0, x1, y, it, faded=False):
        bw = x1 - x0
        lab, col = self.LEVEL_LOOK.get(it.get("level", "warning"))
        if faded:
            col = mix(col, MUTED, 0.6)
        rh = 64 if it.get("note") else 44
        self.rrect(x0, y, x1, y + rh, 12, fill=SURFACE, outline=LINE)
        self.rrect(x0, y + 10, x0 + 3, y + rh - 10, 1, fill=col)
        bits = [lab]
        if it.get("platforms"):
            bits.append(", ".join({"macos": "Mac", "windows": "PC", "ps5": "PS5",
                                   "xbox": "Xbox"}.get(p_.lower(), p_.title())
                                  for p_ in it["platforms"]))
        upd = _parse_time(it.get("updated"))
        if upd:
            bits.append(ago(upd.timestamp(), "updated"))
        self.text(x0 + 18, y + 16, it["title"], 10, "bold", MUTED if faded else TEXT,
                  maxw=bw * 0.6)
        self.text(x1 - 16, y + 16, "  ·  ".join(bits), 8, "bold", col, anchor="e",
                  maxw=bw * 0.38)
        if it.get("note"):
            self.text(x0 + 18, y + 40, it["note"], 9, fill=MUTED, maxw=bw - 36)
        return y + rh + 8

    # ---- leaderboard
    def load_leaderboard(self, region=None, page=None):
        lb = self.lb
        lb["region"] = region or lb["region"] or self.my_region()
        lb["page"] = page or lb["page"] or 1
        lb["busy"], lb["err"], lb["need_key"] = True, None, False
        reg, pg = lb["region"], lb["page"]
        key = self.settings.get("henrik_key") or None

        def work():
            rows = total = err = None
            need = False
            try:
                rows, total = henrik_leaderboard(reg, pg, 50, key)
            except NeedKey:
                need = True
            except Exception as e:
                err = describe_err(e)
            if rows is None and self.state_.get("active"):
                # fall back to the game's own leaderboard through your Riot session
                try:
                    vc, _ = self.get_vc()
                    rows, total = fetch_leaderboard(vc, reg, (pg - 1) * 50, 50)
                    need, err = False, None
                except Exception as e:
                    err = err or describe_err(e)

            def done():
                if (lb["region"], lb["page"]) != (reg, pg):
                    return
                lb.update(busy=False, rows=rows, total=total or 0, err=err, need_key=need)
                self.redraw()
            self.call_ui(done)
        threading.Thread(target=work, daemon=True).start()

    def set_henrik_key(self):
        k = self.ask("HenrikDev API key", "Paste your free key from the HenrikDev dashboard. "
                     "It's used for the leaderboard and for keeping every account's rank up to "
                     "date without logging into each one.", self.settings.get("henrik_key") or "")
        if k is None:
            return
        self.set_setting("henrik_key", k.strip())
        self.lb["rows"] = None
        self.load_leaderboard()
        self.refresh_external(force=True)

    def draw_leaderboard(self, x0, x1, y, h):
        lb = self.lb
        bw = x1 - x0
        if lb["rows"] is None and not lb["busy"] and not lb["err"] and not lb["need_key"]:
            self.load_leaderboard()
        reg = lb["region"] or self.my_region()
        self.chips(x0, y, [(k, k.upper()) for k in STATUS_REGIONS], reg,
                   lambda r: (self.lb.update(rows=None), self.load_leaderboard(r, 1)), "lbreg",
                   size=9, h=30)
        pg = lb["page"]
        nx = self.action_button(x1, y - 2, "Next  ›", lambda: self.load_leaderboard(page=pg + 1),
                                "lb:next", None, primary=False, anchor="e", h=30,
                                disabled=lb["busy"] or not lb["rows"])
        self.action_button(x1 - nx - 8, y - 2, "‹  Prev",
                           lambda: self.load_leaderboard(page=max(1, pg - 1)), "lb:prev", None,
                           primary=False, anchor="e", h=30, disabled=lb["busy"] or pg <= 1)
        y += 48
        if lb["need_key"]:
            self.rrect(x0, y, x1, y + 120, 18, fill=SURFACE, outline=LINE)
            self.icon(x0 + 30, y + 34, "trophy", 16, GOLD)
            self.text(x0 + 56, y + 34, "One quick step to unlock the leaderboard", 13, "bold")
            self.text(x0 + 56, y + 58, "Rankings come from HenrikDev's free VALORANT API. Grab a "
                      "free key (sign in with Discord), paste it here, done.", 9, fill=MUTED,
                      maxw=bw - 90)
            bx = self.action_button(x0 + 56, y + 76, "Get a free key",
                                    lambda: webbrowser.open(HENRIK_KEY_URL), "lb:getkey", "link",
                                    h=30)
            self.action_button(x0 + 56 + bx + 10, y + 76, "Paste key", self.set_henrik_key,
                               "lb:paste", "copy", primary=False, h=30)
            return y + 136
        if lb["busy"] and not lb["rows"]:
            return self.skeleton_rows(x0, x1, y, 8, 52)
        if lb["err"] and not lb["rows"]:
            return self.empty_state(x0, x1, y, "trophy", "Couldn't load the leaderboard",
                                    str(lb["err"]), ("Try again",
                                                     lambda: self.load_leaderboard(),
                                                     "lb:retry", "refresh"), tone=GOLD) + 10
        rows = lb["rows"] or []
        mine = {self.m(n).get("puuid") for n in self.accounts() if self.m(n).get("puuid")}
        sub = f"{ASSETS.current_act_label or 'This act'}  ·  {STATUS_REGIONS.get(reg, reg)}"
        if lb["total"]:
            sub += f"  ·  {lb['total']:,} ranked players"
        self.text(x0, y + 8, sub, 9, "bold", DIM)
        y += 30
        # podium for the top 3
        if pg == 1 and len(rows) >= 3:
            pw = (bw - 24) / 3
            for i, r in enumerate(rows[:3]):
                px = x0 + i * (pw + 12)
                medal = ("#f5c451", "#c9d1e0", "#d99a5b")[i]
                card = ASSETS.cards.get(r.get("card") or "", {})
                if not self.image(card.get("wide"), px, y, pw, 110, mode="cover", radius=16,
                                  fade=True):
                    self.rrect(px, y, px + pw, y + 110, 16, fill=mix(SURFACE, medal, 0.12))
                self.rrect(px, y, px + pw, y + 110, 16, fill="", outline=mix(LINE, medal, 0.7),
                           width=2 if r["puuid"] in mine else 1)
                self.circle(px + 30, y + 30, 16, fill=medal)
                self.text(px + 30, y + 30, str(r["rank"]), 11, "bold", BG, anchor="center")
                name = "Hidden" if self.streamer() and not r["anon"] else r["name"]
                self.text(px + 18, y + 66, name.split("#")[0], 13, "bold", "#ffffff",
                          maxw=pw - 90)
                self.text(px + 18, y + 90, f"{r['rr']:,} RR  ·  {r['wins']} wins", 9, "bold",
                          SOFT)
                self.rank_icon(r["tier"], px + pw - 52, y + 30, 36)
            y += 126
            rows = rows[3:]
        for i, r in enumerate(rows):
            ry = y + i * 48
            if -48 < ry < h:
                me = r["puuid"] in mine
                self.rrect(x0, ry, x1, ry + 42, 12,
                           fill=mix(SURFACE, ACCENT, 0.18) if me else SURFACE,
                           outline=ACCENT if me else "")
                self.text(x0 + 46, ry + 21, f"#{r['rank']}", 10, "bold",
                          GOLD if (r["rank"] or 999) <= 10 else SOFT, anchor="e")
                card = ASSETS.cards.get(r.get("card") or "", {})
                if not self.image(card.get("small"), x0 + 58, ry + 5, 32, 32, radius=8):
                    self.rrect(x0 + 58, ry + 5, x0 + 90, ry + 37, 8, fill=CARD)
                name = "Hidden" if self.streamer() and not r["anon"] else r["name"]
                nm, _, tg = name.partition("#")
                self.text(x0 + 104, ry + 21, nm, 10, "bold", MUTED if r["anon"] else TEXT,
                          maxw=bw * 0.4)
                if tg and not r["anon"]:
                    self.text(x0 + 110 + min(self.measure(nm, 10, "bold"), bw * 0.4), ry + 21,
                              "#" + tg, 9, fill=DIM)
                self.rank_icon(r["tier"], x0 + bw * 0.62, ry + 21, 26)
                self.text(x0 + bw * 0.62 + 22, ry + 21, f"{r['rr']:,} RR", 10, "bold")
                self.text(x1 - 20, ry + 21, f"{r['wins']} wins", 9, fill=MUTED, anchor="e")
        return y + len(rows) * 48

    # ------------------------------------------------------------ store
    def store_hits(self):
        """[(skin, account, price)] wishlisted skins currently in someone's store."""
        memo = getattr(self, "_hits_memo", None)
        if memo and time.time() - memo[0] < 1.0:
            return memo[1]
        res = self._store_hits()
        self._hits_memo = (time.time(), res)
        return res

    def _store_hits(self):
        wish = set(self.state_["wishlist"])
        if not wish:
            return []
        now = time.time()
        out = []
        for name in self.accounts():
            st = self.m(name).get("store") or {}
            if st.get("daily_expires", 0) > now:
                for o in st.get("daily") or []:
                    if o["skin"] in wish:
                        out.append((o["skin"], name, o.get("cost")))
            if st.get("night_expires", 0) > now:
                for o in st.get("night") or []:
                    if o["skin"] in wish:
                        out.append((o["skin"], name, o.get("price") or o.get("cost")))
        return out

    def store_card(self, x, y, cw, ch, skin, owner, price, extra=None, key="", wallet=None):
        s = ASSETS.skins.get(skin)
        k = f"st:{key}"
        hov = self.hover == k
        tags = self.hit(k, click=(lambda: SkinDialog(self, skin, owner)) if s else None)
        ct = ASSETS.ctiers.get((s or {}).get("tier") or "", {})
        col = ct.get("color")
        wish = skin in self.state_["wishlist"]
        fill = mix(SURFACE, col, 0.18) if col else SURFACE
        if hov:
            self.glow(x, y, x + cw, y + ch, 14, col or ACCENT, tags)
        self.rrect(x, y, x + cw, y + ch, 14, fill=mix(fill, "#ffffff", 0.04) if hov else fill,
                   outline=GOLD if wish else (self.hcol(k, LINE, ACCENT, hov)), width=2 if wish else 1,
                   tags=tags)
        if col:
            self.rrect(x + 14, y, x + cw - 14, y + 3, 1, fill=col)
        if s:
            self.image(s["icon"], x + 14, y + 16, cw - 28, ch - 70, tags=tags)
            self.text(x + 14, y + ch - 38, s["name"], 10, "bold", maxw=cw - 50, tags=tags)
            if ct.get("icon"):
                self.image(ct["icon"], x + cw - 30, y + ch - 46, 16, 16, tags=tags)
        else:
            self.text(x + 14, y + ch - 38, "Unknown item", 10, "bold", MUTED, tags=tags)
        if price is not None:
            if not self.image(ASSETS.currency_icons.get(VP), x + 14, y + ch - 25, 14, 14,
                              tags=tags):
                self.circle(x + 20, y + ch - 18, 4, fill=SOFT)
            short = wallet is not None and price > wallet
            self.text(x + 34, y + ch - 18, f"{price:,}", 10, "bold", DANGER if short else TEXT,
                      tags=tags)
        if extra:
            self.text(x + cw - 14, y + ch - 18, extra, 9, "bold", GOOD, anchor="e", tags=tags)
        skey = f"sstar:{key}"
        st = self.hit(skey, click=lambda: self.toggle_wish(skin),
                      tip="Remove from wishlist" if wish else "Add to wishlist")
        if wish or hov or self.hover == skey:
            self.circle(x + cw - 20, y + 20, 13, fill=mix(SURFACE, GOLD, 0.2) if wish else CARD,
                        tags=st)
            self.icon(x + cw - 20, y + 20, "star_on" if wish else "star", 10,
                      GOLD if wish else MUTED, tags=st)

    def draw_store(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 30 - self.scroll()
        top = y
        bw = x1 - x0
        self.page_header(x0, x1, y, "shop", "Store & wishlist",
                         "your shop, night market and bundles")
        active = self.state_.get("active")
        scanning = bool(getattr(self, "scan", None))
        rw = self.action_button(x1, y + 2, "Checking shops…" if scanning else "Check every shop",
                                self.scan_all_shops, "store:scan", "refresh", anchor="e",
                                disabled=self.busy or scanning,
                                tip="Logs into each account for a few seconds to grab its shop, "
                                    "then switches back")
        if active:
            busy = active in self.fetching
            self.action_button(x1 - rw - 10, y + 2, "Refreshing…" if busy else "Refresh",
                               lambda: self.refresh_stats(active), "store:refresh", None,
                               anchor="e", disabled=busy, primary=False)
        y += 60
        # account switcher
        accs = [n for n in self.accounts() if not self.m(n).get("archived")]
        if active in accs:
            accs.remove(active)
            accs.insert(0, active)
        if self.store_acc not in accs:
            self.store_acc = accs[0] if accs else None
        hits_by = {}
        for sk, a, _ in self.store_hits():
            hits_by[a] = hits_by.get(a, 0) + 1
        now = time.time()
        cx = x0
        for n in accs:
            st_ = self.m(n).get("store") or {}
            fresh = st_.get("daily_expires", 0) > now
            lab = n
            tw = self.measure(lab, 10, "bold") + 62 + (22 if hits_by.get(n) else
                                                          (6 if not fresh else -6))
            if cx + tw > x1:
                cx = x0
                y += 50
            key = "sacc:" + n
            on = n == self.store_acc
            hov = self.hover == key
            tags = self.hit(key, click=lambda n=n: self.set_store_acc(n),
                            tip=("Today's shop" if fresh else "Shop expired - log in to refresh")
                            + (f" · {hits_by[n]} wishlisted skin here!" if hits_by.get(n) else ""))
            self.rrect(cx, y, cx + tw, y + 42, 21,
                       fill=ACCENT if on else (self.hcol(key, CARD, CARD_HI, hov)), tags=tags)
            self.account_art(cx + 5, y + 5, 32, n, 16, tags=tags)
            self.text(cx + 46, y + 21, lab, 10, "bold", TEXT if on or hov or fresh else MUTED,
                      tags=tags)
            if hits_by.get(n):
                self.circle(cx + tw - 18, y + 21, 9, fill=GOLD, tags=tags)
                self.text(cx + tw - 18, y + 21, "★", 8, "bold", BG, anchor="center", tags=tags)
            elif not fresh:
                self.circle(cx + tw - 16, y + 21, 3, fill=DIM, tags=tags)
            cx += tw + 8
        y += 62

        names = [self.store_acc] if self.store_acc else []
        for name in names:
            m = self.m(name)
            st = m.get("store") or {}
            self.text(x0, y + 10, "Daily shop", 13, "bold")
            if st.get("daily_expires", 0) > now:
                info = f"Resets in {dur(st['daily_expires'] - now)}"
                fg = MUTED
            elif st:
                info = "Expired. Log into this account to see today's store."
                fg = DIM
            else:
                info = "No store yet. Log into this account with RiotHub."
                fg = DIM
            self.text(x0, y + 30, info, 9, fill=fg)
            wallet = (m.get("wallet") or {}).get(VP)
            hist = m.get("store_history") or []
            hx = x1
            if st.get("daily_expires", 0) > now and HAS_PIL:
                key = "sshare:" + name
                hov = self.hover == key
                tw = self.measure("Share", 9, "bold") + 26
                tg = self.hit(key, click=lambda n=name: self.share_store(n),
                              tip="Save this store as an image")
                self.rrect(hx - tw, y + 4, hx, y + 30, 13, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tg)
                self.text(hx - tw / 2, y + 17, "Share", 9, "bold", self.hcol(key, MUTED, TEXT, hov),
                          anchor="center", tags=tg)
                hx -= tw + 8
            if len(hist) > 1:
                key = "shist:" + name
                on = name in self.show_history
                hov = self.hover == key
                lab = "Hide history" if on else f"History ({len(hist)})"
                tw = self.measure(lab, 9, "bold") + 26
                tags = self.hit(key, click=lambda n=name: self.toggle_history(n))
                self.rrect(hx - tw, y + 4, hx, y + 30, 13, fill=CARD_HI if hov or on else CARD,
                           tags=tags)
                self.text(hx - tw / 2, y + 17, lab, 9, "bold", TEXT if hov or on else MUTED,
                          anchor="center", tags=tags)
                hx -= tw + 12
            if wallet is not None and st.get("daily_expires", 0) > now:
                costs = sorted(o.get("cost") or 0 for o in st.get("daily") or [])
                n_aff, left = 0, wallet
                for c in costs:
                    if c and c <= left:
                        n_aff += 1
                        left -= c
                self.text(hx, y + 17, f"{self.money(wallet)} VP  ·  can afford {n_aff} of "
                                      f"{len(costs)}", 9, "bold", SOFT, anchor="e")
            y += 48
            daily = st.get("daily") or []
            if daily and st.get("daily_expires", 0) > now:
                n = len(daily)
                cw = (bw - (n - 1) * 12) / max(1, n)
                if y < h and y > -180:
                    for i, o in enumerate(daily):
                        self.store_card(x0 + i * (cw + 12), y, cw, 170, o["skin"], name,
                                        o.get("cost"), key=f"{name}:d:{i}",
                                        wallet=None if self.streamer() else wallet)
                y += 184
            if name in self.show_history:
                for hh in reversed(hist[-8:]):
                    if -50 < y < h:
                        self.rrect(x0, y, x1, y + 52, 12, fill=SURFACE, outline=LINE)
                        self.text(x0 + 16, y + 26, datetime.fromtimestamp(hh["t"]).strftime(
                            "%a %d %b"), 9, "bold", MUTED)
                        ix = x0 + 120
                        for su in hh.get("daily", []):
                            sk = ASSETS.skins.get(su)
                            if sk:
                                k2 = f"hs:{name}:{hh['k']}:{su}"
                                t2 = self.hit(k2, click=lambda su=su, n=name: SkinDialog(self, su, n),
                                              tip=sk["name"])
                                self.image(sk["icon"], ix, y + 8, 110, 36, tags=t2)
                                ix += 124
                    y += 58
            night = st.get("night") or []
            if night and st.get("night_expires", 0) > now:
                self.text(x0, y + 8, f"Night market  ·  ends in {dur(st['night_expires'] - now)}",
                          10, "bold", SOFT)
                y += 26
                n = len(night)
                cw = min(260, (bw - (n - 1) * 10) / max(1, n))
                if -150 < y < h:
                    revealed = set(self.state_.setdefault("revealed", []))
                    for i, o in enumerate(night):
                        k = f"{name}:{int(st['night_expires']) // 3600}:{i}"
                        cx = x0 + i * (cw + 10)
                        t0 = self.flips.get(k)
                        if k not in revealed and t0 is None:
                            hov = self.hover == "nm:" + k
                            tags = self.hit("nm:" + k, click=lambda k=k: self.flip_card(k),
                                            tip="Click to reveal")
                            self.rrect(cx, y, cx + cw, y + 150, 14,
                                       fill=mix(BRAND, ACCENT, (0.2 + (0.35 - 0.2) * self.hv(key, hov))),
                                       outline=self.hcol(key, LINE, SOFT, hov), tags=tags)
                            self.text(cx + cw / 2, y + 66, "?", 34, "bold",
                                      mix(SOFT, "#ffffff", 0.3), anchor="center", tags=tags)
                            self.text(cx + cw / 2, y + 112, "Reveal", 9, "bold", SOFT,
                                      anchor="center", tags=tags)
                            continue
                        age = time.time() - t0 if t0 else 1
                        if age < 0.42:
                            f = abs(math.cos(math.pi * age / 0.42))
                            ww = max(6, int(cw * f / 8) * 8)
                            if age < 0.21:
                                self.rrect(cx + (cw - ww) / 2, y, cx + (cw + ww) / 2, y + 150, 14,
                                           fill=mix(BRAND, ACCENT, 0.3), outline=LINE)
                            else:
                                self.rrect(cx + (cw - ww) / 2, y, cx + (cw + ww) / 2, y + 150, 14,
                                           fill=SURFACE, outline=GOLD)
                            self._more = True
                            continue
                        self.store_card(cx, y, cw, 150, o["skin"], name,
                                        o.get("price"), f"-{o.get('percent', 0)}%",
                                        key=f"{name}:n:{i}")
                y += 164
            if not (st.get("daily_expires", 0) > now):
                self.rrect(x0, y, x1, y + 120, 18, fill=SURFACE, outline=LINE)
                self.icon(x0 + 34, y + 60, "shop", 18, DIM)
                self.text(x0 + 64, y + 48, f"{name}'s shop has reset since you last saw it", 12,
                          "bold")
                self.text(x0 + 64, y + 72, "Log into it, or press Check every shop to grab "
                          "every account's shop in one go.", 9, fill=MUTED, maxw=bw - 260)
                if name != active:
                    self.action_button(x1 - 20, y + 42, f"Log into {name}",
                                       lambda n=name: self.switch(n, game="Client only"),
                                       f"slog:{name}", "play", anchor="e", h=34)
                y += 136
            bundles = [b for b in st.get("bundles") or [] if b.get("expires", 0) > now]
            if bundles:
                for b in bundles[:2]:
                    info = ASSETS.bundles.get(b.get("id") or "", {})
                    bh = 130
                    if -bh < y < h:
                        if not self.image(info.get("icon"), x0, y, bw, bh, mode="cover",
                                          radius=16, fade=True):
                            self.rrect(x0, y, x1, y + bh, 16, fill=CARD)
                        self.text(x0 + 24, y + 34, "Featured bundle", 9, "bold", SOFT)
                        self.text(x0 + 24, y + 62, info.get("name", "Bundle"), 18, "bold")
                        self.text(x0 + 24, y + 94, f"{b.get('price') or 0:,} VP  ·  "
                                                   f"{len(b.get('skins') or [])} skins  ·  ends "
                                                   f"in {dur(b['expires'] - now)}", 10, fill=TEXT)
                    y += bh + 12
            y += 16
        wish = self.state_["wishlist"]
        hits = {(s, a) for s, a, _ in self.store_hits()}
        budget = sum(ASSETS.skin_price(su) or 0 for su in wish)
        self.section(x0, y, "star_on", "Wishlist",
                     f"{len(wish)} skin{'s' if len(wish) != 1 else ''}"
                     + (f"  ·  {budget:,} VP total" if budget else "")
                     + "  ·  star skins anywhere to get alerts")
        y += 40
        if not wish:
            self.rrect(x0, y, x1, y + 64, 14, fill=SURFACE, outline=LINE)
            self.text(x0 + 20, y + 32, "Nothing wishlisted yet. Tap the ☆ on any skin in a "
                                       "store, inventory or collection.", 10, fill=MUTED)
            y += 80
        else:
            wx = x0
            for su in wish:
                s = ASSETS.skins.get(su)
                if not s:
                    continue
                where = [a for (sk, a) in hits if sk == su]
                ww = 200
                if wx + ww > x1:
                    wx = x0
                    y += 92
                key = "wish:" + su
                hov = self.hover == key
                tags = self.hit(key, click=lambda su=su: SkinDialog(self, su, self.selected))
                self.rrect(wx, y, wx + ww, y + 80, 14,
                           fill=mix(SURFACE, GOLD, 0.12) if where else
                           (self.hcol(key, SURFACE, CARD_HI, hov)),
                           outline=GOLD if where else LINE, tags=tags)
                self.image(s["icon"], wx + 10, y + 10, 84, 44, tags=tags)
                self.text(wx + 102, y + 24, s["name"], 9, "bold", maxw=ww - 110, tags=tags)
                p = ASSETS.skin_price(su)
                self.text(wx + 102, y + 42, f"{p:,} VP" if p else s["weapon"], 9, fill=MUTED,
                          tags=tags)
                seen = None if where else last_seen(
                    {n: self.m(n) for n in self.accounts()}, su)
                self.text(wx + 12, y + 66, ("In store: " + ", ".join(where)) if where
                          else (f"Last seen: {seen[0]}, {ago(seen[1], '').strip()}" if seen
                                else "Not seen in a store yet"), 8, "bold",
                          GOLD if where else DIM, maxw=ww - 24, tags=tags)
                skey = "wdel:" + su
                st = self.hit(skey, click=lambda su=su: self.toggle_wish(su),
                              tip="Remove from wishlist")
                if hov or self.hover == skey:
                    self.circle(wx + ww - 16, y + 16, 11, fill=CARD, tags=st)
                    self.icon(wx + ww - 16, y + 16, "close", 8, MUTED, tags=st)
                wx += ww + 10
            y += 98

        self.finish_scroll(top, y, h)

    def set_store_acc(self, n):
        self.store_acc = n
        self.redraw()

    # ---- check every shop
    def scan_all_shops(self):
        if self.busy or getattr(self, "scan", None):
            return
        g = games_running()
        if g:
            self.notify("Game running", f"Close {', '.join(g)} first - checking shops restarts "
                                        "the Riot Client.")
            return
        names = [n for n in self.accounts() if not self.m(n).get("archived")
                 and has_login(ACC_DIR / n)]
        orig = self.state_.get("active")
        order = [n for n in names if n != orig] + ([orig] if orig in names else [])
        if not order:
            return
        if not self.confirm("Check every shop", f"RiotHub will log into {len(order)} "
                            f"account{'s' if len(order) != 1 else ''} one after another (about 20 "
                            "seconds each) to grab their shops"
                            + (f", then put you back on {orig}." if orig else "."),
                            ok="Start"):
            return
        self.scan = {"todo": order, "done": []}
        steps = [f"Checking {n}" for n in order]
        self.start_progress("Checking every shop", steps, order[0], "Hang tight")

        def work():
            found = 0
            for i, n in enumerate(order):
                self.step(i, f"Logging into {n}…")
                try:
                    ok = self.signed_in_as(self.state_.get("active")) if read_lockfile() else None
                    self._close_or_fail()
                    self._refresh_active(ok)
                    restore(ACC_DIR / n)
                    self.state_["active"] = n
                    self.state_["active_since"] = time.time()
                    save_state(self.state_)
                    self.launch(None)
                    self.watch_id += 1
                    res = self.wait_login(self.watch_id, total=60, after_seen=25)
                    if res == "ok":
                        self.step(i, f"Reading {n}'s shop…")
                        time.sleep(2)
                        self.load_stats(n, quiet=True)
                        self.keep_session_fresh(n)
                        found += 1
                    elif res == "expired":
                        self.call_ui(lambda n=n: self.update_meta(n, {"expired": True}))
                except Exception as e:
                    print("shop check failed for", n, describe_err(e))
                self.scan["done"].append(n)
            if orig and orig != order[-1]:
                try:
                    self._close_or_fail()
                    restore(ACC_DIR / orig)
                    self.state_["active"] = orig
                    self.launch(None)
                except Exception:
                    pass
            self.end_progress(None)

            def fin():
                self.scan = None
                hits = self.store_hits()
                if hits:
                    self.toast(f"★ {len(hits)} wishlisted skin{'s' if len(hits) != 1 else ''} "
                               "in your shops!", "wish")
                else:
                    self.toast(f"Checked {found} shop{'s' if found != 1 else ''}. Nothing from "
                               "your wishlist today.", "info")
                self.persist()
                self.redraw()
            self.call_ui(fin)
        self.run(work, guard=False)

    # ------------------------------------------------------------ compare
    def draw_compare(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 30 - self.scroll()
        top = y
        self.page_header(x0, x1, y, "compare", "Compare accounts",
                         "Click a column to sort, a row to open the profile")
        y += 62
        cols = [("account", "Account", 0.20), ("rank", "Rank", 0.17), ("peak", "Peak", 0.14),
                ("level", "Level", 0.07), ("skins", "Skins", 0.07), ("value", "Value (VP)", 0.09),
                ("vp", "VP", 0.07), ("week", "This week", 0.09), ("health", "Health", 0.10)]
        bw = x1 - x0
        xs = []
        cx = x0 + 16
        for k, label, frac in cols:
            xs.append(cx)
            cx += bw * frac
        sort_key, desc = self.compare_sort
        self.rrect(x0, y, x1, y + 40, 12, fill=CARD)
        for (k, label, _), cx in zip(cols, xs):
            key = "csort:" + k
            hov = self.hover == key
            tags = self.hit(key, click=lambda k=k: self.set_compare_sort(k))
            arrow = (" ▼" if desc else " ▲") if sort_key == k else ""
            self.text(cx, y + 20, label + arrow, 9, "bold",
                      TEXT if sort_key == k or hov else MUTED, tags=tags)
        y += 50

        def row_data(n):
            m = self.m(n)
            val, _ = inventory_value(m) if ASSETS.ready else (0, 0)
            pens = bool((m.get("penalties") or {}).get("items")) or bool(m.get("expired"))
            return {"account": n.lower(), "rank": (m.get("tier") or 0) * 100 + (m.get("rr") or 0),
                    "peak": m.get("peak_tier") or 0, "level": m.get("level") or 0,
                    "skins": len(owned_skin_set(m)) if ASSETS.ready else 0, "value": val,
                    "vp": (m.get("wallet") or {}).get(VP, 0), "week": self.playtime(n)["week"],
                    "health": 0 if pens else 1, "_m": m, "_n": n}

        rows = [row_data(n) for n in self.accounts()]
        rows.sort(key=lambda r: r[sort_key], reverse=desc)
        best = {}
        for k in ("rank", "peak", "level", "skins", "value", "vp", "week"):
            vals = [r[k] for r in rows if r[k]]
            top = max(vals, default=0)
            best[k] = top if vals and sum(1 for v in vals if v == top) < len(rows) else None
        for r in rows:
            n, m = r["_n"], r["_m"]
            key = "crow:" + n
            hov = self.hover == key
            tags = self.hit(key, click=lambda n=n: self.open_profile(n),
                            right=lambda e, n=n: self.popup(e, n))
            self.rrect(x0, y, x1, y + 58, 12, fill=self.hcol(key, SURFACE, CARD_HI, hov), outline=LINE,
                       tags=tags)
            self.account_art(xs[0], y + 11, 36, n, 9, tags)
            self.text(xs[0] + 46, y + 21, n, 10, "bold", maxw=bw * 0.2 - 60, tags=tags)
            self.text(xs[0] + 46, y + 39, self.rid(m) or "—", 8, fill=MUTED,
                      maxw=bw * 0.2 - 60, tags=tags)
            for idx, ck in ((1, "tier"), (2, "peak_tier")):
                t = m.get(ck)
                if t and t >= 3:
                    self.rank_icon(t, xs[idx] + 12, y + 29, 26, tags)
                label = ASSETS.tier_name(t) if m.get("puuid") else "—"
                if idx == 1 and t and t >= 3:
                    label += f" · {m.get('rr', 0)}"
                bestc = (r["rank"] if idx == 1 else r["peak"]) == best["rank" if idx == 1 else
                                                                        "peak"] and t and t >= 3
                self.text(xs[idx] + 30, y + 29, label, 9, "bold",
                          GOLD if bestc and len(rows) > 1 else TEXT, maxw=bw * 0.15 - 36,
                          tags=tags)
            vals = [(3, "level", str(r["level"] or "—")),
                    (4, "skins", str(r["skins"] or "—")),
                    (5, "value", ("≈" + self.short_vp(r["value"])) if r["value"] else "—"),
                    (6, "vp", self.money(r["vp"]) if r["vp"] else "—"),
                    (7, "week", dur(r["week"]) if r["week"] >= 60 else "—")]
            for idx, k, s in vals:
                top_one = r[k] and r[k] == best[k] and len(rows) > 1
                vt = tags
                if k == "value" and r["value"]:
                    vt = self.hit(f"cval:{r['_n']}", click=lambda n=r["_n"]: self.open_profile(n),
                                  tip=f"About {r['value']:,} VP if you bought these skins at "
                                      "list price today (Select 875 · Deluxe 1,275 · Premium "
                                      "1,775 · Exclusive 2,175 · Ultra 2,475 · knives ×2). "
                                      "Free and battle pass skins count as 0; bundle "
                                      "discounts aren't taken off.")
                self.text(xs[idx], y + 29, s, 10, "bold", GOLD if top_one else TEXT, tags=vt)
            if m.get("expired"):
                self.pill(xs[8], y + 29, "Expired", fill=DANGER, fg="#fff", tags=tags)
            elif (m.get("penalties") or {}).get("items"):
                self.pill(xs[8], y + 29, "Restricted", fill=DANGER, fg="#fff", tags=tags)
            elif m.get("penalties"):
                self.pill(xs[8], y + 29, "Clear", fill=mix(SURFACE, GOOD, 0.3), fg=GOOD,
                          tags=tags)
            else:
                self.text(xs[8], y + 29, "—", 10, fill=MUTED, tags=tags)
            y += 66
        if not rows:
            self.text((x0 + x1) / 2, y + 30, "No accounts yet.", 11, fill=MUTED, anchor="center")
        y = self.draw_weeklies(x0, x1, y + 20, h)
        self.finish_scroll(top, y, h)

    def draw_weeklies(self, x0, x1, y, h):
        """Which accounts still have weeklies / battle pass to do, with time to reset."""
        rows = []
        for n in self.accounts():
            m = self.m(n)
            if m.get("archived"):
                continue
            ms = m.get("missions") or []
            wk = [x for x in ms if x["kind"] == "Weekly"]
            reset = min((x["expires"] for x in wk if x.get("expires")), default=None)
            bp = (m.get("contracts") or {}).get("bp")
            if wk or bp:
                rows.append((n, wk, reset, bp, m.get("updated")))
        if not rows:
            return y
        self.section(x0, y, "check", "Weekly missions",
                     "progress as of each account's last refresh")
        y += 44
        bw = x1 - x0
        for n, wk, reset, bp, upd in rows:
            done = sum(1 for x in wk if x["done"])
            all_done = wk and done == len(wk)
            self.rrect(x0, y, x1, y + 58, 14, fill=SURFACE, outline=LINE)
            self.account_art(x0 + 12, y + 11, 36, n, 10)
            self.text(x0 + 60, y + 21, n, 10, "bold")
            self.text(x0 + 60, y + 39, ago(upd, "updated"), 8, fill=DIM)
            # weeklies bar
            bx = x0 + bw * 0.28
            bwid = bw * 0.3
            if wk:
                self.text(bx, y + 18, f"Weeklies {done}/{len(wk)}", 9, "bold",
                          GOOD if all_done else TEXT)
                self.bar(bx, y + 36, bwid, done / len(wk), 6)
            else:
                self.text(bx, y + 29, "No weeklies loaded", 9, fill=DIM)
            # battle pass
            px = x0 + bw * 0.64
            if bp:
                self.text(px, y + 18, f"Pass level {bp['level']}/{bp['total']}", 9, "bold")
                self.bar(px, y + 36, bw * 0.2, bp["level"] / max(1, bp["total"]), 6)
            if reset and reset > time.time():
                self.text(x1 - 18, y + 29, f"resets in {dur(reset - time.time())}", 9, "bold",
                          GOLD if reset - time.time() < 86400 and not all_done else MUTED,
                          anchor="e")
            y += 66
        return y

    # ------------------------------------------------------------ settings sync
    def prefs_info(self, name):
        p = PREFS_DIR / f"{name}.json"
        return p.stat().st_mtime if p.exists() else None

    def prefs_backups(self, name):
        if not PREFS_BACKUP_DIR.exists():
            return []
        files = sorted(PREFS_BACKUP_DIR.glob(f"{name}__*.json"), reverse=True)
        return files[:6]

    def draw_sync(self, w, h):
        x0, x1 = self.SIDE + 36, w - 32
        y = 30 - self.scroll()
        top = y
        self.page_header(x0, x1, y, "copy", "Settings sync",
                         "Copy crosshair, sensitivity and keybinds between accounts")
        y += 62
        active = self.state_.get("active")
        bw = x1 - x0
        lw = bw * 0.55
        self.section(x0, y, "upload", "1  Copy from")
        self.section(x0 + lw + 24, y, "download", "2  Copy to")
        y += 40
        ly = y
        for n in self.accounts():
            ts = self.prefs_info(n)
            key = "ssrc:" + n
            on = self.sync_source == n
            hov = self.hover == key
            tags = self.hit(key, click=(lambda n=n: self.set_sync_source(n)) if ts else None,
                            tip=None if ts else "Log into this account once to save its settings")
            self.rrect(x0, ly, x0 + lw, ly + 56, 12,
                       fill=CARD_HI if on else self.hcol(key, SURFACE, CARD_HI, hov),
                       outline=ACCENT if on else LINE, width=2 if on else 1, tags=tags)
            self.account_art(x0 + 10, ly + 10, 36, n, 9, tags)
            self.text(x0 + 58, ly + 20, n, 10, "bold", TEXT if ts else DIM, tags=tags)
            self.text(x0 + 58, ly + 38, ago(ts, "Settings saved") if ts else "No settings saved yet",
                      9, fill=MUTED if ts else DIM, tags=tags)
            if on:
                self.icon(x0 + lw - 24, ly + 28, "check", 11, ACCENT)
            ly += 64
        rx = x0 + lw + 24
        ry = y
        self.rrect(rx, ry, x1, ry + 70, 12, fill=SURFACE, outline=LINE)
        if active:
            self.account_art(rx + 12, ry + 15, 40, active, 10)
            self.text(rx + 64, ry + 26, active, 11, "bold")
            self.text(rx + 64, ry + 46, "Currently logged in", 9, fill=GOOD)
        else:
            self.text(rx + 18, ry + 35, "Log into the account you want to copy settings to.", 10,
                      fill=MUTED, maxw=x1 - rx - 30)
        ry += 86
        self.text(rx, ry, "What to copy", 9, "bold", DIM)
        ry += 16
        cx = rx
        for k, label in SYNC_CATEGORIES.items():
            key = "scat:" + k
            on = k in self.sync_cats
            hov = self.hover == key
            tags = self.hit(key, click=lambda k=k: self.toggle_sync_cat(k))
            tw = self.measure(label, 9, "bold") + 40
            if cx + tw > x1:
                cx = rx
                ry += 38
            self.rrect(cx, ry, cx + tw, ry + 30, 15,
                       fill=ACCENT if on else (self.hcol(key, CARD, CARD_HI, hov)), tags=tags)
            self.icon(cx + 16, ry + 15, "check" if on else "add", 8, TEXT if on else MUTED,
                      tags=tags)
            self.text(cx + 28, ry + 15, label, 9, "bold", TEXT if on else self.hcol(key, MUTED, TEXT, hov),
                      tags=tags)
            cx += tw + 8
        ry += 48
        ok = bool(active and self.sync_source and self.sync_source != active and self.sync_cats)
        label = (f"Copy {self.sync_source} → {active}" if ok else
                 "Pick a different source account" if self.sync_source == active and active
                 else "Pick a source account")
        self.action_button(rx, ry, label, self.apply_sync, "sync:apply", "copy",
                           disabled=not ok or self.busy)
        ry += 48
        self.cv.create_text(rx, ry - 7, text="Your current settings are backed up first. "
                            "VALORANT picks them up the next time it starts.", anchor="nw",
                            font=(self.UI, 9), fill=MUTED, width=max(120, x1 - rx))
        ry += 40
        if active:
            backs = self.prefs_backups(active)
            self.text(rx, ry, f"Backups for {active}", 9, "bold", DIM)
            ry += 18
            if not backs:
                self.text(rx, ry + 6, "None yet.", 9, fill=DIM)
                ry += 24
            for f in backs:
                ts = f.stem.split("__")[-1]
                try:
                    when = datetime.strptime(ts, "%Y%m%d-%H%M%S").strftime("%d %b %H:%M")
                except ValueError:
                    when = ts
                key = "sback:" + f.name
                hov = self.hover == key
                tags = self.hit(key, click=lambda f=f: self.restore_prefs(f),
                                tip="Restore these settings")
                self.rrect(rx, ry, x1, ry + 34, 10, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags)
                self.icon(rx + 18, ry + 17, "history", 9, MUTED, tags=tags)
                self.text(rx + 36, ry + 17, when, 9, "bold", tags=tags)
                self.text(x1 - 14, ry + 17, "Restore", 9, "bold", self.hcol(key, MUTED, SOFT, hov),
                          anchor="e", tags=tags)
                ry += 40
        y = max(ly, ry) + 20
        self.section(x0, y, "eye", "Crosshair & keybind library",
                     "save from any account, apply to the logged-in one")
        y += 40
        self.text(x0, y + 12, "Save from", 9, "bold", DIM)
        cx = x0 + 74
        for n in self.accounts():
            if not self.prefs_info(n):
                continue
            key = "xsave:" + n
            hov = self.hover == key
            tags = self.hit(key, click=lambda n=n: self.save_crosshair(n),
                            tip=f"Save {n}'s crosshair (right-click: keybinds)",
                            right=lambda e, n=n: self.save_settings_preset(n, "keybinds"))
            tw = self.measure(n, 9, "bold") + 40
            if cx + tw > x1:
                cx = x0 + 74
                y += 34
            self.rrect(cx, y, cx + tw, y + 26, 13, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags)
            self.icon(cx + 14, y + 13, "add", 8, SOFT, tags=tags)
            self.text(cx + 26, y + 13, n, 9, "bold", self.hcol(key, MUTED, TEXT, hov), tags=tags)
            cx += tw + 8
        y += 42
        xs = self.state_.get("crosshairs") or []
        if not xs:
            self.rrect(x0, y, x1, y + 56, 12, fill=SURFACE, outline=LINE)
            self.text(x0 + 18, y + 28, "No crosshairs saved yet. Accounts appear above once "
                                       "they've been logged in with RiotHub.", 9,
                      fill=MUTED, maxw=x1 - x0 - 36)
            y += 70
        for ch in xs:
            key = "xapply:" + ch["name"]
            hov = self.hover == key
            tags = self.hit(key, click=lambda ch=ch: self.apply_crosshair(ch),
                            tip="Apply to the logged-in account")
            self.rrect(x0, y, x1, y + 52, 12, fill=self.hcol(key, SURFACE, CARD_HI, hov), outline=LINE,
                       tags=tags)
            self.circle(x0 + 26, y + 26, 13, fill=CARD, tags=tags)
            self.cv.create_line(x0 + 26, y + 18, x0 + 26, y + 23, fill=GOOD, width=2, tags=tags)
            self.cv.create_line(x0 + 26, y + 29, x0 + 26, y + 34, fill=GOOD, width=2, tags=tags)
            self.cv.create_line(x0 + 18, y + 26, x0 + 23, y + 26, fill=GOOD, width=2, tags=tags)
            self.cv.create_line(x0 + 29, y + 26, x0 + 34, y + 26, fill=GOOD, width=2, tags=tags)
            self.text(x0 + 52, y + 18, ch["name"] + ("  · keybinds" if ch.get("kind") ==
                                                    "keybinds" else ""), 10, "bold", tags=tags)
            self.text(x0 + 52, y + 36, f"From {ch.get('from', '?')}  ·  {ago(ch.get('t'), 'saved')}",
                      8, fill=MUTED, tags=tags)
            self.text(x1 - 60, y + 26, "Apply" if active else "Log in to apply", 9, "bold",
                      self.hcol(key, MUTED, SOFT, hov), anchor="e", tags=tags)
            dkey = "xdel:" + ch["name"]
            dt = self.hit(dkey, click=lambda ch=ch: self.delete_crosshair(ch), tip="Delete")
            self.text(x1 - 24, y + 26, "✕", 10, "bold", DANGER if self.hover == dkey else DIM,
                      anchor="center", tags=dt)
            y += 60
        y += 10
        self.section(x0, y, "film", "Graphics settings",
                     "copy video settings between accounts on this PC (VALORANT closed)")
        y += 40
        cx = x0
        for n in self.accounts():
            if n == active or not self.m(n).get("puuid"):
                continue
            key = "vid:" + n
            hov = self.hover == key
            tags = self.hit(key, click=lambda n=n: self.copy_video(n),
                            tip=f"Copy {n}'s graphics settings to {active}" if active else None)
            lab = f"From {n}"
            tw = self.measure(lab, 9, "bold") + 30
            if cx + tw > x1:
                cx = x0
                y += 34
            self.rrect(cx, y, cx + tw, y + 26, 13, fill=self.hcol(key, CARD, CARD_HI, hov), tags=tags)
            self.text(cx + tw / 2, y + 13, lab, 9, "bold", self.hcol(key, MUTED, TEXT, hov), anchor="center",
                      tags=tags)
            cx += tw + 8
        y += 40
        self.finish_scroll(top, y, h)

    # ------------------------------------------------------------ settings
    SET_TABS = [("appearance", "palette", "Appearance"), ("general", "settings", "General"),
                ("game", "game", "In game"), ("offline", "moon", "Offline mode"),
                ("data", "refresh", "Stats & alerts"), ("tools", "lock", "Backup & tools"),
                ("about", "info", "About")]

    def set_set_tab(self, t):
        if t != getattr(self, "set_tab", None):
            keys = [k for k, _, _ in self.SET_TABS]
            cur = getattr(self, "set_tab", "appearance")
            self.tab_switched((keys.index(t) if t in keys else 0)
                              - (keys.index(cur) if cur in keys else 0))
        self.set_tab = t
        self.reset_scroll()
        self.redraw()

    def draw_settings(self, w, h):
        X0 = self.SIDE + 36
        y = 30 - self.scroll()
        top = y
        self.page_header(X0, w - 32, y, "settings", "Settings", f"v{VERSION}")
        y += 66
        tab = getattr(self, "set_tab", "appearance")
        # left category list (stays put while the panel scrolls)
        ny = 96
        keys = [k for k, _, _ in self.SET_TABS]
        if tab in keys:      # the active highlight glides between categories
            ay = self.tween("stab:y", 96 + 46 * keys.index(tab), 0.36, "back")
            self.soft(X0, ay, X0 + 188, ay + 40, 12, ACCENT, alpha=55, spread=10, dy=2)
            self.rrect(X0, ay, X0 + 188, ay + 40, 12, fill=mix(SURFACE, ACCENT, 0.28), depth=1.0)
            self.rrect(X0 + 6, ay + 12, X0 + 9, ay + 28, 1.5, fill=ACCENT_HI, depth=0)
        for k, ic, lab in self.SET_TABS:
            key = "stab:" + k
            on = tab == k
            hov = self.hover == key
            tags = self.hit(key, click=lambda k=k: self.set_set_tab(k),
                            box=(X0, ny, X0 + 188, ny + 40))
            if not on:
                self.hover_bg(X0, ny, X0 + 188, ny + 40, 12, key, base=mix(BG, SURFACE, 0.5),
                              hot=CARD, tags=tags)
            dx = 0 if on else round(2 * self.hv(key), 1)
            self.icon(X0 + 22 + dx, ny + 20, ic, 11,
                      SOFT if on else (self.hcol(key, MUTED, TEXT, hov)), tags=tags)
            self.text(X0 + 42 + dx, ny + 20, lab, 10, "bold",
                      TEXT if on else self.hcol(key, MUTED, TEXT, hov), tags=tags)
            ny += 46
        self.mark_tab_content(90)
        x0 = X0 + 212
        x1 = min(w - 32, x0 + 720)
        bw = x1 - x0
        RH = 62

        def rows_card(y, rows, title=None, sub=None):
            if title:
                self.text(x0 + 4, y + 8, title, 9, "bold", DIM)
                if sub:
                    self.text(x0 + 10 + self.measure(title, 9, "bold"), y + 8, "·  " + sub, 9,
                              fill=DIM, maxw=bw - 120)
                y += 28
            rows = [r for r in rows if r]
            if not rows:
                return y
            hgt = RH * len(rows)
            self.rrect(x0, y, x1, y + hgt, 16, fill=SURFACE, outline=LINE)
            for n, r in enumerate(rows):
                ry = y + n * RH
                if n:
                    self.cv.create_line(x0 + 18, ry, x1 - 18, ry,
                                        fill=mix(LINE, "#ffffff", 0.045))
                kind = r[0]
                if kind == "toggle":
                    _, key, ttl, sub_, enabled = (r + (True,))[:5]
                    k = "set:" + key
                    hov = self.hover == k and enabled
                    tags = self.hit(k, click=(lambda key=key: self.toggle(key)) if enabled
                                    else None)
                    if enabled:
                        self.hover_bg(x0 + 4, ry + 4, x1 - 4, ry + RH - 4, 12, k, tags=tags)
                    self.text(x0 + 20, ry + 22, ttl, 10, "bold", TEXT if enabled else DIM,
                              tags=tags)
                    self.text(x0 + 20, ry + 41, sub_, 8, fill=MUTED, maxw=bw - 110, tags=tags)
                    on = bool(self.settings.get(key, False)) and enabled
                    self.toggle_switch(x1 - 64, ry + 31, on, k, tags, enabled)
                elif kind == "choice":
                    _, ttl, sub_, options, current, pick, key = r
                    self.text(x0 + 20, ry + 22, ttl, 10, "bold")
                    self.text(x0 + 20, ry + 41, sub_, 8, fill=MUTED, maxw=bw * 0.45)
                    tw = sum(self.measure(lab, 9, "bold") + 32 for _, lab in options) + \
                        8 * (len(options) - 1)
                    self.chips(x1 - tw - 18, ry + 17, options, current, pick, key, size=9, h=28)
                elif kind == "link":
                    _, key, ic, ttl, sub_, fn = r
                    k = "row:" + key
                    hov = self.hover == k
                    tags = self.hit(k, click=fn)
                    self.hover_bg(x0 + 4, ry + 4, x1 - 4, ry + RH - 4, 12, k, tags=tags)
                    self.rrect(x0 + 16, ry + 15, x0 + 48, ry + 47, 10,
                               fill=self.hcol(k, CARD_HI, ACCENT, hov), tags=tags)
                    self.icon(x0 + 32, ry + 31, ic, 11, TEXT, tags=tags)
                    self.text(x0 + 62, ry + 22, ttl, 10, "bold", tags=tags)
                    self.text(x0 + 62, ry + 41, sub_, 8, fill=MUTED, maxw=bw - 110, tags=tags)
                    self.text(x1 - 22, ry + 31, "›", 14, "bold", self.hcol(k, DIM, SOFT, hov),
                              anchor="center", tags=tags)
            return y + hgt + 22

        st = self.settings
        if tab == "appearance":
            self.text(x0 + 4, y + 8, "THEME", 9, "bold", DIM)
            y += 28
            self.rrect(x0, y, x1, y + 120, 16, fill=SURFACE, outline=LINE)
            tx = x0 + 24
            n_sw = len([k for k in THEMES if k != "Custom"]) + 1
            sw_step = max(56, min(76, (x1 - x0 - 48) / n_sw))
            for name, pal in [(k, v) for k, v in THEMES.items() if k != "Custom"]:
                key = "theme:" + name
                on = st.get("theme") == name
                hov = self.hover == key
                tags = self.hit(key, click=lambda n=name: self.set_theme(n), tip=name)
                f_ = self.hv(key, hov)
                ring = self.tween("thring:" + name, 1.0 if on else 0.0, 0.3, "back")
                if f_ > 0 or ring > 0.05:
                    self.soft(tx, y + 28, tx + 44, y + 72, 22, pal[0],
                              alpha=int(60 * max(f_, ring)), spread=10, dy=2)
                if ring > 0.05:
                    self.circle(tx + 22, y + 50, 23 + 4 * ring, fill="",
                                outline=mix(BG, TEXT, ring), width=2)
                self.circle(tx + 22, y + 50, 22 + 1.5 * f_ - self.pressed(key), fill=pal[4],
                            tags=tags, depth=0.8)
                self.circle(tx + 22, y + 50, 13 + 1.5 * f_, fill=pal[0], tags=tags, depth=1.0)
                self.text(tx + 22, y + 94, name, 8, "bold", TEXT if on else DIM, anchor="center")
                tx += sw_step
            key = "theme:pick"
            hov = self.hover == key
            tags = self.hit(key, click=self.open_color_picker, tip="Pick any colour")
            cc = st.get("custom_color")
            on = st.get("theme") == "Custom"
            if on:
                self.circle(tx + 22, y + 50, 27, fill="", outline=TEXT, width=2)
            self.circle(tx + 22, y + 50, (22 + (23 - 22) * self.hv(key, hov)),
                        fill=custom_palette(cc)[4] if cc else CARD_HI, tags=tags)
            if cc:
                self.circle(tx + 22, y + 50, 13, fill=cc, tags=tags)
            else:
                self.icon(tx + 22, y + 50, "add", 11, TEXT, tags=tags)
            self.text(tx + 22, y + 94, "Custom", 8, "bold", TEXT if on else DIM, anchor="center")
            y += 142
            y = rows_card(y, [
                ("choice", "Account layout", "Big tiles or a compact list",
                 [("grid", "Tiles"), ("list", "List")], st.get("layout"),
                 lambda v: self.set_setting("layout", v), "lay"),
                ("toggle", "animations", "Animations", "Smooth page and pop-up transitions"),
                ("toggle", "ui_sounds", "Interface sounds",
                 "Very quiet clicks and chimes for switching, toggles and alerts"),
                ("toggle", "rank_glow", "Rank-coloured glow",
                 "The background glow takes on the selected account's rank colour"),
                ("link", "bgimg", "palette", "Remove background image" if st.get("bg_image")
                 else "Custom background image",
                 Path(st["bg_image"]).name if st.get("bg_image")
                 else "Any picture behind the app, dimmed so text stays readable", self.pick_bg),
            ], "LOOK & FEEL")
            y = rows_card(y, [("toggle", "streamer", "Streamer mode",
                               "Hides Riot IDs, notes and wallet balances everywhere")],
                          "PRIVACY")
        elif tab == "general":
            tray_sub = ("Closing the window keeps RiotHub in the system tray"
                        if HAS_TRAY else "Needs extras: py -m pip install pillow pystray")
            y = rows_card(y, [
                ("toggle", "close_to_tray", "Keep running in the tray", tray_sub, HAS_TRAY),
                ("toggle", "start_with_windows", "Start with Windows",
                 "Starts quietly in the tray when you sign into Windows"),
                ("toggle", "close_after_launch", "Close after the game opens",
                 "Quits once the game is running"),
            ], "APP")
            y = rows_card(y, [
                ("toggle", "warm_client", "Keep the Riot Client ready",
                 "Starts it minimised in the background when the app opens, so Play is instant"),
                ("toggle", "tuck_client", "Hide the Riot Client while you play",
                 "Minimises its window as soon as you're signed in"),
                ("choice", "Open on", "The page you see when the app starts",
                 [("play", "Play"), ("home", "Accounts")], st.get("start_page", "play"),
                 lambda v: self.set_setting("start_page", v), "spg"),
            ], "LAUNCHER")
            y = rows_card(y, [
                ("toggle", "open_client", "Open the Riot Client after switching",
                 "Off: switching just swaps the login, and whatever you open next is signed "
                 "in (offline mode needs this on)"),
            ], "SWITCHING")
            y = rows_card(y, [
                ("toggle", "hotkeys", "Hotkeys",
                 "Ctrl+Alt+1–9 logs into accounts in tile order, Ctrl+Alt+0 switches back"),
                ("link", "mini", "grid", ("Hide" if self.mini else "Show") + " mini overlay",
                 "Small always-on-top account switcher", self.toggle_mini),
                ("link", "sc_all", "link", "Desktop shortcuts for every account",
                 "One 'Log in as …' shortcut each, pin them to your taskbar", self.shortcut_all),
            ], "SHORTCUTS")
        elif tab == "game":
            y = rows_card(y, [
                ("toggle", "agent_picker", "Mini agent picker",
                 "A tiny window with your favourite agents pops up in agent select"),
                ("toggle", "agent_grid", "Agent select from the app",
                 "Pick and lock from the Live page too (manual, at your own risk)"),
                ("toggle", "auto_live", "Open Live view when a match is found",
                 "Brings the whole app up instead (when the mini picker is off)"),
                ("toggle", "live_alerts", "Match alerts",
                 "Notification when agent select starts"),
                ("toggle", "match_sound", "Match found sound",
                 "Plays a chime and flashes the taskbar, so you don't miss it while tabbed out"),
                ("toggle", "focus_mode", "Focus mode",
                 "Hides other players' ranks so you just play"),
            ], "VALORANT")
            y = rows_card(y, [
                ("toggle", "lol_auto_accept", "Auto-accept matches",
                 "Accepts the ready check while the League client is open"),
                ("toggle", "lol_random_skin", "Random skin on lock-in",
                 "Picks a random owned skin after you lock a champion"),
            ], "LEAGUE OF LEGENDS")
        elif tab == "offline":
            rows = [("choice", "Engine", "Built-in, or Deceive.exe if you use it",
                     [("builtin", "Built-in"), ("deceive", "Deceive.exe")],
                     st.get("status_engine"), lambda v: self.set_setting("status_engine", v),
                     "eng")]
            if st.get("status_engine") == "deceive":
                rows.append(("link", "deceive", "folder", "Deceive.exe location",
                             st.get("deceive_path") or "Not set", self.pick_deceive))
            rows += [("toggle", "chat_control", "Control from chat",
                      "A 'RiotHub' friend you can message online / offline / mobile"),
                     ("toggle", "auto_offline", "Scheduled offline",
                      f"Appear offline from {st.get('offline_from', 0):02d}:00 to "
                      f"{st.get('offline_to', 8):02d}:00")]
            if st.get("auto_offline"):
                rows += [("choice", "Offline from", "Start of the quiet hours",
                          [(20, "20:00"), (22, "22:00"), (0, "00:00"), (2, "02:00")],
                          st.get("offline_from"), lambda v: self.set_setting("offline_from", v),
                          "off_a"),
                         ("choice", "Until", "End of the quiet hours",
                          [(6, "06:00"), (8, "08:00"), (10, "10:00"), (12, "12:00")],
                          st.get("offline_to"), lambda v: self.set_setting("offline_to", v),
                          "off_b")]
            y = rows_card(y, rows, "OFFLINE MODE", "switch it on/off with the moon button")
            self.text(x0 + 6, y - 8, "Connection: " + {
                "idle": "not running", "running": "waiting for the Riot Client…",
                "connected": "chat connected, changes apply live",
                "error": "error, see the status bar"}.get(self.proxy_state, ""), 8, fill=DIM)
            y += 14
        elif tab == "data":
            key = st.get("henrik_key")
            y = rows_card(y, [
                ("link", "henrik", "link", "HenrikDev API key" + ("  ✓" if key else ""),
                 ("Keeps every account's rank fresh and powers the leaderboard"
                  if key else "Free key: keeps every account's rank fresh without logging in, "
                  "and powers the leaderboard"), self.set_henrik_key),
                ("link", "henrik_get", "link", "Get a free key",
                 "Opens the HenrikDev dashboard (sign in with Discord)",
                 lambda: webbrowser.open(HENRIK_KEY_URL)),
            ], "STATS SOURCE")
            y = rows_card(y, [
                ("toggle", "bg_refresh", "Background refresh",
                 "Keeps rank, store and matches fresh while you're logged in"),
                ("choice", "Refresh every", "How often background refresh runs",
                 [(5, "5m"), (10, "10m"), (20, "20m"), (30, "30m")], st.get("bg_minutes"),
                 lambda v: self.set_setting("bg_minutes", v), "bgm"),
                ("choice", "Matches to load", "More take longer the first time",
                 [(5, "5"), (10, "10"), (20, "20")], st.get("match_count"),
                 lambda v: self.set_setting("match_count", v), "mc"),
            ], "REFRESH")
            y = rows_card(y, [("toggle", "wishlist_alerts", "Wishlist alerts",
                               "Notification the moment a wishlisted skin is in any of your shops")],
                          "ALERTS")
        elif tab == "tools":
            ab = st.get("auto_backup")
            y = rows_card(y, [
                ("link", "pin", "lock", "Remove app PIN" if st.get("pin") else
                 "Lock the app with a PIN", "Asked every time RiotHub opens", self.set_pin),
                ("link", "autob", "history", "Turn off weekly backups" if ab else
                 "Automatic weekly backups",
                 (f"To {ab['folder']}  ·  last {ago(ab.get('last'), '').strip() or 'never'}"
                  if ab else "Encrypted backup to a folder you pick, keeps 4"),
                 self.auto_backup_setup),
                ("link", "export", "upload", "Export backup",
                 "Accounts, tags, notes and settings in one password-protected file",
                 self.export_backup),
                ("link", "import", "download", "Import backup",
                 "Restore a backup on this or another PC", self.import_backup),
                ("link", "tcno", "download", "Import from TcNo",
                 "Bring over Riot accounts saved in TcNo Account Switcher", self.import_tcno),
            ], "BACKUP")
            y = rows_card(y, [
                ("link", "obs", "film", ("Stop" if st.get("obs_overlay") else "Start")
                 + " OBS rank overlay", "Browser source at http://127.0.0.1:47822",
                 self.toggle_obs),
                ("link", "health", "check", "Run health check",
                 "Tests every part of the app on this PC", self.health_check),
                ("link", "diag", "info", "Export diagnostics",
                 "Settings and error log for troubleshooting (no logins)",
                 self.export_diagnostics),
                ("link", "assets", "refresh", "Re-download game data",
                 "Skins, ranks, maps and agents from valorant-api.com", self.reload_assets),
                ("link", "folder", "folder", "Open data folder",
                 "Saved logins, stats and settings live here", self.open_folder),
            ], "TOOLS")
            trash = self.trash_items()
            if trash:
                y = rows_card(y, [("link", "trash:" + tp.name, "history",
                                   f"Restore {tp.name.split('__')[0]}",
                                   f"Deleted {ago(tp.stat().st_mtime, '').strip()}",
                                   (lambda tp=tp: self.restore_trash(tp))) for tp in trash],
                              "RECENTLY DELETED")
        else:
            self.rrect(x0, y, x1, y + 120, 16, fill=SURFACE, outline=LINE)
            logo = self.logo_photo(64)
            if logo:
                self.cv.create_image(x0 + 56, y + 60, image=logo)
            self.text(x0 + 104, y + 44, APP_TITLE, 15, "bold")
            self.text(x0 + 104, y + 70, f"Version {VERSION}", 9, fill=MUTED)
            if self.update_repo():
                self.action_button(x1 - 20, y + 60, "Check for updates",
                                   lambda: self.check_updates(loud=True), "about:upd", "refresh",
                                   anchor="e", primary=False, h=32)
            y += 142
            notes = [("Images", "on" if HAS_PIL else "off (py -m pip install pillow)"),
                     ("Tray icon", "on" if self.tray else "off"),
                     ("Video previews", "on" if VideoPlayer.backend() else
                      "off (py -m pip install av)"),
                     ("Game data", "ready" if ASSETS.ready else (ASSETS.error or "loading…"))]
            if self.hotkeys and self.hotkeys.failed:
                notes.append(("Hotkeys in use elsewhere",
                              ", ".join(f"Ctrl+Alt+{i}" for i in self.hotkeys.failed)))
            self.rrect(x0, y, x1, y + 26 * len(notes) + 20, 16, fill=SURFACE, outline=LINE)
            for n, (k, v) in enumerate(notes):
                self.text(x0 + 20, y + 22 + n * 26, k, 9, "bold", MUTED)
                self.text(x1 - 20, y + 22 + n * 26, v, 9, fill=TEXT, anchor="e")
            y += 26 * len(notes) + 40
            self.text(x0 + 4, y, "Keyboard", 9, "bold", DIM)
            y += 22
            for k, v in (("Ctrl+1–8", "jump to a page"),
                         ("Ctrl+F", "filter accounts"), ("Ctrl+Alt+1–9", "log into an account"),
                         ("Ctrl+Alt+0", "switch back")):
                self.pill(x0, y, k, fill=CARD, fg=TEXT, size=8)
                self.text(x0 + 110, y, v, 9, fill=MUTED)
                y += 26
        self.finish_scroll(top, max(y, ny + 20), h)

    # ------------------------------------------------------------ events
    def current_key(self):
        """What's under the mouse. Worked out from geometry: Tk's own 'current' item is
        empty for a moment after every redraw, and relying on it silently dropped clicks."""
        x, y = getattr(self, "mouse", (None, None))
        if x is None:
            return None
        ok = (lambda k: self.key_ok(k)) if self.layers else (lambda k: True)
        for (x0, y0, x1, y1), key in reversed(self.hit_boxes):
            if x0 <= x <= x1 and y0 <= y <= y1 and key in self.hits and ok(key):
                return key
        try:
            under = self.cv.find_overlapping(x, y, x, y)
        except tk.TclError:
            return None
        for item in reversed(under):           # topmost first
            for t in self.cv.gettags(item):
                if t.startswith("hit:") and t[4:] in self.hits and ok(t[4:]):
                    return t[4:]
        return None

    def on_motion(self, e):
        px, py = self.mouse if self.mouse and self.mouse[0] is not None else (e.x, e.y)
        self.mouse = (e.x, e.y)
        if self.kbd_focus and abs(e.x - px) + abs(e.y - py) > 3:
            self.kbd_focus = False      # mouse is back: hide the keyboard focus ring
            self.redraw()
        self.set_hover(self.current_key())

    def set_hover(self, key):
        if key != self.hover:
            self.hover = key
            self.hover_t = time.time()
            if key and (self.hits.get(key) or {}).get("tip"):
                self.after(480, lambda k=key: self.hover == k and self.draw_overlays())
            hk = self.hits.get(key, {}) if key else {}
            self.cv.config(cursor="hand2" if hk.get("click") or hk.get("down") else "")
            self.layer_redraw() if self.layers else self.redraw()

    def fire(self, kind, event=None):
        if event is not None and hasattr(event, "x"):
            self.mouse = (event.x, event.y)
        key = self.current_key()
        h = self.hits.get(key) if key else None
        fn = h and h.get(kind)
        if fn:
            fn(event) if kind == "right" else fn()

    # Clicks fire on release (like every native control) so buttons can show a pressed
    # state and a press can be cancelled by dragging off. Menus still fire on press.
    def on_press(self, e):
        self.cv.focus_set()
        self.mouse = (e.x, e.y)
        key = self.current_key()
        if self.pop:
            if key and key.startswith("pop:"):
                self.fire("click")
            else:
                self.close_pop()
            return
        if self.layers and not key:
            top = self.top_layer()
            if top and top.dismiss:
                x0, y0, x1, y1 = top.box
                if not (x0 <= e.x <= x1 and y0 <= e.y <= y1):
                    top.close()
            return
        self.press = (key, e.x, e.y)
        self.dragging = None
        self.press_t = time.time()
        hk = (self.hits.get(key) or {}) if key else {}
        if hk.get("down"):
            try:
                hk["down"](e.x, e.y)
            except Exception as ex:
                self.log(f"down: {ex!r}")
        if hk.get("click") or hk.get("down"):
            self.layer_redraw() if self.layers else self.redraw()

    def on_drag(self, e):
        if not self.press:
            return
        key, px, py = self.press
        hk = (self.hits.get(key) or {}) if key else {}
        if hk.get("drag"):
            try:
                hk["drag"](e.x, e.y)
            except Exception as ex:
                self.log(f"drag: {ex!r}")
            self.layer_redraw() if self.layers else self.redraw()
            return
        if self.layers:
            return
        if self.dragging:
            self.drag_pos = (e.x, e.y)
            self.redraw()
        elif (key and key.startswith("tile:") and key != "tile:__add__"
              and self.page == "home" and not self.search_var.get()
              and abs(e.x - px) + abs(e.y - py) > 10):
            self.dragging = key[5:]
            self.drag_pos = (e.x, e.y)
            self.cv.config(cursor="fleur")
            self.redraw()

    def drop_index(self):
        if not self.tile_slots:
            return -1
        x, y = self.drag_pos
        T = self.TILE if self.settings.get("layout") != "list" else 0
        best, bd = 0, None
        for i, (_, sx, sy) in enumerate(self.tile_slots):
            cx = sx + (T / 2 if T else 150)
            cy = sy + (T / 2 if T else 30)
            d = (cx - x) ** 2 + (cy - y) ** 2
            if bd is None or d < bd:
                best, bd = i, d
        return best

    def on_release(self, e):
        pk = self.press[0] if self.press else None
        if pk and not self.dragging:
            self.mouse = (e.x, e.y)
            if self.current_key() == pk:
                self.press = None
                self.fire("click")
                self.layer_redraw() if self.layers else self.redraw()
                return
        if self.dragging:
            name = self.dragging
            idx = self.drop_index()
            order = self.accounts()
            if name in order and idx >= 0:
                order.remove(name)
                order.insert(idx, name)
                self.state_["order"] = order
                self.persist()
            self.dragging = None
            self.cv.config(cursor="")
            self.redraw()
        self.press = None
        self.layer_redraw() if self.layers else self.redraw()

    def on_wheel(self, e):
        try:
            if e.widget.winfo_toplevel() is not self:
                return
        except Exception:
            return
        if self.sheets:
            fn = getattr(self.sheets[-1], "on_wheel", None)
            if fn:
                fn(e)
            return
        if self.layers:
            top = self.top_layer()
            if self.pop:
                self.close_pop()
            elif top:
                top.on_wheel(e.delta)
            return
        if self.pop:
            self.close_pop()
            return
        base = self.scroll_t.get(self.page, self.scroll())
        self.scroll_t[self.page] = max(0, min(self.max_scroll, base - (e.delta / 120) * 96))
        self._wheel_t = time.time()
        self._scroll_last = time.time() - 0.016
        self.redraw()

    def play_menu_items(self, n):
        active = self.state_.get("active") == n
        dflt = self.m(n).get("default_game") or self.state_["game"]
        items = []
        for g in installed_games():
            prod = GAMES[g]
            if prod is None:
                continue
            items.append({"label": ("Play " if active else "Log in & play ") + g, "icon": "play",
                          "hint": "default" if g == dflt else "",
                          "fn": lambda g=g: self.switch(n, game=g)})
        items += [None, {"label": "Log in only (no game)", "icon": "person",
                         "fn": lambda: self.switch(n, game="Client only", quiet=False),
                         "disabled": active},
                  {"label": "Switch without opening anything", "icon": "moon",
                   "hint": "opens signed in later",
                   "fn": lambda: self.switch(n, quiet=True), "disabled": active},
                  {"label": "Desktop shortcut for a game…", "icon": "link",
                   "fn": lambda: self.reopen_pop(self.shortcut_menu_items(n))}]
        return items

    def shortcut_menu_items(self, n):
        return [{"label": f"Shortcut: {g}" if GAMES[g] else "Shortcut: log in only",
                 "icon": "link", "fn": lambda g=g: self.shortcut(n, g)}
                for g in installed_games()]

    def reopen_pop(self, items):
        x, y, anchor = getattr(self, "_pop_xy", (200, 200, "nw"))
        self.popmenu(items, x, y, anchor)

    def account_menu_items(self, n):
        m = self.m(n)
        rid = f"{m.get('game_name')}#{m.get('tag')}" if m.get("game_name") else None
        active = self.state_.get("active") == n
        return [
            {"label": "Log in" if not active else "Logged in", "icon": "play",
             "fn": lambda: self.switch(n), "disabled": active},
            {"label": "Play…", "icon": "game", "hint": "pick a game",
             "fn": lambda: self.reopen_pop(self.play_menu_items(n))},
            {"label": "Profile", "icon": "person", "fn": lambda: self.open_profile(n)},
            {"label": "Store", "icon": "shop",
             "fn": lambda: (self.select(n), self.set_page("store"))},
            None,
            {"label": "Edit name, tags & note", "icon": "edit", "fn": lambda: self.edit(n)},
            {"label": "Refresh stats", "icon": "refresh", "fn": lambda: self.refresh_stats(n)},
            {"label": "Update with current login", "icon": "save",
             "fn": lambda: self.update_login(n)},
            {"label": "Move to top", "icon": "chevron", "fn": lambda: self.move_top(n)},
            {"label": "Create desktop shortcut", "icon": "link", "fn": lambda: self.shortcut(n)},
            None,
            {"label": "Copy Riot ID", "icon": "copy", "hint": rid or "",
             "fn": (lambda: self.copy_text(rid, "Riot ID")) if rid else
             (lambda: self.toast("Riot ID unknown."))},
            {"label": "Open on tracker.gg", "icon": "link", "fn": lambda: self.open_tracker(m)},
            None,
            {"label": "Delete", "icon": "delete", "danger": True, "fn": lambda: self.delete(n)},
        ]

    def popup(self, e, name):
        self._menu_target = name
        x, y = (e.x, e.y) if e is not None and hasattr(e, "x") else (
            self.winfo_pointerx() - self.winfo_rootx(), self.winfo_pointery() - self.winfo_rooty())
        self.popmenu(self.account_menu_items(name), x + 2, y + 2)

    def select(self, name):
        if name != self.selected:
            self.duos = None
        self.selected = name
        self.expanded = None
        self.redraw()

    def page_index(self, p):
        order = [x for x, _, _ in self.PAGES] + ["settings"]
        return order.index(p) if p in order else len(order)

    def set_page(self, p):
        if self.layers:
            self.close_layers()
        if p != self.page:
            self.search_var.set("")
            self.page_t = time.time()
            self.page_dir = 1 if self.page_index(p) >= self.page_index(self.page) else -1
            self.reset_anims("cnt:", "bar:")
            self._tab_mark = None
            self.play_ui("tap")
        self.page = p
        self.cv.focus_set()
        self.redraw()

    def open_profile(self, name):
        if name:
            self.selected = name
        self.set_page("profile")

    PTABS = ["overview", "matches", "inventory", "loadout", "collections", "league"]

    def set_ptab(self, t):
        if t != self.ptab:
            a = self.PTABS.index(self.ptab) if self.ptab in self.PTABS else 0
            b = self.PTABS.index(t) if t in self.PTABS else 0
            self.tab_switched(b - a)
        self.ptab = t
        self.search_var.set("")
        self.redraw()

    def set_inv_tab(self, t):
        if t != self.inv_tab:
            self.tab_switched()
        self.inv_tab = t
        self.weapon = "All"
        self.redraw()

    RANKED_CHIP = "__ranked__"

    def set_tag_filter(self, t):
        self.tag_filter = t
        self.redraw()

    def flip_archived(self):
        self.show_archived = not self.show_archived
        self.redraw()

    def flip_card(self, k):
        self.flips[k] = time.time()
        rv = self.state_.setdefault("revealed", [])
        rv.append(k)
        del rv[:-120]
        save_state(self.state_)
        self.redraw()

    def toggle_history(self, n):
        self.show_history ^= {n}
        self.redraw()

    def set_inv_sort(self, k):
        self.inv_sort = k
        self.redraw()

    def set_weapon(self, wpn):
        self.weapon = wpn
        self.redraw()

    def toggle_expand(self, cid):
        self.expanded = None if self.expanded == cid else cid
        self.redraw()

    def game_menu(self, x, y):
        cur = self.state_["game"]
        items = [{"label": g if GAMES[g] else "Client only (no game)", "icon": "game",
                  "check": g == cur, "fn": lambda g=g: self.set_game(g)}
                 for g in installed_games()]
        self.popmenu(items, x, y, "n")

    def set_game(self, g):
        self.state_["game"] = g
        self.persist()
        self.redraw()

    def set_compare_sort(self, k):
        cur, desc = self.compare_sort
        self.compare_sort = (k, not desc if cur == k else k != "account")
        self.redraw()

    def set_sync_source(self, n):
        self.sync_source = n
        self.redraw()

    def toggle_sync_cat(self, k):
        if k == "everything":
            self.sync_cats = {"everything"} if "everything" not in self.sync_cats else set()
        else:
            self.sync_cats.discard("everything")
            self.sync_cats ^= {k}
        self.redraw()

    def set_setting(self, key, val):
        self.settings[key] = val
        save_state(self.state_)
        self.redraw()

    def open_color_picker(self):
        start = self.settings.get("custom_color") or ACCENT
        res = ColorPicker(self, start).result
        if res:
            self.settings["custom_color"] = res
            THEMES["Custom"] = custom_palette(res)
            self.set_theme("Custom")

    def set_theme(self, name):
        self.settings["theme"] = name
        save_state(self.state_)
        apply_theme(name)
        self.glow_cur = GLOW
        if self.images:
            self.images.photos.clear()
        self._shapes.clear()
        self.make_icons()
        self.redraw()

    def toggle(self, key):
        val = not self.settings.get(key)
        if key == "start_with_windows":
            try:
                set_autostart(val)
            except Exception as e:
                self.notify("Couldn't change startup", str(e))
                return
        self.settings[key] = val
        save_state(self.state_)
        self.play_ui("toggle")
        if key == "hotkeys":
            self.apply_hotkeys()
            if self.tray:
                self.tray.update_menu()
        if key == "chat_control":
            self.proxy.control = val
        if key == "status_enabled":
            self.toast("Status control is on. It kicks in the next time you log in."
                       if val else "Status control is off from your next login.")
        self.redraw()

    def pick_deceive(self):
        if not filedialog:
            return
        p = filedialog.askopenfilename(title="Find Deceive.exe",
                                       filetypes=[("Deceive", "Deceive*.exe"), ("Programs", "*.exe")])
        if p:
            self.set_setting("deceive_path", p)

    def set_status_mode(self, mode):
        self.settings["status_mode"] = mode
        save_state(self.state_)
        self.proxy.mode = mode
        if self.settings.get("status_engine") == "deceive":
            self.toast(f"Deceive will use {STATUS_MODES[mode]} from the next launch. Use "
                       "Deceive's tray icon to change it live.")
        elif self.proxy.connected:
            self.proxy.set_mode(mode)
            self.toast(f"You now appear {STATUS_MODES[mode].lower()}.", "good")
        elif self.settings.get("status_enabled"):
            self.toast(f"You'll appear {STATUS_MODES[mode].lower()} from your next login.")
        if self.tray:
            try:
                self.tray.update_menu()
            except Exception:
                pass
        self.redraw()

    def on_proxy(self, kind, info):
        if kind == "connected":
            self.proxy_state = "connected"
            if self.settings.get("status_mode") != "online":
                self.toast(f"Chat hooked. You appear "
                           f"{STATUS_MODES[self.settings['status_mode']].lower()}.", "good")
        elif kind == "disconnected":
            self.proxy_state = "running" if self.proxy.started else "idle"
        elif kind == "mode":
            self.settings["status_mode"] = info
            save_state(self.state_)
            self.toast(f"Chat command: you now appear {STATUS_MODES[info].lower()}.", "good")
        elif kind == "error":
            self.proxy_state = "error"
            self.status, self.status_until = f"Status control: {info}", time.time() + 15
        self.redraw()

    # ------------------------------------------------------------ dialogs
    def ask(self, title, msg, initial=""):
        return Modal(self, title, msg, entry=initial, ok="Save").result

    def confirm(self, title, msg, ok="Continue", danger=False):
        return bool(Modal(self, title, msg, ok=ok, danger=danger).result)

    def notify(self, title, msg):
        Modal(self, title, msg, cancel=None)

    # ------------------------------------------------------------ tray / window / ipc
    def start_tray(self):
        if not HAS_TRAY:
            return

        def items():
            yield pystray.MenuItem("Open RiotHub", lambda i, it: self.call_ui(self.show_window),
                                   default=True)
            yield pystray.Menu.SEPARATOR
            for idx, n in enumerate(self.accounts()):
                label = n + (f"    Ctrl+Alt+{idx + 1}" if self.settings.get("hotkeys")
                             and idx < 9 else "")
                yield pystray.MenuItem(
                    label,
                    (lambda name: lambda i, it: self.call_ui(lambda: self.switch(name)))(n),
                    checked=(lambda name: lambda it: self.state_.get("active") == name)(n))
            prev = self.state_.get("previous")
            if prev and prev in self.accounts() and prev != self.state_.get("active"):
                yield pystray.MenuItem(f"Switch back to {prev}",
                                       lambda i, it: self.call_ui(self.switch_back))
            d = self.live or {}
            if d.get("party_id") and d.get("phase") == "none":
                yield pystray.Menu.SEPARATOR
                if self.queueing():
                    yield pystray.MenuItem("Stop queue", lambda i, it: self.call_ui(
                        lambda: self.party_do("leave")))
                else:
                    q = d.get("queue") or ""
                    yield pystray.MenuItem(f"Start queue ({QUEUES.get(q, q.title() or 'Custom')})",
                                           lambda i, it: self.call_ui(lambda: self.party_do("join")))
                yield pystray.MenuItem("Party open", lambda i, it: self.call_ui(
                    lambda: self.party_do("access", not (self.live or {}).get("party_open"))),
                    checked=lambda it: bool((self.live or {}).get("party_open")))
            yield pystray.Menu.SEPARATOR
            yield pystray.MenuItem("Offline mode", lambda i, it: self.call_ui(
                self.toggle_offline_mode), checked=lambda it: self.offline_on())
            if self.settings.get("status_enabled"):
                yield pystray.MenuItem("Status", pystray.Menu(*[
                    pystray.MenuItem(
                        label, (lambda k: lambda i, it: self.call_ui(
                            lambda: self.set_status_mode(k)))(k),
                        checked=(lambda k: lambda it: self.settings.get("status_mode") == k)(k),
                        radio=True)
                    for k, label in STATUS_MODES.items()]))
            yield pystray.MenuItem("Mini overlay", lambda i, it: self.call_ui(self.toggle_mini),
                                   checked=lambda it: bool(self.mini))
            yield pystray.MenuItem("Quit", lambda i, it: self.call_ui(self.quit_app))

        try:
            self.tray = pystray.Icon(APP_NAME, make_app_icon(64, tray=True), APP_TITLE,
                                     menu=pystray.Menu(items))
            self.tray.run_detached()
        except Exception as e:
            print("Tray failed:", e)
            self.tray = None

    def show_window(self):
        if self.locked and not self.unlock():
            return
        self.deiconify()
        self.lift()
        self.attributes("-topmost", True)
        self.after(200, lambda: self.attributes("-topmost", False))
        self.focus_force()
        self.redraw()

    def on_close(self):
        try:
            if self.state() == "normal":
                self.state_["geometry"] = self.geometry()
                save_state(self.state_)
        except Exception:
            pass
        if self.tray and self.settings.get("close_to_tray"):
            self.withdraw()
            if not self.state_.get("tray_hint_shown"):
                self.state_["tray_hint_shown"] = True
                save_state(self.state_)
                try:
                    self.tray.notify("Still running in the tray. Right-click the icon to "
                                     "switch or quit.", APP_TITLE)
                except Exception:
                    pass
        else:
            self.quit_app()

    def quit_app(self):
        self._quitting = True
        save_state(self.state_)
        if self.hotkeys:
            self.hotkeys.stop()
        if self.tray:
            try:
                self.tray.stop()
            except Exception:
                pass
        self.destroy()

    def apply_hotkeys(self):
        if os.name != "nt":
            return
        if self.hotkeys:
            self.hotkeys.stop()
            self.hotkeys = None
        if self.settings.get("hotkeys"):
            self.hotkeys = Hotkeys(lambda i: self.call_ui(lambda: self.hotkey(i)))
            self.hotkeys.start()

    def hotkey(self, i):
        if i == 10:          # Ctrl+Alt+P: play your default game on the current account
            a = self.state_.get("active") or self.play_account()
            g = self.m(a).get("default_game") or self.state_["game"]
            self.play_game(g if GAMES.get(g) else "VALORANT")
            return
        if i == 9:
            self.switch_back()
            return
        acc = self.accounts()
        if i < len(acc):
            self.switch(acc[i])

    def nav(self, d):
        if self.page != "home" or isinstance(self.focus_get(), tk.Entry):
            return
        names = [n for n, _, _ in self.tile_slots] or self.accounts()
        if not names:
            return
        if self.settings.get("layout") == "list":
            d = max(-1, min(1, d))
        elif abs(d) == 4:
            w = self.cv.winfo_width() - self.SIDE - 36 - (self.RIGHT + 44
                                                         if self.cv.winfo_width() >= 1060 else 32)
            d = (d // 4) * max(1, int((w - self.TILE_PAD + 30) // (self.TILE + 30)))
        i = names.index(self.selected) if self.selected in names else -1
        self.kbd_focus = True
        self.select(names[max(0, min(len(names) - 1, i + d))])

    def nav_enter(self):
        if self.page == "home" and self.selected and not isinstance(self.focus_get(), tk.Entry):
            self.switch(self.selected)

    def tour(self):
        steps = [
            (f"Welcome to {APP_TITLE}",
             "Log into the Riot Client with 'Stay signed in' ticked, then press Save (bottom "
             "bar) or + Add account. After that, switching is one click."),
            ("Everything else loads by itself",
             "Each time you log in, rank, store, matches and inventory refresh. Star skins to get "
             "alerts when they hit your store."),
            ("Shortcuts",
             "Ctrl+1–8 jump between pages. Ctrl+Alt+1–9 "
             "switch accounts from anywhere, Ctrl+Alt+0 switches back."),
        ]
        for i, (t, msg) in enumerate(steps):
            last = i == len(steps) - 1
            if not Modal(self, t, msg, ok="Let's go" if last else "Next",
                         cancel=None if last else "Skip").result:
                break
        self.set_setting("toured", True)

    def switch_back(self):
        prev = self.state_.get("previous")
        if prev and prev in self.accounts() and prev != self.state_.get("active"):
            self.switch(prev)
        else:
            self.toast("No previous account to switch back to.")

    def start_ipc(self):
        try:
            srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            srv.bind(("127.0.0.1", IPC_PORT))
            srv.listen(4)
        except OSError:
            return

        def loop():
            while True:
                try:
                    conn, _ = srv.accept()
                    with conn:
                        conn.settimeout(2)
                        data = conn.recv(65536)
                    msg = json.loads(data.decode() or "{}")
                    self.call_ui(lambda msg=msg: self.handle_ipc(msg))
                except Exception:
                    continue
        threading.Thread(target=loop, daemon=True).start()

    def handle_ipc(self, msg):
        if msg.get("cmd") == "login" and msg.get("name"):
            self.switch(msg["name"], game=msg.get("game"))
        else:
            self.show_window()

    # ------------------------------------------------------------ playtime / background
    def playtime(self, name):
        pt = self.state_["playtime"].get(name) or {}
        days = pt.get("days") or {}
        return {"total": pt.get("total", 0), "today": days.get(today_key(), 0),
                "week": sum(days.get(today_key(i), 0) for i in range(7))}

    def _league_loop(self):
        done = set()
        while True:
            time.sleep(1.5)
            st = self.settings
            if not (st.get("lol_auto_accept") or st.get("lol_random_skin")):
                continue
            try:
                lf = league_lockfile()
                if not lf:
                    done.clear()
                    time.sleep(5)
                    continue
                if st.get("lol_auto_accept") and lol_ready_check(lf):
                    self.set_status("Match accepted.", "good")
                if st.get("lol_random_skin"):
                    picked = lol_random_skin(lf, done)
                    if picked:
                        self.set_status(f"Random skin: {picked}", "good")
            except Exception as e:
                self.call_ui(lambda e=e: self.log(f"league loop: {e}"))

    def _playtime_loop(self):
        step = 30
        was = False
        while True:
            time.sleep(step)
            try:
                running = "VALORANT" in games_running()
                if running or games_running():
                    self.call_ui(lambda: self._add_playtime(step))
                if running and not was:
                    self.call_ui(self.session_begin)
                elif was and not running:
                    self.call_ui(self.session_end)
                was = running
            except Exception:
                pass

    def _add_playtime(self, secs):
        a = self.state_.get("active")
        if not a:
            return
        pt = self.state_["playtime"].setdefault(a, {"total": 0, "days": {}})
        pt["total"] = pt.get("total", 0) + secs
        days = pt.setdefault("days", {})
        k = today_key()
        days[k] = days.get(k, 0) + secs
        for old in sorted(days)[:-30]:
            days.pop(old, None)
        self._pt_dirty = getattr(self, "_pt_dirty", 0) + 1
        if self._pt_dirty >= 4:
            self._pt_dirty = 0
            save_state(self.state_)

    def _bg_tick(self):
        self.after(60_000, self._bg_tick)
        try:
            self.auto_offline_check()
            self.run_auto_backup()
            self.check_patch()
            self._obs_snapshot = self.obs_data()
            a0 = self.state_.get("active")
            st0 = self.m(a0).get("store") or {}
            if self.tray and st0.get("daily_expires", 0) > time.time():
                self.tray.title = (f"{APP_TITLE} · {a0}'s store resets in "
                                   f"{dur(st0['daily_expires'] - time.time())}")
            if a0 and not self.league_busy and league_lockfile() and time.time() - (
                    self.m(a0).get("league") or {}).get("updated", 0) > 900:
                self.refresh_league(quiet=True)
        except Exception as e:
            self.log(f"bg tick: {e}")
        a = self.state_.get("active")
        if not (a and self.settings.get("bg_refresh")) or self.busy or a in self.fetching:
            return
        m = self.m(a)
        mins = int(self.settings.get("bg_minutes") or 10)
        due = time.time() - (m.get("updated") or 0) > mins * 60
        st = m.get("store") or {}
        if st and 0 < st.get("daily_expires", 0) < time.time():
            due = True
        if due and read_lockfile():
            self.refresh_stats(a, quiet=True)

    # ------------------------------------------------------------ worker helpers
    def run(self, fn, *args, guard=True):
        if self.busy:
            # don't silently ignore a click: do it as soon as the current job finishes
            if getattr(fn, "__self__", None) is self and fn.__name__ in (
                    "_open_login", "_save", "_switch", "do_switch"):
                self._queued = (fn, args, guard)
                self.toast("Finishing the current task first - yours starts right after.",
                           tray=False)
                return True
            self.toast("RiotHub is still busy with the last action - try again in a moment.",
                       tray=False)
            return False
        self.busy = True
        self._tick()

        def worker():
            try:
                if guard:       # checked here, off the UI thread (tasklist is slow)
                    g = games_running()
                    if g:
                        self.end_progress(f"Close {', '.join(g)} first.")
                        self.call_ui(lambda: self.notify(
                            "Game running", f"Close {', '.join(g)} before switching."))
                        return
                fn(*args)
            except Exception as e:
                msg = describe_err(e)
                self.end_progress(msg)
                self.call_ui(lambda: self.toast(msg, "bad"))
            finally:
                self.call_ui(self._done)
        threading.Thread(target=worker, daemon=True).start()
        return True

    def _tick(self):
        if getattr(self, "_ticking", False):
            return
        self._ticking = True

        def loop():
            self._spin += 1
            if self.busy or self.progress or self.fetching:
                if not self._ovl_loop:
                    self.draw_overlays()
                self.after(400, loop)
            else:
                self._ticking = False
                self.redraw()
        loop()

    def _done(self):
        self.busy = False
        self.accounts_changed()
        q = getattr(self, "_queued", None)
        if q:
            self._queued = None
            self.after(150, lambda: self.run(q[0], *q[1], guard=q[2]))
        self.persist()
        self.redraw()

    def _close_or_fail(self):
        if not close_client():
            if riot_admin_flags():
                self.call_ui(self.offer_admin_fix)
                raise RuntimeError("The Riot Client is running as administrator, so the "
                                   "switcher isn't allowed to close it.")
            raise RuntimeError("Riot Client wouldn't close. Close it from the tray icon and "
                               "try again.")
        if ELEVATED_SEEN["close"] or ELEVATED_SEEN["launch"]:
            self.call_ui(self.offer_admin_fix)

    def offer_admin_fix(self):
        """One-time offer to stop the Riot Client forcing administrator mode."""
        if getattr(self, "_admin_offered", False):
            return
        flags = riot_admin_flags()
        if not flags:
            return
        self._admin_offered = True
        mine = [f for f in flags if f[0] == "user"]
        if mine and self.confirm(
                "Riot Client runs as administrator",
                "Your Riot Client is set to always run as administrator, so Windows asks for "
                "permission every time RiotHub opens or closes it (or blocks it). Riot "
                "doesn't need this. Turn it off? You can always tick it again in the exe's "
                "Properties > Compatibility.", ok="Turn it off"):
            left = clear_riot_admin_flags()
            ELEVATED_SEEN.update(launch=False, close=False)
            if left:
                self.notify("Almost done", "It's also set for all users. Right-click "
                            "RiotClientServices.exe > Properties > Compatibility > Change "
                            "settings for all users, and untick 'Run this program as an "
                            "administrator'. Then restart the Riot Client.")
            else:
                self.toast("Done. Close the Riot Client once and switching works normally.",
                           "good")
        elif not mine:
            self.notify("Riot Client runs as administrator",
                        "Windows is set to run the Riot Client as administrator for all users, "
                        "so RiotHub has to ask for permission to open or close it. To stop "
                        "that: right-click RiotClientServices.exe > Properties > Compatibility > "
                        "Change settings for all users, untick 'Run this program as an "
                        "administrator'.")

    def signed_in_as(self, name):
        """True if the running Riot Client is signed in as `name` right now."""
        lf = read_lockfile()
        if not lf or not name:
            return False
        try:
            _, _, sub = local_tokens(lf)
        except Exception:
            return False
        want = self.m(name).get("puuid")
        return not want or sub == want

    def _refresh_active(self, verified=None):
        """Re-save the active account's sign-in before switching away, so the saved copy is
        the newest one Riot issued. Never overwrites a good save with a signed-out client."""
        a = self.state_.get("active")
        if not a or not (ACC_DIR / a).exists() or not has_login(RIOT_DIR):
            return
        if verified is False:
            return
        if login_fingerprint(RIOT_DIR) != login_fingerprint(ACC_DIR / a):
            snapshot(ACC_DIR / a)

    def _close_and_keep(self):
        """Check who is signed in, close the client politely, then save that sign-in."""
        a = self.state_.get("active")
        ok = self.signed_in_as(a) if read_lockfile() else None
        self._close_or_fail()
        return ok

    def launch(self, product):
        how = launch_client(product, self.status_opts())
        if how == "proxy":
            self.call_ui(lambda: setattr(self, "proxy_state", "running"))
        return how

    def keep_session_fresh(self, name, delay=0):
        """Copy the Riot Client's current sign-in into the account's save whenever Riot has
        rotated it. Stale saves are the usual reason a 'Stay signed in' account gets logged out."""
        def work():
            if delay:
                time.sleep(delay)
            try:
                if (self.state_.get("active") == name and has_login(RIOT_DIR)
                        and self.signed_in_as(name)
                        and login_fingerprint(RIOT_DIR) != login_fingerprint(ACC_DIR / name)):
                    snapshot(ACC_DIR / name)
                    self.state_.setdefault("session_saved", {})[name] = time.time()
            except Exception as e:
                print("session save failed:", e)
        threading.Thread(target=work, daemon=True).start()

    def _session_tick(self):
        self.after(10 * 60 * 1000, self._session_tick)
        a = self.state_.get("active")
        if a and not self.busy:
            self.keep_session_fresh(a)

    def try_previous_login(self, name, product, wid):
        """Riot rejected the saved sign-in: try the copy from before the last save, once."""
        prev = APP_DIR / PREV_DIR_NAME / name
        tried = self.__dict__.setdefault("_prev_tried", set())
        if name in tried or not has_login(prev) or \
                login_fingerprint(prev) == login_fingerprint(ACC_DIR / name):
            return False
        tried.add(name)
        try:
            self.set_status(f"Riot rejected '{name}'s saved login - trying the one before it…")
            close_client()
            restore(prev)
            self.launch(product)
        except Exception:
            return False
        res = self.wait_login(wid)
        if res != "ok":
            return False
        snapshot(ACC_DIR / name, keep_prev=False)
        self.call_ui(lambda: self.update_meta(name, {"expired": False}))
        self.set_status(f"Recovered '{name}'s login.", "good")
        self.load_stats(name, quiet=True)
        return True

    def wait_login(self, wid, total=90, after_seen=35):
        start = time.time()
        seen = None
        while time.time() - start < total:
            if wid != self.watch_id:
                return "cancelled"
            lf = read_lockfile()
            if lf:
                try:
                    local_tokens(lf)
                    return "ok"
                except NotLoggedIn:
                    seen = seen or time.time()
                except ClientDown:
                    pass
            if seen and time.time() - seen > after_seen:
                return "expired"
            time.sleep(1.5)
        return "expired" if seen else "down"

    def watch(self, name, product=None, progress=False, total=90):
        """After a switch/save: confirm login worked, then load VALORANT stats."""
        self.watch_id += 1
        wid = self.watch_id

        def work():
            res = self.wait_login(wid, total=total)
            if res == "expired" and self.try_previous_login(name, product, wid):
                return
            if res == "expired":
                self.call_ui(lambda: self.update_meta(name, {"expired": True}))
                if progress:
                    self.end_progress("Riot signed this account out.")
                self.set_status(f"'{name}' login expired. Sign in again to fix it.", "bad")
                self.call_ui(lambda: self.expired_prompt(name))
                return
            if res != "ok":
                if progress:
                    self.end_progress(None)
                return
            self.call_ui(lambda: self.update_meta(name, {"expired": False}))
            self.keep_session_fresh(name, delay=20)
            if progress:
                self.step(4, "Loading rank, store and inventory…")
            self.load_stats(name, quiet=True)
            if progress:
                self.end_progress(None)
            if self.m(name).get("roulette"):
                time.sleep(1)
                self.call_ui(lambda: self.shuffle_loadout(quiet=True))
            if product and self.settings.get("close_after_launch"):
                if self.settings.get("status_enabled") and \
                        self.settings.get("status_engine") == "builtin":
                    return  # the chat proxy must keep running
                exe = GAME_EXE.get(product, "").lower()
                end = time.time() + 300
                while time.time() < end and wid == self.watch_id:
                    if exe in running_processes():
                        time.sleep(3)
                        self.call_ui(self.quit_app)
                        return
                    time.sleep(3)
        threading.Thread(target=work, daemon=True).start()

    def refresh_stats(self, name, quiet=False):
        if not name:
            self.notify("No active account", "Log into an account first.")
            return
        if name != self.state_.get("active"):
            if self.m(name).get("puuid"):
                self.refresh_external(force=True, names=[name], loud=True)
            else:
                self.toast(f"Log into {name} once so the app knows who it is.")
            return
        if name in self.fetching:
            return
        self.fetching.add(name)
        self._tick()

        def work():
            try:
                self.load_stats(name, quiet=quiet)
            finally:
                self.call_ui(lambda: (self.fetching.discard(name), self.redraw()))
        threading.Thread(target=work, daemon=True).start()

    def refresh_external(self, force=False, names=None, loud=False):
        """Rank, peak, level and RR history for accounts that aren't logged in, from
        HenrikDev's public API (by PUUID, so name changes don't matter)."""
        if getattr(self, "_ext_busy", False):
            return
        key = self.settings.get("henrik_key") or None
        targets = []
        for n in names or self.accounts():
            m = self.m(n)
            if not m.get("puuid") or m.get("archived"):
                continue
            if n == self.state_.get("active") and time.time() - (m.get("updated") or 0) < 900:
                continue  # the local data is fresher
            if not force and time.time() - (m.get("ext_updated") or 0) < 14 * 60:
                continue
            targets.append(n)
        if not targets:
            return
        self._ext_busy = True
        for n in targets:
            self.fetching.add(n)
        self.redraw()

        def work():
            done_n, need = 0, False
            for n in targets:
                m = self.m(n)
                try:
                    upd = henrik_profile(m["puuid"], m.get("region") or "eu", key)
                    if upd:
                        if upd.get("game_name") and m.get("game_name") and \
                                upd["game_name"] != m["game_name"]:
                            upd["renamed_from"] = f"{m['game_name']}#{m.get('tag', '')}"
                        self.call_ui(lambda n=n, u=upd: self.update_meta(n, u))
                        done_n += 1
                except NeedKey:
                    need = True
                    break
                except Exception as e:
                    print("external refresh failed for", n, describe_err(e))
                time.sleep(1.2)

            def fin():
                self._ext_busy = False
                for n in targets:
                    self.fetching.discard(n)
                self.ext_need_key = need
                if loud:
                    if need:
                        self.toast("Add a free HenrikDev key in Settings to refresh accounts "
                                   "you're not logged into.", "info")
                    elif done_n:
                        self.toast(f"Updated {', '.join(targets)}.", "good", tray=False)
                    else:
                        self.toast("Couldn't reach the stats service right now.", "bad")
                self.redraw()
            self.call_ui(fin)
        threading.Thread(target=work, daemon=True).start()

    def _ext_tick(self):
        self.after(15 * 60 * 1000, self._ext_tick)
        self.refresh_external()
        a = self.state_.get("active")
        shop_reset = (self.m(a).get("store") or {}).get("daily_expires", 0) < time.time()
        if a and not self.busy and not games_running() and \
                (shop_reset or time.time() - (self.m(a).get("updated") or 0) > 30 * 60):
            def check():
                if self.signed_in_as(a):
                    self.call_ui(lambda: self.refresh_stats(a, quiet=True))
            threading.Thread(target=check, daemon=True).start()

    def load_stats(self, name, quiet=False):
        """Worker thread: fetch everything for the logged-in account."""
        m = self.m(name)
        try:
            prof = fetch_all(m.get("region_override"), m.get("shard"),
                             int(self.settings.get("match_count") or 10))
        except NotLoggedIn:
            self.set_status("Riot Client isn't logged in yet.")
            return
        except Exception as e:
            msg = describe_err(e)
            self.set_status(f"Couldn't load stats: {msg}", None if quiet else "bad")
            return
        if m.get("puuid") and m["puuid"] != prof["puuid"]:
            self.set_status(f"The client is logged into a different account than '{name}'. "
                            "Use Update with current login if that's intended.", "bad")
            return
        settings = prof.pop("_settings", None)
        if settings is not None:
            try:
                PREFS_DIR.mkdir(parents=True, exist_ok=True)
                (PREFS_DIR / f"{name}.json").write_text(json.dumps(settings), encoding="utf-8")
            except Exception:
                pass
        prof["expired"] = False

        def apply():
            old_tier = m.get("tier")
            old_store = [o["skin"] for o in (m.get("store") or {}).get("daily") or []]
            old_pen = m.get("penalties")
            if "penalties" in prof:
                self.check_penalty_change(name, old_pen, prof.get("penalties"))
            if prof.get("store"):
                prof["store_history"] = add_store_history(m, prof["store"])
            self.update_meta(name, prof)
            self.check_wishlist(name)
            new_tier = prof.get("tier")
            if old_tier and new_tier and new_tier != old_tier and new_tier >= 3:
                up = new_tier > old_tier
                self.toast(f"{'Rank up' if up else 'Rank down'}: {ASSETS.tier_name(old_tier)} → "
                           f"{ASSETS.tier_name(new_tier)}", "good" if up else "bad")
            old_night = bool((m.get("store") or {}).get("night"))
            if (prof.get("store") or {}).get("night") and not old_night and \
                    m.get("store") is not None:
                self.toast(f"🌙 Night market is open on {name}!", "wish")
            new_store = [o["skin"] for o in (prof.get("store") or {}).get("daily") or []]
            if old_store and new_store and new_store != old_store:
                self.toast(f"New daily store for {name}.", "info")
            dupes = [n for n in self.accounts() if n != name
                     and self.m(n).get("puuid") == prof["puuid"]]
            if dupes:
                self.toast(f"'{name}' and '{dupes[0]}' are the same Riot account. You can "
                           "delete one.", "bad")
            g = self.m(name).get("goal")
            if g and new_tier and new_tier >= g.get("tier", 99) and not g.get("hit"):
                g["hit"] = True
                save_meta(name, self.m(name))
                self.toast(f"Goal reached: {ASSETS.tier_name(g['tier'])}!", "good")
            if not quiet:
                self.toast(f"{name} is up to date.", "good")
            self.enc = {}
            self.duos = None
        self.call_ui(apply)

    def expired_prompt(self, name):
        if self.is_hidden():
            return
        if self.confirm("Login expired",
                        f"Riot signed '{name}' out (password change or it's been a while). "
                        "Sign in again now? RiotHub saves it automatically.",
                        ok="Sign in again"):
            self.relogin(name)

    def check_penalty_change(self, name, before, after):
        had = bool((before or {}).get("items"))
        now_ = bool((after or {}).get("items"))
        if had and not now_:
            self.notify("Penalty over", f"{name} is clear - no more restrictions.")
        elif now_ and not had and before is not None:
            p = after["items"][0]
            self.notify("New penalty", f"{name}: {p['label']}"
                        + (f", ends in {dur(p['expires'] - time.time())}" if p.get("expires")
                           else ""))
        # remind when a known end time passes while the app is open
        for p in (after or {}).get("items") or []:
            left = (p.get("expires") or 0) - time.time()
            if 0 < left < 24 * 3600:
                self.after(int(left * 1000) + 5000,
                           lambda n=name: self.notify("Penalty over",
                                                      f"{n}'s restriction should be over now."))

    def check_wishlist(self, name):
        if not self.settings.get("wishlist_alerts"):
            return
        st = self.m(name).get("store") or {}
        wish = set(self.state_["wishlist"])
        notified = self.state_.setdefault("notified", [])
        fresh = []
        for kind, exp_key in (("daily", "daily_expires"), ("night", "night_expires")):
            for o in st.get(kind) or []:
                if o["skin"] in wish:
                    k = f"{name}|{o['skin']}|{int(st.get(exp_key, 0)) // 600}"
                    if k not in notified:
                        notified.append(k)
                        fresh.append(o["skin"])
        if fresh:
            del notified[:-300]
            save_state(self.state_)
            names = ", ".join(ASSETS.skins.get(s, {}).get("name", "A wishlisted skin")
                              for s in fresh)
            msg = f"★ {names} is in {name}'s store!"
            self.toast(msg, "wish", tray=False)
            self.store_acc = name
            if self.tray:
                try:
                    self.tray.notify(msg, "Wishlist alert")
                except Exception:
                    pass

    def toggle_wish(self, skin):
        wl = self.state_["wishlist"]
        if skin in wl:
            wl.remove(skin)
            self.toast("Removed from wishlist.")
        else:
            wl.append(skin)
            name = ASSETS.skins.get(skin, {}).get("name", "Skin")
            hits = [a for s, a, _ in self.store_hits() if s == skin]
            self.toast(f"★ {name} added." + (f" It's in {hits[0]}'s store right now!"
                                              if hits else " You'll get an alert when it "
                                                           "shows up."), "wish" if hits else "info")
        save_state(self.state_)
        self.redraw()

    def open_item(self, it, owner):
        kind = it.get("kind")
        if kind == "skin":
            SkinDialog(self, it["id"], owner)
        elif kind in ("card", "title"):
            if owner != self.state_.get("active"):
                self.toast(f"Log into {owner} to equip this.")
                return
            if self.confirm("Equip " + kind, f"Use '{it['name']}' on {owner}?", ok="Equip"):
                self.equip_identity(kind, it["id"])
        else:
            self.toast(f"{it['name']}")

    # ------------------------------------------------------------ actions
    def switch(self, name, from_shortcut=False, game=None, quiet=None):
        if not name or name not in self.accounts():
            self.notify("Pick an account", "Select an account first, then press Log in.")
            return
        if not has_login(ACC_DIR / name):
            self.notify("No login saved", f"'{name}' has no saved login. Log into it, then "
                                          "right-click it > Update with current login.")
            return
        if self.m(name).get("expired") and not self.is_hidden():
            if self.confirm("Login expired", f"'{name}' was signed out by Riot last time. "
                                             "Sign in again now?", ok="Sign in again"):
                self.relogin(name)
            return
        self.selected = name
        picked = game in GAMES
        game = game if picked else (self.m(name).get("default_game") or self.state_["game"])
        product = GAMES.get(game)
        if name == self.state_.get("active") and product and read_lockfile():
            # already signed in: no restart needed, just ask the Riot Client to open the game
            def go():
                self.launch(product)
                self.set_status(f"Opening {game} on {name}…", "info")
                self.call_ui(lambda: self.watch(name, product))
            self.run(go, guard=False)
            return
        if quiet is None:
            quiet = not self.settings.get("open_client", True) and not picked
        if quiet:
            if self.run(self._switch, name, None, True):
                self.start_progress(f"Switching to {name}",
                                    ["Closing Riot Client", "Swapping login", "Ready"], name,
                                    "Nothing will open")
            return
        if self.run(self._switch, name, product):
            self.start_progress(f"Switching to {name}",
                                ["Closing Riot Client", "Restoring login",
                                 "Launching " + game, "Signing in",
                                 "Loading stats"], name, "Hang tight")

    def _switch(self, name, product, quiet=False):
        ok = self._close_and_keep()
        self.step(1)
        if name != self.state_.get("active"):
            self._refresh_active(ok)
        snapshot(BACKUP_DIR)
        try:
            restore(ACC_DIR / name)
        except Exception:
            restore(BACKUP_DIR)
            raise
        prev = self.state_.get("active")
        if prev and prev != name:
            self.state_["previous"] = prev
        self.state_["active"] = name
        self.state_["active_since"] = time.time()
        self.state_["last_used"][name] = time.time()
        ds = self.m(name).get("default_status")
        if ds in STATUS_MODES and ds != self.settings.get("status_mode"):
            self.call_ui(lambda: self.set_status_mode(ds))
            self.proxy.mode = ds
            self.settings["status_mode"] = ds
        if quiet:
            save_state(self.state_)
            self.step(2, "Done")
            self.end_progress(None, delay=1.0)
            tip = (" Offline mode only works when RiotHub opens the client."
                   if self.offline_on() else "")
            self.set_status(f"Switched to {name}. Open VALORANT or the Riot Client whenever "
                            f"you like - it'll be signed in.{tip}", "good")
            # pick things up (stats, fresh login save) once you open the client yourself
            self.call_ui(lambda: self.watch(name, None, total=4 * 3600))
            return
        self.step(2)
        self.launch(product)
        self.step(3, "Waiting for Riot to sign in…")
        self.set_status(f"Logged in as {name}.")
        self.call_ui(lambda: self.watch(name, product, progress=True))

    def add_new(self):
        if self.confirm("Add account",
                        "The Riot Client will reopen on the login screen. Sign into the new "
                        "account with 'Stay signed in' ticked and RiotHub picks it up "
                        "automatically."):
            self.run(self._open_login, None)

    def relogin(self, name):
        self.run(self._open_login, name)

    def _open_login(self, target):
        ok = self._close_and_keep()
        self._refresh_active(ok)
        snapshot(BACKUP_DIR)
        clear_login()
        self.state_["active"] = None
        self.launch(None)
        self.set_status("Sign in with 'Stay signed in' ticked…", "info")
        self.call_ui(lambda: self.watch_new_login(target))

    def watch_new_login(self, target):
        self.watch_id += 1
        wid = self.watch_id

        def work():
            res = self.wait_login(wid, total=600, after_seen=600)
            if res != "ok":
                return
            time.sleep(2)
            prof = None
            try:
                prof = fetch_all(match_count=0)
            except Exception:
                pass
            self.call_ui(lambda: self.finish_new_login(target, prof))
        threading.Thread(target=work, daemon=True).start()

    def finish_new_login(self, target, prof):
        if target:
            m = self.m(target)
            if prof and m.get("puuid") and m["puuid"] != prof["puuid"]:
                if not self.confirm("Different account",
                                    f"You signed into {prof.get('game_name')}"
                                    f"#{prof.get('tag')}, not the account saved as '{target}'. "
                                    "Save it as that anyway?", ok="Save anyway"):
                    return
            name = target
        else:
            self.show_window()
            suggested = (prof or {}).get("game_name") or ""
            who = f"{prof['game_name']}#{prof.get('tag')}" if prof and prof.get(
                "game_name") else "the new account"
            name = clean_name(self.ask("Save account",
                                       f"Signed in as {who}. Name this account:", suggested))
            if not name:
                self.toast("Not saved. Use 'Save current login' whenever you're ready.")
                return
            if (ACC_DIR / name).exists() and not self.confirm(
                    "Overwrite?", f"'{name}' already exists. Replace its saved login?",
                    ok="Overwrite"):
                return
        if prof:
            prof.pop("_settings", None)
            upd = dict(prof)
            upd["expired"] = False
            self.update_meta(name, upd)
        self.selected = name
        self.run(self._save, name)

    def save_current(self):
        if not has_login(RIOT_DIR):
            self.notify("Not logged in",
                        "Log into the Riot Client with 'Stay signed in' ticked first.")
            return
        name = clean_name(self.ask("Save account", "Name this account (e.g. Main, Alt):"))
        if not name:
            return
        if (ACC_DIR / name).exists() and not self.confirm(
                "Overwrite?", f"'{name}' already exists. Replace its saved login?",
                ok="Overwrite"):
            return
        self.watch_id += 1
        self.selected = name
        self.run(self._save, name)

    def update_login(self, name):
        if not name:
            return
        if not has_login(RIOT_DIR):
            self.notify("Not logged in", "Log into that account in the Riot Client first.")
            return
        if self.confirm("Update login", f"Save whoever is signed into the Riot Client right "
                                        f"now as '{name}'?", ok="Update"):
            self.m(name).pop("puuid", None)
            self.run(self._save, name)

    def _save(self, name):
        self._close_or_fail()
        if not has_login(RIOT_DIR):
            raise RuntimeError("Login wasn't kept. Tick 'Stay signed in' when logging in.")
        ACC_DIR.mkdir(parents=True, exist_ok=True)
        snapshot(ACC_DIR / name)
        self.state_["active"] = name
        self.state_["active_since"] = time.time()
        self.state_["last_used"][name] = time.time()
        self.launch(None)
        self.set_status(f"Saved '{name}'. Loading stats…", "good")
        self.call_ui(lambda: self.watch(name))

    def launch_only(self):
        def go():
            self.launch(GAMES.get(self.state_["game"]))
            self.set_status(f"Opening {self.state_['game']}…", "info")
        self.run(go, guard=False)

    def reload_assets(self):
        def go():
            self.set_status("Downloading game data…", "info")
            ok = ASSETS.ensure(force=True)
            self.set_status("Game data updated." if ok else f"Failed: {ASSETS.error}",
                            "good" if ok else "bad")
        self.run(go, guard=False)

    def open_folder(self):
        APP_DIR.mkdir(parents=True, exist_ok=True)
        os.startfile(APP_DIR)

    # ---- equip
    def _active_client(self):
        a = self.state_.get("active")
        m = self.m(a)
        vc, _, _, _ = connect(m.get("region_override"), m.get("shard"))
        if m.get("puuid") and vc.puuid != m["puuid"]:
            raise RuntimeError("The Riot Client is logged into a different account.")
        return a, vc

    def equip_skin(self, skin_uuid, chroma=None):
        s = ASSETS.skins[skin_uuid]

        def go():
            a, vc = self._active_client()
            owned_lv = owned_ids(self.m(a), "skins")
            levels = [lv["uuid"] for lv in s["levels"] if lv["uuid"] in owned_lv]
            level = levels[-1] if levels else (s["levels"][0]["uuid"] if s["levels"] else None)
            ch = chroma or (s["chromas"][0]["uuid"] if s["chromas"] else None)
            lo = vc.get_loadout()
            for g in lo.get("Guns") or []:
                if str(g.get("ID", "")).lower() == s["weapon_id"].lower():
                    g["SkinID"], g["SkinLevelID"], g["ChromaID"] = skin_uuid, level, ch
                    break
            else:
                raise RuntimeError("That weapon isn't in your loadout.")
            res = vc.put_loadout(lo) or {}
            # check Riot really took it, rather than assuming
            got = next((g for g in res.get("Guns") or []
                        if str(g.get("ID", "")).lower() == s["weapon_id"].lower()), None)
            if res.get("Guns") and (not got or str(got.get("SkinID", "")).lower()
                                    != skin_uuid.lower()):
                raise RuntimeError("Riot didn't accept the change - do you own this skin on "
                                   f"{a}?")
            eq = dict(self.m(a).get("loadout") or {})
            eq[s["weapon_id"]] = {"skin": skin_uuid, "chroma": ch}
            self.call_ui(lambda: self.update_meta(a, {"loadout": eq}))
            self.set_status(f"Equipped {s['name']}.", "good")
        if not self.run(go, guard=False):
            return

    def equip_identity(self, kind, item_id):
        field = {"card": "PlayerCardID", "title": "PlayerTitleID"}[kind]

        def go():
            a, vc = self._active_client()
            lo = vc.get_loadout()
            lo.setdefault("Identity", {})[field] = item_id
            vc.put_loadout(lo)
            self.call_ui(lambda: self.update_meta(a, {kind: item_id}))
            self.set_status(f"{kind.title()} equipped.", "good")
        self.run(go, guard=False)

    # ---- settings sync
    def apply_sync(self):
        src, dst = self.sync_source, self.state_.get("active")
        if not (src and dst and src != dst):
            return
        try:
            source = json.loads((PREFS_DIR / f"{src}.json").read_text(encoding="utf-8"))
        except Exception:
            self.notify("No saved settings", f"Log into {src} once so its settings get saved.")
            return
        cats = sorted(self.sync_cats)
        what = ", ".join(SYNC_CATEGORIES[c] for c in cats)
        if "VALORANT" in games_running():
            if not self.confirm("VALORANT is open", "Close VALORANT first for the cleanest "
                                                    "result. It may overwrite the copied "
                                                    "settings when it exits.",
                                ok="Copy anyway"):
                return
        if not self.confirm("Copy settings", f"Copy {what} from {src} to {dst}? {dst}'s "
                                             "current settings are backed up first.",
                            ok="Copy"):
            return

        def go():
            a, vc = self._active_client()
            current, host = vc.get_settings()
            PREFS_BACKUP_DIR.mkdir(parents=True, exist_ok=True)
            stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
            (PREFS_BACKUP_DIR / f"{a}__{stamp}.json").write_text(json.dumps(current),
                                                                 encoding="utf-8")
            merged = merge_settings(current, source, set(cats))
            vc.put_settings(merged, host)
            (PREFS_DIR / f"{a}.json").write_text(json.dumps(merged), encoding="utf-8")
            self.set_status(f"Copied {what} from {src} to {a}.", "good")
        self.run(go, guard=False)

    def restore_prefs(self, f):
        if not self.confirm("Restore settings", "Put these settings back on the active "
                                                "account?", ok="Restore"):
            return

        def go():
            a, vc = self._active_client()
            settings = json.loads(Path(f).read_text(encoding="utf-8"))
            _, host = vc.get_settings()
            vc.put_settings(settings, host)
            self.set_status("Settings restored.", "good")
        self.run(go, guard=False)

    # ---- backups
    def export_backup(self):
        if not filedialog:
            return
        pw = Modal(self, "Export backup", "Pick a password. You'll need it to import the "
                                          "backup. It contains your saved logins, so keep it "
                                          "private.", password=True, confirm_password=True,
                   ok="Export").result
        if not pw:
            return
        if len(pw) < 6:
            self.notify("Password too short", "Use at least 6 characters.")
            return
        path = filedialog.asksaveasfilename(
            title="Save backup", defaultextension=".rasbak",
            initialfile=f"riothub-{datetime.now():%Y-%m-%d}.rasbak",
            filetypes=[("RiotHub backup", "*.rasbak")])
        if not path:
            return

        def go():
            self.set_status("Encrypting backup…", "info")
            Path(path).write_bytes(make_backup(pw))
            self.set_status(f"Backup saved to {Path(path).name}.", "good")
        self.run(go, guard=False)

    def import_backup(self):
        if not filedialog:
            return
        path = filedialog.askopenfilename(title="Open backup",
                                          filetypes=[("RiotHub backup", "*.rasbak")])
        if not path:
            return
        pw = Modal(self, "Import backup", "Enter the backup's password. Accounts with the "
                                          "same name are replaced.", password=True,
                   ok="Import").result
        if not pw:
            return

        def go():
            self.set_status("Decrypting backup…", "info")
            restore_backup(Path(path).read_bytes(), pw)

            def reload():
                wish = self.state_.get("wishlist", [])
                self.state_ = load_state()
                for s in wish:
                    if s not in self.state_["wishlist"]:
                        self.state_["wishlist"].append(s)
                self.settings = self.state_["settings"]
                apply_theme(self.settings.get("theme", "Violet"))
                self.meta = {n: load_meta(n) for n in self.accounts()}
                save_state(self.state_)
                self.toast(f"Imported {len(self.accounts())} accounts.", "good")
            self.call_ui(reload)
        self.run(go, guard=False)

    # ---- loadout: roulette / presets / picker
    def _apply_guns(self, lo, picks, owner_meta):
        """picks: {weapon_id: {"skin":…, "chroma":…}}; only applies owned skins."""
        owned = owned_skin_set(owner_meta)
        owned_lv = owned_ids(owner_meta, "skins")
        owned_ch = owned_ids(owner_meta, "chromas")
        applied = skipped = 0
        for g in lo.get("Guns") or []:
            want = picks.get(str(g.get("ID", "")).lower())
            if not want:
                continue
            su = want.get("skin")
            s = ASSETS.skins.get(su)
            weapon = ASSETS.weapons.get(str(g.get("ID", "")).lower()) or ASSETS.weapons.get(
                g.get("ID")) or {}
            if su == weapon.get("default_skin") or (s and su in owned):
                if s:
                    lvls = [lv["uuid"] for lv in s["levels"] if lv["uuid"] in owned_lv]
                    ch = want.get("chroma")
                    base = s["chromas"][0]["uuid"] if s["chromas"] else None
                    if ch not in owned_ch:
                        ch = base
                    g["SkinID"] = su
                    g["SkinLevelID"] = lvls[-1] if lvls else (s["levels"][0]["uuid"]
                                                              if s["levels"] else None)
                    g["ChromaID"] = ch
                applied += 1
            else:
                skipped += 1
        return applied, skipped

    def shuffle_loadout(self, quiet=False):
        a = self.state_.get("active")
        if not a:
            self.toast("Log into an account first.")
            return

        def go():
            a2, vc = self._active_client()
            picks = {w: {"skin": su} for w, su in pick_roulette(self.m(a2)).items()}
            if not picks:
                raise RuntimeError("No owned skins to shuffle yet. Refresh stats first.")
            lo = vc.get_loadout()
            applied, _ = self._apply_guns(lo, picks, self.m(a2))
            vc.put_loadout(lo)
            eq = {g.get("ID"): {"skin": g.get("SkinID"), "chroma": g.get("ChromaID")}
                  for g in lo.get("Guns") or []}
            self.call_ui(lambda: self.update_meta(a2, {"loadout": eq}))
            self.set_status(f"🎲 Shuffled {applied} weapons.", None if quiet else "good")
        self.run(go, guard=False)

    def save_preset(self):
        a = self.selected
        m = self.m(a)
        if not m.get("loadout"):
            self.notify("No loadout yet", "Refresh this account's stats first.")
            return
        name = self.ask("Save loadout preset", "Name this loadout (e.g. Prime set, Pink):")
        if not name:
            return
        self.state_["presets"] = [p for p in self.state_["presets"] if p["name"] != name]
        self.state_["presets"].append({
            "name": name[:28], "from": a, "t": time.time(),
            "guns": {str(k).lower(): v for k, v in (m.get("loadout") or {}).items()},
            "card": m.get("card"), "title": m.get("title")})
        save_state(self.state_)
        self.toast(f"Saved loadout '{name}'.", "good")
        self.redraw()

    def apply_preset(self, preset):
        a = self.state_.get("active")
        if not a:
            self.toast("Log into an account first.")
            return

        def go():
            a2, vc = self._active_client()
            m = self.m(a2)
            lo = vc.get_loadout()
            applied, skipped = self._apply_guns(lo, preset.get("guns") or {}, m)
            ident = lo.setdefault("Identity", {})
            if preset.get("card") in owned_ids(m, "cards"):
                ident["PlayerCardID"] = preset["card"]
            if preset.get("title") in owned_ids(m, "titles"):
                ident["PlayerTitleID"] = preset["title"]
            vc.put_loadout(lo)
            eq = {g.get("ID"): {"skin": g.get("SkinID"), "chroma": g.get("ChromaID")}
                  for g in lo.get("Guns") or []}
            self.call_ui(lambda: self.update_meta(a2, {"loadout": eq,
                                                       "card": ident.get("PlayerCardID"),
                                                       "title": ident.get("PlayerTitleID")}))
            extra = f" ({skipped} skins not owned on {a2}, kept as is)" if skipped else ""
            self.set_status(f"Applied '{preset['name']}' to {applied} weapons{extra}.", "good")
        self.run(go, guard=False)

    def delete_preset(self, preset):
        self.state_["presets"] = [p for p in self.state_["presets"] if p is not preset]
        save_state(self.state_)
        self.redraw()

    def pick_skin_for(self, weapon_id, owner):
        w = ASSETS.weapons.get(weapon_id.lower()) or ASSETS.weapons.get(weapon_id) or {}
        m = self.m(owner)
        owned = owned_skin_set(m)
        skins = [su for su in owned if ASSETS.skins[su]["weapon_id"].lower() == weapon_id.lower()]
        if not skins:
            self.toast(f"No {w.get('name', 'weapon')} skins owned on {owner}.")
            return
        SkinPicker(self, w.get("name", "Weapon"), skins, owner)

    # ---- crosshair library
    def save_crosshair(self, source):
        try:
            settings = json.loads((PREFS_DIR / f"{source}.json").read_text(encoding="utf-8"))
        except Exception:
            self.notify("No saved settings", f"Log into {source} once so its settings get saved.")
            return
        entries = crosshair_entries(settings)
        if not entries:
            self.notify("No crosshair found", f"Couldn't find crosshair settings for {source}.")
            return
        name = self.ask("Save crosshair", f"Name {source}'s crosshair:", f"{source} crosshair")
        if not name:
            return
        self.state_["crosshairs"] = [c for c in self.state_["crosshairs"] if c["name"] != name]
        self.state_["crosshairs"].append({"name": name[:30], "from": source, "t": time.time(),
                                          "entries": entries})
        save_state(self.state_)
        self.toast(f"Saved crosshair '{name}'.", "good")
        self.redraw()

    def apply_crosshair(self, ch):
        a = self.state_.get("active")
        if not a:
            self.toast("Log into an account first.")
            return
        if not self.confirm("Apply crosshair", f"Put '{ch['name']}' on {a}? Current settings "
                                               "are backed up first.", ok="Apply"):
            return

        def go():
            a2, vc = self._active_client()
            current, host = vc.get_settings()
            PREFS_BACKUP_DIR.mkdir(parents=True, exist_ok=True)
            stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
            (PREFS_BACKUP_DIR / f"{a2}__{stamp}.json").write_text(json.dumps(current),
                                                                  encoding="utf-8")
            merged = merge_settings(current, ch["entries"], {ch.get("kind") or "crosshair"})
            vc.put_settings(merged, host)
            (PREFS_DIR / f"{a2}.json").write_text(json.dumps(merged), encoding="utf-8")
            self.set_status(f"Crosshair '{ch['name']}' applied to {a2}. Restart VALORANT to "
                            "see it.", "good")
        self.run(go, guard=False)

    def delete_crosshair(self, ch):
        self.state_["crosshairs"] = [c for c in self.state_["crosshairs"] if c is not ch]
        save_state(self.state_)
        self.redraw()

    # ---- goals / misc
    def change_goal(self, name, step):
        m = self.m(name)
        cur = m.get("tier") or 3
        g = m.get("goal") or {}
        tiers = sorted(t for t in ASSETS.tiers if t >= 3)
        if not tiers:
            return
        target = (g.get("tier") or cur) + step
        target = max(cur + 1, min(max(tiers), target))
        if step == 0:
            self.update_meta(name, {"goal": None})
            return
        start = (m.get("tier") or 0) * 100 + (m.get("rr") or 0)
        self.update_meta(name, {"goal": {"tier": target, "start": g.get("start", start)
                                         if g.get("tier") else start, "set": time.time()}})

    def copy_text(self, text, what="Copied"):
        self.clipboard_clear()
        self.clipboard_append(text)
        self.toast(f"{what}: {text}", "good")

    def open_tracker(self, m):
        if not m.get("game_name"):
            self.toast("Riot ID unknown. Refresh stats first.")
            return
        rid = urllib.parse.quote(f"{m['game_name']}#{m.get('tag', '')}")
        webbrowser.open(f"https://tracker.gg/valorant/profile/riot/{rid}/overview")

    def move_top(self, name):
        order = self.accounts()
        if name in order:
            order.remove(name)
            order.insert(0, name)
            self.state_["order"] = order
            self.persist()
            self.redraw()

    def sort_accounts(self, by):
        names = self.accounts()
        if by == "rank":
            names.sort(key=lambda n: -((self.m(n).get("tier") or 0) * 100 + (self.m(n).get("rr") or 0)))
        elif by == "recent":
            names.sort(key=lambda n: -(self.state_["last_used"].get(n) or 0))
        else:
            names.sort(key=str.lower)
        self.state_["order"] = names
        self.persist()
        self.toast(f"Sorted by {by}.")
        self.redraw()

    def trash_items(self):
        d = APP_DIR / "trash"
        if not d.exists():
            return []
        return sorted((p for p in d.iterdir() if p.is_dir()), key=lambda p: p.stat().st_mtime,
                      reverse=True)

    def restore_trash(self, p):
        name = p.name.split("__")[0]
        if (ACC_DIR / name).exists():
            name = f"{name} (restored)"
        shutil.move(str(p / "login"), str(ACC_DIR / name))
        if (p / "meta.json").exists():
            META_DIR.mkdir(parents=True, exist_ok=True)
            shutil.move(str(p / "meta.json"), str(meta_path(name)))
        _rm(p)
        self.meta.pop(name, None)
        self.persist()
        self.toast(f"Restored '{name}'.", "good")
        self.redraw()

    # ---- live match
    def get_vc(self):
        a = self.state_.get("active")
        if self._vc and time.time() - self._vc[2] < 240 and self._vc[3] == a:
            return self._vc[0], self._vc[1]
        m = self.m(a)
        vc, _, region, _ = connect(m.get("region_override"), m.get("shard"))
        self._vc = (vc, region, time.time(), a)
        return vc, region

    def refresh_live(self, notify=False):
        if self.live_busy or not self.state_.get("active"):
            return
        self.live_busy = True

        def work():
            try:
                vc, region = self.get_vc()
                data = fetch_live(vc, region, self.rank_cache, read_lockfile())
                err = None
            except Exception as e:
                data, err = None, str(e)
                self._vc = None

            def apply():
                prev_phase = (self.live or {}).get("phase")
                if prev_phase == "ingame" and data and data.get("phase") == "none":
                    a_ = self.state_.get("active")
                    self.after(45_000, lambda: self.refresh_stats(a_, quiet=True))
                self.live_busy = False
                self.live_error = err
                if data is not None:
                    self.live = data
                    if not self.enc:
                        me = self.m(self.state_.get("active")).get("puuid")
                        if me:
                            threading.Thread(target=lambda: setattr(
                                self, "enc", encounter_index(me)), daemon=True).start()
                    if data["phase"] == "pregame" and prev_phase != "pregame":
                        if self.settings.get("match_sound") and PreviewAudio.current is None:
                            threading.Thread(target=play_chime, daemon=True).start()
                            flash_taskbar(self)
                        if self.settings.get("agent_picker", True):
                            self.open_picker()
                        elif self.settings.get("auto_live"):
                            self.show_window()
                            self.set_page("live")
                    elif self.picker:
                        if data["phase"] == "pregame":
                            self.picker.render()
                        else:
                            self.close_picker()
                    if notify and data["phase"] != "none" and prev_phase != data["phase"]:
                        msg = ("Agent select started. Open the Live page to see the lobby."
                               if data["phase"] == "pregame" else
                               "Match started. Open the Live page for ranks.")
                        self.toast(msg, "info", tray=False)
                        if self.tray and self.is_hidden():
                            try:
                                self.tray.notify(msg, "Live match")
                            except Exception:
                                pass
                self.redraw()
            self.call_ui(apply)
        threading.Thread(target=work, daemon=True).start()

    def queueing(self):
        d = self.live or {}
        return d.get("phase") == "none" and str(d.get("party_state", "")).upper() == "MATCHMAKING"

    def _live_tick(self):
        on_page = self.page == "live" and not self.is_hidden()
        in_select = (self.live or {}).get("phase") == "pregame"
        picking = bool(self.picker) and in_select
        queueing = self.queueing()
        self.after(2500 if picking else 3000 if (on_page and in_select) or queueing
                   else 6000 if on_page or self.mini else 20000, self._live_tick)
        if not self.state_.get("active"):
            return
        if self.mini and "valorant" in self.running_games and not (on_page or picking or queueing):
            self.refresh_live()
            return
        if on_page or picking or queueing:
            self.refresh_live(notify=queueing and not on_page
                              and bool(self.settings.get("live_alerts")))
        elif (self.settings.get("live_alerts") or self.settings.get("match_sound")
              or self.settings.get("overlay")
              or self.settings.get("auto_live") or self.settings.get("agent_picker", True)):
            def check():
                if "VALORANT" in games_running():
                    self.call_ui(lambda: self.refresh_live(
                        notify=bool(self.settings.get("live_alerts"))))
            threading.Thread(target=check, daemon=True).start()
            return

    # ---- league / collections / exports
    def refresh_league(self, quiet=False):
        a = self.state_.get("active")
        if not a or self.league_busy:
            return
        self.league_busy = True

        def work():
            try:
                lg = fetch_league()
                DDRAGON.ensure()
                err = None
            except Exception as e:
                lg, err = None, str(e)

            def done():
                self.league_busy = False
                if lg:
                    self.update_meta(a, {"league": lg})
                    if not quiet:
                        self.toast("League stats loaded.", "good")
                elif not quiet:
                    self.toast(f"Couldn't read League: {err}", "bad")
                self.redraw()
            self.call_ui(done)
        threading.Thread(target=work, daemon=True).start()

    def equip_collection(self, c):
        a = self.state_.get("active")
        m = self.m(a)
        owned = owned_skin_set(m)
        picks = {ASSETS.skins[su]["weapon_id"].lower(): {"skin": su} for su in c["skins"]
                 if su in owned}
        if not picks:
            self.toast("You don't own any skins from this collection on this account.")
            return

        def go():
            a2, vc = self._active_client()
            lo = vc.get_loadout()
            applied, _ = self._apply_guns(lo, picks, self.m(a2))
            vc.put_loadout(lo)
            eq = {g.get("ID"): {"skin": g.get("SkinID"), "chroma": g.get("ChromaID")}
                  for g in lo.get("Guns") or []}
            self.call_ui(lambda: self.update_meta(a2, {"loadout": eq}))
            self.set_status(f"Equipped {applied} {c['name']} skins.", "good")
        self.run(go, guard=False)

    def export_csv(self, name):
        if not filedialog:
            return
        path = filedialog.asksaveasfilename(title="Export inventory", defaultextension=".csv",
                                            initialfile=f"{name}-skins.csv",
                                            filetypes=[("CSV", "*.csv")])
        if path:
            Path(path).write_text(inventory_csv(self.m(name)), encoding="utf-8")
            self.toast(f"Saved {Path(path).name}.", "good")

    def share_store(self, name):
        if not HAS_PIL:
            self.notify("Needs Pillow", "Run  py -m pip install pillow  to export images.")
            return
        st = self.m(name).get("store") or {}
        daily = st.get("daily") or []
        if not daily:
            self.toast("No store to share yet.")
            return

        def go():
            W, H, pad = 1200, 420, 40
            im = Image.new("RGBA", (W, H), BG)
            d = ImageDraw.Draw(im)
            d.rounded_rectangle((0, 0, W - 1, H - 1), 28, fill=SURFACE)
            title = f"{'Hidden' if self.streamer() else name}'s store"
            d.text((pad, 28), title, fill=TEXT)
            d.text((pad, 52), datetime.now().strftime("%A %d %B %Y"), fill=MUTED)
            cw = (W - pad * 2 - 3 * 20) // 4
            for i, o in enumerate(daily[:4]):
                s = ASSETS.skins.get(o["skin"]) or {}
                ct = ASSETS.ctiers.get(s.get("tier") or "", {})
                col = ct.get("color") or ACCENT
                x = pad + i * (cw + 20)
                d.rounded_rectangle((x, 90, x + cw, H - pad), 20, fill=mix(SURFACE, col, 0.22))
                d.rectangle((x + 20, 90, x + cw - 20, 94), fill=col)
                url = s.get("icon")
                if url and self.images:
                    p = self.images.path(url)
                    if not p.exists():
                        self.images._download(url, p)
                    if p.exists():
                        sk = Image.open(p).convert("RGBA")
                        sk.thumbnail((cw - 40, 150), Image.LANCZOS)
                        im.alpha_composite(sk, (x + (cw - sk.width) // 2, 120 + (150 - sk.height) // 2))
                d.text((x + 20, H - pad - 70), s.get("name", "?"), fill=TEXT)
                d.text((x + 20, H - pad - 44), f"{o.get('cost') or 0:,} VP", fill=GOLD)
            out = Path(os.environ.get("USERPROFILE", APP_DIR)) / "Pictures"
            out = out if out.exists() else APP_DIR
            f = out / f"valorant-store-{name}-{datetime.now():%Y%m%d}.png"
            im.convert("RGB").save(f)
            os.startfile(f)
            self.set_status(f"Saved {f.name} to {out.name}.", "good")
        self.run(go, guard=False)

    # ---- friends / server status
    def refresh_social(self):
        self.friends_busy = True
        self.friends_t = time.time()

        def work():
            fr, ferr, st = None, None, None
            try:
                lf = read_lockfile()
                if not lf:
                    raise ClientDown("Riot Client isn't running.")
                local_tokens(lf)
                fr = fetch_friends(lf)
            except Exception as e:
                ferr = ("Friends show up once the Riot Client is open and signed in."
                        if isinstance(e, (NotLoggedIn, ClientDown)) else
                        f"Couldn't load friends: {describe_err(e)}")
            st = self.status_items

            def done():
                old = {f["puuid"]: f["online"] for f in self.friends or []}
                stars = set(self.state_.get("star_friends") or [])
                if fr and old:
                    for f in fr:
                        if f["puuid"] in stars and f["online"] and not old.get(f["puuid"]):
                            self.toast(f"{f['name'].split('#')[0]} is online.", "good")
                self.friends, self.friends_err = fr, ferr
                self.friends_busy = False
                a_ = self.state_.get("active")
                if fr and a_:
                    self.update_meta(a_, {"friends": [{"puuid": f["puuid"], "name": f["name"]}
                                                      for f in fr if f.get("puuid")]})
                self.redraw()
            self.call_ui(done)
        threading.Thread(target=work, daemon=True).start()

    def copy_friends(self, src):
        dst = self.state_.get("active")
        theirs = self.m(src).get("friends") or []
        mine = {f["puuid"] for f in (self.friends or [])}
        me = self.m(dst).get("puuid")
        todo = [f for f in theirs if f["puuid"] not in mine and f["puuid"] != me
                and self.m(src).get("puuid") != f["puuid"]]
        if not todo:
            self.toast(f"{dst} is already friends with everyone from {src}.")
            return
        if not self.confirm("Copy friends", f"Send friend requests from {dst} to {len(todo)} "
                                            f"people on {src}'s friends list? They still have to "
                                            "accept.", ok=f"Send {len(todo)} requests"):
            return

        def go():
            lf = read_lockfile()
            if not lf:
                raise RuntimeError("Riot Client isn't running.")
            sent = failed = 0
            for f in todo:
                try:
                    send_friend_request(lf, f["name"], f["puuid"])
                    sent += 1
                except Exception:
                    failed += 1
                time.sleep(0.6)
            extra = f" ({failed} failed)" if failed else ""
            self.set_status(f"Sent {sent} friend requests from {dst}{extra}.", "good")
            self.call_ui(self.refresh_social)
        self.run(go, guard=False)

    def toggle_star_friend(self, pu):
        st = self.state_.setdefault("star_friends", [])
        if pu in st:
            st.remove(pu)
        else:
            st.append(pu)
        save_state(self.state_)
        self.redraw()

    # ---- tcno / video / presets of settings
    def import_tcno(self):
        if not filedialog:
            return
        guess = Path(os.environ.get("APPDATA", "")) / "TcNo Account Switcher" / "LoginCache" / "Riot"
        folder = filedialog.askdirectory(title="Pick TcNo's Riot LoginCache folder",
                                         initialdir=str(guess if guess.exists() else Path.home()))
        if not folder:
            return
        found = tcno_accounts(folder)
        if not found:
            self.notify("Nothing found", "No Riot logins in that folder. In TcNo it's usually "
                                         "TcNo Account Switcher\\LoginCache\\Riot.")
            return
        made = 0
        for d in found:
            name = clean_name(d.name) or f"Imported {made + 1}"
            base, i = name, 2
            while (ACC_DIR / name).exists():
                name = f"{base} {i}"
                i += 1
            if import_tcno_folder(d, name):
                made += 1
            else:
                _rm(ACC_DIR / name)
        self.persist()
        self.toast(f"Imported {made} account{'s' if made != 1 else ''} from TcNo.", "good")
        self.redraw()

    def copy_video(self, src):
        dst = self.state_.get("active")
        sp, dp = self.m(src).get("puuid"), self.m(dst).get("puuid")
        if not (sp and dp):
            self.notify("Need stats first", "Both accounts need stats loaded once.")
            return
        if "VALORANT" in games_running():
            self.notify("Close VALORANT", "VALORANT overwrites graphics settings when it exits.")
            return
        try:
            copy_video_settings(sp, dp)
            self.toast(f"Copied graphics settings from {src} to {dst}.", "good")
        except Exception as e:
            self.notify("Couldn't copy", str(e))

    def save_settings_preset(self, source, kind):
        if kind == "crosshair":
            return self.save_crosshair(source)
        try:
            settings = json.loads((PREFS_DIR / f"{source}.json").read_text(encoding="utf-8"))
        except Exception:
            self.notify("No saved settings", f"Log into {source} once so its settings get saved.")
            return
        entries = {k: settings[k] for k in ("actionMappings", "axisMappings") if k in settings}
        if not entries:
            self.notify("No keybinds found", f"Couldn't find keybinds for {source}.")
            return
        name = self.ask("Save keybinds", f"Name {source}'s keybinds:", f"{source} keybinds")
        if not name:
            return
        self.state_["crosshairs"] = [c for c in self.state_["crosshairs"] if c["name"] != name]
        self.state_["crosshairs"].append({"name": name[:30], "from": source, "t": time.time(),
                                          "entries": entries, "kind": "keybinds"})
        save_state(self.state_)
        self.toast(f"Saved keybinds '{name}'.", "good")
        self.redraw()

    # ---- security / background / overlays
    def set_pin(self):
        if self.settings.get("pin"):
            if self.confirm("App lock", "Remove the PIN?", ok="Remove", danger=True):
                self.set_setting("pin", None)
            return
        pin = Modal(self, "Set a PIN", "You'll need it to open RiotHub. 4+ digits or "
                                       "letters.", password=True, confirm_password=True,
                    ok="Set PIN").result
        if not pin:
            return
        if len(pin) < 4:
            self.notify("Too short", "Use at least 4 characters.")
            return
        salt, hsh = pin_hash(pin)
        self.set_setting("pin", {"salt": salt, "hash": hsh})
        self.toast("PIN set. It's asked every time RiotHub opens.", "good")

    def unlock(self):
        pin = self.settings.get("pin")
        if not pin:
            self.locked = False
            return True
        for i in range(3):
            v = Modal(self, "Locked", "Enter your PIN." + (" Try again." if i else ""),
                      password=True, ok="Unlock", cancel="Quit", opaque=True).result
            if v is None:
                return False
            if hmac.compare_digest(pin_hash(v, pin["salt"])[1], pin["hash"]):
                self.locked = False
                return True
        return False

    def pick_bg(self):
        if self.settings.get("bg_image"):
            self.settings["bg_image"] = ""
            self.bg_photo = None
            save_state(self.state_)
            self.redraw()
            return
        if not filedialog:
            return
        p = filedialog.askopenfilename(title="Pick a background image",
                                       filetypes=[("Images", "*.png *.jpg *.jpeg *.webp *.bmp")])
        if p:
            self.bg_photo = None
            self.set_setting("bg_image", p)

    def bg_image(self, w, h):
        p = self.settings.get("bg_image")
        if not (p and HAS_PIL and Path(p).exists()):
            return None
        key = (p, w, h, self.settings.get("theme"))
        if self.bg_photo and self.bg_photo[0] == key:
            return self.bg_photo[1]
        try:
            im = ImageOps.fit(Image.open(p).convert("RGB"), (w, h), Image.LANCZOS)
            r, g, b = (int(BG[i:i + 2], 16) for i in (1, 3, 5))
            im = Image.blend(im, Image.new("RGB", (w, h), (r, g, b)), 0.62)
            ph = ImageTk.PhotoImage(im)
            self.bg_photo = (key, ph)
            self._bg_pil = im
            return ph
        except Exception:
            return None

    def toggle_mini(self):
        if self.mini and self.mini.winfo_exists():
            self.mini.destroy()
            self.mini = None
            self.set_setting("overlay", False)
        else:
            self.mini = MiniWindow(self)
            self.set_setting("overlay", True)

    def toggle_obs(self):
        on = not self.settings.get("obs_overlay")
        self.set_setting("obs_overlay", on)
        if on:
            self.start_obs()
            self.copy_text("http://127.0.0.1:47822", "OBS browser source URL")
        else:
            self.toast("OBS overlay stops when you restart RiotHub.")

    def obs_data(self):
        a = self.state_.get("active")
        m = self.m(a)
        t = today_summary(m) if a else {}
        tier = m.get("tier")
        return {"name": None if self.streamer() or not a else (self.rid(m) or a),
                "rank": ASSETS.tier_name(tier) if a else "",
                "rr": m.get("rr", 0), "icon": ASSETS.tier_icon(tier, True) if tier else None,
                "color": ASSETS.tier_color(tier) or ACCENT, "w": t.get("w", 0),
                "l": t.get("l", 0), "today_rr": t.get("rr", 0)}

    def start_obs(self):
        if self.obs:
            return
        app = self
        page = OBS_PAGE.encode("utf-8")

        class H(BaseHTTPRequestHandler):
            def do_GET(h):
                if h.path.startswith("/data"):
                    body = json.dumps(app._obs_snapshot).encode()
                    ctype = "application/json"
                else:
                    body, ctype = page, "text/html; charset=utf-8"
                h.send_response(200)
                h.send_header("Content-Type", ctype)
                h.send_header("Content-Length", str(len(body)))
                h.send_header("Cache-Control", "no-store")
                h.end_headers()
                h.wfile.write(body)

            def log_message(h, *a):
                pass
        try:
            self.obs = ThreadingHTTPServer(("127.0.0.1", 47822), H)
        except OSError as e:
            self.toast(f"OBS overlay port busy: {e}", "bad")
            return
        self._obs_snapshot = self.obs_data()
        threading.Thread(target=self.obs.serve_forever, daemon=True).start()

    def auto_backup_setup(self):
        if self.settings.get("auto_backup"):
            if self.confirm("Automatic backups", "Turn off weekly backups?", ok="Turn off"):
                self.set_setting("auto_backup", None)
            return
        if not filedialog:
            return
        folder = filedialog.askdirectory(title="Where should weekly backups go?")
        if not folder:
            return
        pw = Modal(self, "Backup password", "Backups are encrypted with this password. It's "
                                            "stored protected by your Windows login so backups "
                                            "can run on their own.", password=True,
                   confirm_password=True, ok="Save").result
        if not pw or len(pw) < 6:
            if pw is not None:
                self.notify("Password too short", "Use at least 6 characters.")
            return
        enc = base64.b64encode(dpapi(pw.encode())).decode()
        self.set_setting("auto_backup", {"folder": folder, "pw": enc, "last": 0})
        self.toast("Weekly backups on. The first one runs now.", "good")
        self.run_auto_backup(force=True)

    def run_auto_backup(self, force=False):
        cfg = self.settings.get("auto_backup")
        if not cfg or (not force and time.time() - cfg.get("last", 0) < 7 * 86400):
            return

        def work():
            try:
                pw = dpapi(base64.b64decode(cfg["pw"]), protect=False).decode()
                folder = Path(cfg["folder"])
                folder.mkdir(parents=True, exist_ok=True)
                (folder / f"riothub-{datetime.now():%Y-%m-%d}.rasbak").write_bytes(
                    make_backup(pw))
                olds = sorted(folder.glob("riothub-*.rasbak"))[:-4]
                for o in olds:
                    o.unlink(missing_ok=True)
                cfg["last"] = time.time()
                self.call_ui(lambda: (save_state(self.state_),
                                      self.toast("Weekly backup saved.", "good")))
            except Exception as e:
                self.log(f"auto backup: {e}")
        threading.Thread(target=work, daemon=True).start()

    def _on_tk_error(self, exc, val, tb):
        import traceback
        self.log("callback: " + "".join(traceback.format_exception(exc, val, tb)))
        try:
            self.toast(f"Something went wrong: {val}", "bad")
        except Exception:
            pass

    def health_check(self):
        def work():
            res = []

            def add(ok, label, detail=""):
                res.append((ok, label, detail))
            exe = client_exe()
            add(bool(exe), "Riot Client installed", exe or "Not found")
            add(RIOT_DIR.exists(), "Riot Client data folder", str(RIOT_DIR))
            lf = read_lockfile()
            if lf:
                try:
                    local_tokens(lf)
                    add(True, "Riot Client logged in", "Local API answering")
                except Exception as e:
                    add(None, "Riot Client open but not logged in", str(e)[:80])
            else:
                add(None, "Riot Client not running", "That's fine, only needed for stats")
            try:
                v = http(Assets.BASE + "/version", timeout=8)["data"]["riotClientVersion"]
                add(True, "valorant-api.com reachable", v)
            except Exception as e:
                add(False, "valorant-api.com unreachable", str(e)[:80])
            add(ASSETS.ready, "Game data loaded", ASSETS.error or ASSETS.version)
            add(HAS_PIL, "Pillow (images)", "" if HAS_PIL else "py -m pip install pillow")
            add(HAS_TRAY, "pystray (tray icon)", "" if HAS_TRAY else "py -m pip install pystray")
            try:
                APP_DIR.mkdir(parents=True, exist_ok=True)
                t = APP_DIR / ".write_test"
                t.write_text("ok")
                t.unlink()
                add(True, "Data folder writable", str(APP_DIR))
            except Exception as e:
                add(False, "Data folder not writable", str(e)[:80])
            try:
                ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
                c, k = APP_DIR / ".c.pem", APP_DIR / ".k.pem"
                c.write_text(LOCAL_CERT.strip() + "\n")
                k.write_text(LOCAL_KEY.strip() + "\n")
                ctx.load_cert_chain(str(c), str(k))
                c.unlink()
                k.unlink()
                add(True, "Status control certificate", "Loads fine")
            except Exception as e:
                add(False, "Status control certificate", str(e)[:80])
            fails = self.hotkeys.failed if self.hotkeys else []
            add(not fails, "Hotkeys", "All registered" if not fails else
                "Taken by another app: " + ", ".join(map(str, fails)))
            add(None if not league_lockfile() else True, "League client",
                "Open" if league_lockfile() else "Not open (optional)")
            self.call_ui(lambda: HealthDialog(self, res))
        self.toast("Running health check…")
        threading.Thread(target=work, daemon=True).start()

    # ---- session recap
    def session_begin(self):
        a = self.state_.get("active")
        if not a:
            return
        self.session = {"name": a, "t": time.time()}

    def session_end(self):
        sess = getattr(self, "session", None)
        self.session = None
        if not sess or time.time() - sess["t"] < 300:
            return
        name = sess["name"]
        if name == self.state_.get("active"):
            self.refresh_stats(name, quiet=True)
        self.after(35_000, lambda: self.session_recap(sess))

    def session_recap(self, sess):
        m = self.m(sess["name"])
        games = [x for x in m.get("rr_history") or [] if x["start"] >= sess["t"] - 60]
        ms = [x for x in m.get("matches") or [] if (x.get("start") or 0) >= sess["t"] - 60]
        w = sum(1 for x in ms if x.get("won") is True)
        l = sum(1 for x in ms if x.get("won") is False)
        rr = sum(x["delta"] for x in games)
        length = dur(time.time() - sess["t"])
        parts = [f"{length} played"]
        if ms:
            parts.append(f"{w}W {l}L")
        if games:
            parts.append(f"{rr:+d} RR")
        msg = f"Session on {sess['name']}: " + "  ·  ".join(parts)
        m["last_session"] = {"t": sess["t"], "len": time.time() - sess["t"], "w": w, "l": l,
                             "rr": rr, "ranked": len(games)}
        save_meta(sess["name"], m)
        self.toast(msg, "good" if rr >= 0 else "info", tray=False)
        if self.tray:
            try:
                self.tray.notify(msg, "Session recap")
            except Exception:
                pass
        self.redraw()

    def check_patch(self):
        last = self.state_.get("assets_checked", 0)
        if time.time() - last < 6 * 3600:
            return
        self.state_["assets_checked"] = time.time()

        def work():
            try:
                v = http(Assets.BASE + "/version", timeout=10)["data"]["riotClientVersion"]
            except Exception:
                return
            if ASSETS.version and v != ASSETS.version:
                ok = ASSETS.ensure(force=True)
                if ok:
                    if self.images:
                        self.call_ui(lambda: self.images.failed.clear())
                    self.set_status("New VALORANT patch: game data updated.", "good")
        threading.Thread(target=work, daemon=True).start()

    def log(self, msg):
        self.errors.append(f"{datetime.now():%Y-%m-%d %H:%M:%S}  {msg}")
        self.errors = self.errors[-300:]

    def export_diagnostics(self):
        if not filedialog:
            return
        path = filedialog.asksaveasfilename(title="Save diagnostics", defaultextension=".zip",
                                            initialfile="riothub-diagnostics.zip",
                                            filetypes=[("Zip", "*.zip")])
        if not path:
            return
        st = json.loads(json.dumps(self.state_))
        st["settings"].pop("auto_backup", None)
        st["settings"].pop("pin", None)
        info = {"version": VERSION, "python": sys.version, "pillow": HAS_PIL, "tray": HAS_TRAY,
                "assets_ready": ASSETS.ready, "assets_error": ASSETS.error,
                "accounts": len(self.accounts()), "proxy": self.proxy_state,
                "client": client_exe(), "lockfile": LOCKFILE.exists()}
        with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
            z.writestr("info.json", json.dumps(info, indent=2))
            z.writestr("state.json", json.dumps(st, indent=2))
            z.writestr("log.txt", "\n".join(self.errors) or "(empty)")
        self.toast("Diagnostics saved (no logins or passwords included).", "good")

    def auto_offline_check(self):
        if not (self.settings.get("auto_offline") and self.settings.get("status_enabled")):
            return
        a, b = int(self.settings.get("offline_from", 0)), int(self.settings.get("offline_to", 8))
        hr = datetime.now().hour
        inside = (a <= hr < b) if a < b else (hr >= a or hr < b)
        want = "offline" if inside else "online"
        if self.state_.get("_auto_mode") != want:
            self.state_["_auto_mode"] = want
            if self.settings.get("status_mode") != want:
                self.set_status_mode(want)

    def account_icon(self, name):
        url = self.card_url(name)
        src = self.images.file(url) if (self.images and url) else None
        if src and HAS_PIL:
            try:
                ICON_DIR.mkdir(parents=True, exist_ok=True)
                im = ImageOps.fit(Image.open(src).convert("RGBA"), (256, 256), Image.LANCZOS)
                mask = Image.new("L", (256, 256), 0)
                ImageDraw.Draw(mask).rounded_rectangle((0, 0, 255, 255), 56, fill=255)
                im.putalpha(ImageChops.multiply(im.getchannel("A"), mask))
                p = ICON_DIR / f"{name}.ico"
                im.save(p, sizes=[(16, 16), (32, 32), (48, 48), (64, 64), (128, 128),
                                  (256, 256)])
                return p
            except Exception:
                pass
        if getattr(sys, "frozen", False):
            return Path(sys.executable)
        return self.app_ico

    def shortcut(self, name, game=None):
        if not name:
            return
        try:
            create_shortcut(name, self.account_icon(name), game)
            label = f"{game} - {name}" if game and GAMES.get(game) else f"Log in as {name}"
            self.toast(f"Added '{label}' to your desktop.", "good")
        except Exception as e:
            self.notify("Couldn't create shortcut", str(e))

    def shortcut_all(self):
        names = self.accounts()
        if not names:
            self.notify("No accounts", "Save an account first.")
            return
        errors = []
        for n in names:
            try:
                create_shortcut(n, self.account_icon(n))
            except Exception as e:
                errors.append(f"{n}: {e}")
        if errors:
            self.notify("Some shortcuts failed", "\n".join(errors))
        else:
            self.toast(f"Added {len(names)} shortcuts to your desktop.", "good")

    def edit(self, name):
        if not name:
            return
        r = AccountEditor(self, name, self.m(name)).result
        if not r:
            return
        new = r.pop("name")
        startup = r.pop("_startup", False)
        if new != name:
            if (ACC_DIR / new).exists():
                self.notify("Rename", f"'{new}' already exists.")
                return
            (ACC_DIR / name).rename(ACC_DIR / new)
            ACC_GEN[0] += 1
            for d in (META_DIR, PREFS_DIR):
                if (d / f"{name}.json").exists():
                    (d / f"{name}.json").replace(d / f"{new}.json")
            self.meta[new] = self.meta.pop(name, {})
            s = self.state_
            if s.get("active") == name:
                s["active"] = new
            if self.selected == name:
                self.selected = new
            if self.sync_source == name:
                self.sync_source = new
            s["order"] = [new if n == name else n for n in s.get("order", [])]
            for k in ("last_used", "playtime"):
                if name in s[k]:
                    s[k][new] = s[k].pop(name)
            save_state(s)
        self.update_meta(new, r)
        if startup:
            self.settings["startup_account"] = new
        elif self.settings.get("startup_account") in (name, new):
            self.settings["startup_account"] = None
        self.persist()

    def delete(self, name):
        if not name:
            return
        if self.confirm("Delete account", f"Remove '{name}' from RiotHub? Your Riot "
                                          "account itself isn't affected, and you can restore "
                                          "it from Settings > Recently deleted.", ok="Delete",
                        danger=True):
            trash = APP_DIR / "trash" / f"{name}__{int(time.time())}"
            trash.mkdir(parents=True, exist_ok=True)
            shutil.move(str(ACC_DIR / name), str(trash / "login"))
            if meta_path(name).exists():
                shutil.move(str(meta_path(name)), str(trash / "meta.json"))
            for old in self.trash_items()[5:]:
                _rm(old)
            _rm(PREFS_DIR / f"{name}.json")
            _rm(ICON_DIR / f"{name}.ico")
            self.meta.pop(name, None)
            if self.state_.get("active") == name:
                self.state_["active"] = None
            if self.selected == name:
                self.selected = None
            for k in ("last_used", "playtime"):
                self.state_[k].pop(name, None)
            self.persist()
            self.redraw()


def dark_menus():
    """Make every Windows menu this app shows (the tray icon's right-click menu included)
    use the dark theme. Uses the same uxtheme switch Explorer uses; harmless if missing."""
    try:
        ux = ctypes.WinDLL("uxtheme")
        set_mode = ux[135]          # SetPreferredAppMode (1809: AllowDarkModeForApp)
        set_mode.argtypes = [ctypes.c_int]
        set_mode(2)                 # 2 = force dark
        ux[136]()                   # FlushMenuThemes
    except Exception:
        pass


def main():
    if os.name != "nt":
        print("RiotHub only runs on Windows.")
        sys.exit(1)
    args = sys.argv[1:]
    login = game = None
    if "--login" in args:
        i = args.index("--login")
        if i + 1 < len(args):
            login = args[i + 1]
    if "--game" in args:
        i = args.index("--game")
        if i + 1 < len(args) and args[i + 1] in GAMES:
            game = args[i + 1]
    tray_start = "--tray" in args
    if ipc_send({"cmd": "login", "name": login, "game": game} if login else {"cmd": "show"}):
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    try:
        dark_menus()
    except Exception:
        pass
    ACC_DIR.mkdir(parents=True, exist_ok=True)
    hidden = tray_start or (bool(login) and HAS_TRAY)
    app = App(start_hidden=hidden)
    if not hidden and app.locked:
        app.withdraw()
        if not app.unlock():
            app.quit_app()
            return
        app.deiconify()
    if app.settings.get("overlay"):
        app.after(1500, lambda: setattr(app, "mini", MiniWindow(app)))
    if app.settings.get("obs_overlay"):
        app.start_obs()
    start = app.settings.get("startup_account")
    if login:
        app.after(800, lambda: app.switch(login, from_shortcut=True))
    elif start and start in app.accounts() and start != app.state_.get("active"):
        app.after(1500, lambda: app.switch(start))
    if not app.settings.get("toured") and not hidden:
        app.after(900, app.tour)
    app.mainloop()


if __name__ == "__main__":
    main()
