<p align="center">
  <img src="assets/logo-256.png" width="128" alt="RiotHub logo">
</p>

<h1 align="center">RiotHub</h1>

<p align="center">
  One-click account switching and an instant launcher for Riot games — plus a full VALORANT companion.<br>
  No passwords. No logging out. Just pick an account and play.
</p>

<p align="center">
  <a href="../../releases/latest"><b>⬇ Download the latest version</b></a>
</p>

---

## What it does

**Switch accounts instantly.** Save each Riot account once, then swap between them with one click, a hotkey or a desktop shortcut. RiotHub never sees or stores your password — it keeps the Riot Client's own "Stay signed in" login for each account, on your PC only.

**Launch games instantly.** The Play page works like a game library for VALORANT, League of Legends / TFT, Legends of Runeterra and 2XKO. If you're already signed in, Play starts the game straight away.

**VALORANT companion**
- Rank, peak, RR history, match history with full scoreboards and round-by-round results
- Daily shop, night market and bundles for every account, with wishlist alerts
- Inventory, loadouts, skin previews with in-app video, inventory value
- Live lobby ranks in agent select and in game (hidden names stay hidden)
- Party controls: see who's in your party, start or stop queue, change mode, open or close the party — from the app, the tray or the mini overlay
- Optional match-found sound and taskbar flash for when you're tabbed out
- "Ranked ready" badges show which accounts can queue competitive right now
- Copy crosshair, keybinds and settings between accounts
- Weekly missions and battle pass progress across all your accounts
- Penalty details with countdowns, server status, leaderboard, friends and chat
- Appear offline, themes, tray icon, hotkeys, encrypted backups

## Install

1. Download **RiotHub Setup.exe** from the [latest release](../../releases/latest) and run it.
   (Or grab **RiotHub.exe** if you'd rather not install anything.)
2. Open RiotHub and press **Add account**. The Riot Client opens on its login screen.
3. Sign in with **Stay signed in** ticked. RiotHub saves it automatically. Repeat for each account.

RiotHub updates itself — you'll get a prompt when a new version is out.

> Windows may show "Windows protected your PC" the first time, because the app isn't code-signed yet. Click **More info → Run anyway**.

## FAQ

**Is my password safe?**
RiotHub never asks for, sees or stores your password. It saves the Riot Client's own sign-in files for each account in `%APPDATA%\RiotHub` on your PC. Nothing is sent anywhere.

**Can this get me banned?**
RiotHub doesn't touch game memory or files and doesn't automate gameplay. It uses the same local Riot Client API that the official client uses, like other popular companion tools. The optional "pick an agent from the app" feature is off by default and you use it at your own risk.

**Do I need the HenrikDev key?**
No. It's optional and free — it powers the leaderboard and keeps the rank of accounts you aren't logged into up to date. Get one at [henrikdev.xyz](https://api.henrikdev.xyz/dashboard/) and paste it in Settings → Stats & alerts.

**Where is my data?**
`%APPDATA%\RiotHub`. Uninstalling keeps it, so reinstalling never loses your accounts.

## Build it yourself

You need [Python 3.10+](https://www.python.org/downloads/) on Windows.

```bat
py -m pip install -r requirements.txt
build.bat
```

You get the portable `dist\RiotHub.exe` and the faster-starting `dist\app\RiotHub\` folder the installer uses. Compile `installer.iss` with [Inno Setup](https://jrsoftware.org/isinfo.php) to make the installer.

## Making a release (for maintainers)

On GitHub, go to **Releases → Draft a new release**, create a new tag that's higher than the last one (like `v1.1.0`) and publish. GitHub Actions builds `RiotHub.exe` and `RiotHub Setup.exe` and attaches them to the release within a few minutes, and everyone's RiotHub offers the update.

## Legal

RiotHub isn't endorsed by Riot Games and doesn't reflect the views or opinions of Riot Games or anyone officially involved in producing or managing Riot Games properties. Riot Games, and all associated properties are trademarks or registered trademarks of Riot Games, Inc.

Released under the [MIT License](LICENSE).
