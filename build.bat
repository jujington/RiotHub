@echo off
rem Builds dist\RiotHub.exe
py -m PyInstaller --noconfirm --onefile --windowed --name "RiotHub" --icon logo.ico --collect-all av RiotHub.pyw
echo.
echo Done: dist\RiotHub.exe
pause
