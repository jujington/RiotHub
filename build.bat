@echo off
rem Builds both versions of RiotHub:
rem   dist\RiotHub.exe          portable single file
rem   dist\app\RiotHub\         fast-starting folder (what the installer ships)
py -m PyInstaller --noconfirm --onefile --windowed --name "RiotHub" --icon logo.ico --collect-all av --workpath build\onefile RiotHub.pyw || goto :fail
py -m PyInstaller --noconfirm --onedir --windowed --name "RiotHub" --icon logo.ico --collect-all av --workpath build\onedir --distpath dist\app RiotHub.pyw || goto :fail
echo.
echo Done: dist\RiotHub.exe and dist\app\RiotHub\
echo To make the installer, compile installer.iss with Inno Setup.
pause
exit /b 0
:fail
echo Build failed.
pause
exit /b 1
