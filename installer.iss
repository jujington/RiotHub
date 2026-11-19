; Inno Setup script - builds "RiotHub Setup.exe"
; 1) Build the app first:  build.bat
; 2) Install Inno Setup (free): https://jrsoftware.org/isinfo.php
; 3) Right-click this file > Compile  (or: "C:\Program Files (x86)\Inno Setup 6\ISCC.exe" installer.iss)
; The finished installer appears in the "installer" folder.
; GitHub Actions runs this automatically for every release tag.

#define MyAppName "RiotHub"
#ifndef MyAppVersion
  #define MyAppVersion "11.0"
#endif
#define MyAppPublisher "RiotHub"
#define MyExeName "RiotHub.exe"

[Setup]
; Keep this AppId the same forever so updates replace the old install.
AppId={{6B1E2C0A-4C5E-4C2B-9E1A-7A3F1D2B9C10}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={localappdata}\Programs\{#MyAppName}
DefaultGroupName={#MyAppName}
DisableProgramGroupPage=yes
; Per-user install: no admin prompt, and the app can update itself in place.
PrivilegesRequired=lowest
OutputDir=installer
OutputBaseFilename={#MyAppName} Setup
SetupIconFile=logo.ico
UninstallDisplayIcon={app}\{#MyExeName}
Compression=lzma2
SolidCompression=yes
WizardStyle=modern
CloseApplications=yes

[Tasks]
Name: "desktopicon"; Description: "Create a desktop shortcut"; GroupDescription: "Shortcuts:"
Name: "startup"; Description: "Start with Windows (in the tray)"; GroupDescription: "Shortcuts:"; Flags: unchecked

[Files]
Source: "dist\{#MyExeName}"; DestDir: "{app}"; Flags: ignoreversion

[Icons]
Name: "{group}\{#MyAppName}"; Filename: "{app}\{#MyExeName}"
Name: "{group}\Uninstall {#MyAppName}"; Filename: "{uninstallexe}"
Name: "{userdesktop}\{#MyAppName}"; Filename: "{app}\{#MyExeName}"; Tasks: desktopicon
Name: "{userstartup}\{#MyAppName}"; Filename: "{app}\{#MyExeName}"; Parameters: "--tray"; Tasks: startup

[Run]
Filename: "{app}\{#MyExeName}"; Description: "Launch {#MyAppName}"; Flags: nowait postinstall skipifsilent

; Saved accounts live in %APPDATA%\RiotHub and are kept on uninstall on purpose,
; so reinstalling or updating never loses anyone's logins.
