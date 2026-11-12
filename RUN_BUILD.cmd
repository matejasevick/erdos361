@echo off
REM Erdos #361 Lean verification. Double-click to run.
REM Builds a copy of this folder in C:\erdos361-build; logs go to ..\erdos361-build-logs
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0build.ps1"
pause
