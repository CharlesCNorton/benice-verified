@echo off
rem Compiles the development and checks the compiled proof object with coqchk.
rem Usage: build.cmd [path-to-rocq-bin]
setlocal
set "BIN=%~1"
if "%BIN%"=="" set "BIN=C:\Rocq-Platform~9.0~2025.08\bin"
set "PATH=%BIN%;%PATH%"
cd /d "%~dp0"
"%BIN%\coqc.exe" benice_verified.v || exit /b 1
"%BIN%\coqchk.exe" -silent -o -Q . "" benice_verified || exit /b 1
endlocal
