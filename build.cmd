@echo off
rem Compiles the modules in dependency order and checks the compiled objects with coqchk.
rem Usage: build.cmd [path-to-rocq-bin]
setlocal
set "BIN=%~1"
if "%BIN%"=="" set "BIN=C:\Rocq-Platform~9.0~2025.08\bin"
set "PATH=%BIN%;%PATH%"
cd /d "%~dp0"
for %%f in (Vectors Actions Sums LightCone Survival Resources Judges Independence Population Summary) do (
  "%BIN%\coqc.exe" -Q . BeNice %%f.v || exit /b 1
)
"%BIN%\coqchk.exe" -silent -o -Q . BeNice BeNice.Summary || exit /b 1
endlocal
