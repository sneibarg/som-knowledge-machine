@echo off
cd /d "%~dp0"
clojure -J-Xmx4g -M:start
exit /b %ERRORLEVEL%
