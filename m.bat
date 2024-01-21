@echo off
if %1'==test' goto :test
python main.py "%*" | C:\Users\sgraham\Sync\utils\clang-format\clang-format.exe -style=Chromium
goto :EOF

:test
python main.py %1 %2 %3 %4 %5
