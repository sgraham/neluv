@echo off
if %1'==test' goto :test
python main.py "%1" | C:\Users\sgraham\Sync\utils\clang-format\clang-format.exe -style=Chromium
goto :EOF

:test
python main.py test
