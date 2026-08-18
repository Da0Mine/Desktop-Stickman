@echo off
cd /d "%~dp0"
python stickman_pet.py
if %errorlevel% neq 0 pause
