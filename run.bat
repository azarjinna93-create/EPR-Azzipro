@echo off
cd /d "%~dp0"
title Azzi Soft
python -m pip install -q -r requirements.txt
start "" http://127.0.0.1:5000
python app.py
pause
