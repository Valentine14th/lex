#!/bin/bash
# run_all.sh
# Purpose: launch external consent platform, internal purpose platform, and FUSE daemon.

set -e

# --- Define base paths ---
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE="$ROOT_DIR"
VENV_PATH="$ROOT_DIR/.gdprfs-venv"

# --- Step 1: External Consent Platform (port 5000) ---
gnome-terminal -- bash -c "
cd $BASE/external_consent_platform;
source $VENV_PATH/bin/activate;
python app.py;
exec bash
"

# --- Step 2: Internal Purpose Platform (port 8000) ---
gnome-terminal -- bash -c "
cd $BASE/internal_purpose_platform;
source $VENV_PATH/bin/activate;
python app.py;
exec bash
"

# --- Step 3: LLM Analyzer (port 5005) ---
gnome-terminal -- bash -c "
cd $BASE/LLManalyzer;
source $VENV_PATH/bin/activate;
python api.py;
exec bash
"

# --- Step 4: FUSE daemon (requires root privileges) ---
gnome-terminal -- bash -c "
cd $ROOT_DIR;
source $VENV_PATH/bin/activate;
./reset_myfs_sudo.sh;
exec bash
"
