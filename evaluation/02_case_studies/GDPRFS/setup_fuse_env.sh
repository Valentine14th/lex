#!/bin/bash
# setup_fuse_env.sh
# Purpose: Configure fuse-python for a virtual environment and ensure /dev/fuse permissions.

set -e

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV_DIR=.gdprfs-venv
PYTHON_VERSION=python3.12

echo "🔹 Ensuring virtual environment exists..."
if [ ! -f "$VENV_DIR/bin/activate" ]; then
    echo "Virtual environment not found. Creating $VENV_DIR..."
    $PYTHON_VERSION -m venv "$VENV_DIR"
fi

echo "🔹 Activating virtual environment..."
source "$VENV_DIR/bin/activate"

echo "🔹 Loading OpenAI key from openai.secret (if present)..."
if [ -f "openai.secret" ]; then
    OPENAI_SECRET_RAW="$(head -n1 openai.secret | tr -d '\r')"

    if [[ "$OPENAI_SECRET_RAW" == OPENAI_API_KEY=* ]]; then
        OPENAI_SECRET_RAW="${OPENAI_SECRET_RAW#OPENAI_API_KEY=}"
    fi

    OPENAI_SECRET_RAW="$(printf '%s' "$OPENAI_SECRET_RAW" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')"

    if [ -n "$OPENAI_SECRET_RAW" ]; then
        export OPENAI_API_KEY="$OPENAI_SECRET_RAW"

        if [ -f ".env" ]; then
            if grep -q '^OPENAI_API_KEY=' .env; then
                sed -i "s|^OPENAI_API_KEY=.*|OPENAI_API_KEY=$OPENAI_API_KEY|" .env
            else
                printf '\nOPENAI_API_KEY=%s\n' "$OPENAI_API_KEY" >> .env
            fi
        else
            printf 'OPENAI_API_KEY=%s\n' "$OPENAI_API_KEY" > .env
        fi

        echo "OPENAI_API_KEY loaded and .env updated."
    else
        echo "openai.secret exists but is empty. Skipping."
    fi
else
    echo "openai.secret not found. Skipping."
fi

PY_MM="$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
SITE_PACKAGES="$VENV_DIR/lib/python$PY_MM/site-packages"

# Try common install locations for python-fuse (egg dir first, then plain dist-packages)
SYSTEM_FUSE_PATH="$(ls -d \
    /usr/local/lib/python$PY_MM/dist-packages/fuse_python-*.egg \
    /usr/lib/python$PY_MM/dist-packages/fuse_python-*.egg \
    2>/dev/null | head -n1 || true)"

if [ -z "$SYSTEM_FUSE_PATH" ]; then
    echo "🔹 python-fuse not found in system paths. Trying to install python3-fuse..."
    if command -v apt >/dev/null 2>&1; then
        sudo apt update -y
        sudo apt install -y python3-fuse || true
    fi

    SYSTEM_FUSE_PATH="$(ls -d \
        /usr/local/lib/python$PY_MM/dist-packages/fuse_python-*.egg \
        /usr/lib/python$PY_MM/dist-packages/fuse_python-*.egg \
        2>/dev/null | head -n1 || true)"

    if [ -f "/usr/lib/python3/dist-packages/fuse.py" ]; then
        SYSTEM_FUSE_PATH="/usr/lib/python3/dist-packages"
    elif [ -f "/usr/local/lib/python3/dist-packages/fuse.py" ]; then
        SYSTEM_FUSE_PATH="/usr/local/lib/python3/dist-packages"
    fi
fi

if [ -z "$SYSTEM_FUSE_PATH" ]; then
    echo "❌ Could not locate system python-fuse files (fuse.py/fuseparts)."
    echo "   Install python-fuse for your system Python, then re-run this script."
    exit 1
fi

echo "🔹 Checking/Installing poppler-utils (pdftotext)..."
if ! command -v pdftotext &> /dev/null; then
    echo "Installing poppler-utils..."
    sudo apt update -y
    sudo apt install -y poppler-utils
    echo "poppler-utils installed"
else
    echo "poppler-utils already present"
fi

echo "🔹 Checking FUSE device group and permissions..."
sudo groupadd fuse 2>/dev/null || true
sudo usermod -aG fuse "$USER"
sudo chown root:fuse /dev/fuse
sudo chmod 660 /dev/fuse
echo "/dev/fuse permissions:"
ls -l /dev/fuse

echo "🔹 Ensuring user is part of the fuse group..."
groups "$USER" | grep -q fuse || echo "Please log out and log back in to apply group membership."

echo "🔹 Cleaning any conflicting local fuse.py..."
rm -f "$SITE_PACKAGES/fuse.py"
rm -f "$SITE_PACKAGES/fuseparts"

echo "🔹 Creating symlinks for fuse and fuseparts..."
if [ -e "$SYSTEM_FUSE_PATH/fuseparts" ]; then
    sudo ln -sf "$SYSTEM_FUSE_PATH/fuseparts" "$SITE_PACKAGES/fuseparts"
fi
ln -sf "$SYSTEM_FUSE_PATH/fuse.py" "$SITE_PACKAGES/fuse.py"

echo "Symlink verification:"
ls -l "$SITE_PACKAGES/fuse.py" "$SITE_PACKAGES/fuseparts" 2>/dev/null || true

echo "🔹 Testing FUSE import..."
python3 -c "from fuse import Fuse; print('Fuse imported successfully')"

echo "🔹 Installing/Building EnfGuard..."
ENFGUARD_DIR="$ROOT_DIR/enfguard"
ENFGUARD_BIN="$ENFGUARD_DIR/bin/enfguard.exe"
ENFGUARD_REPO="https://github.com/runtime-enforcement/whyenf.git"
ENFGUARD_BRANCH="new_temp"

if [ ! -x "$ENFGUARD_BIN" ]; then
    if command -v apt >/dev/null 2>&1; then
        sudo apt update -y
        sudo apt install -y opam libgmp-dev git
    fi

    if [ ! -d "$HOME/.opam" ]; then
        opam init -y --disable-sandboxing
    fi

    if ! opam switch list --short | grep -qx "4.13.1"; then
        opam switch create 4.13.1
    fi

    eval "$(opam env --switch=4.13.1)"

    opam install -y dune core_kernel base zarith menhir js_of_ocaml js_of_ocaml-ppx \
        zarith_stubs_js dune-build-info qcheck pyml calendar

    if [ ! -d "$ENFGUARD_DIR/.git" ]; then
        git clone --branch "$ENFGUARD_BRANCH" "$ENFGUARD_REPO" "$ENFGUARD_DIR"
    else
        git -C "$ENFGUARD_DIR" remote set-url origin "$ENFGUARD_REPO"
        git -C "$ENFGUARD_DIR" fetch origin "$ENFGUARD_BRANCH"
        git -C "$ENFGUARD_DIR" checkout "$ENFGUARD_BRANCH"
        git -C "$ENFGUARD_DIR" pull --ff-only origin "$ENFGUARD_BRANCH"
    fi

    (cd "$ENFGUARD_DIR" && dune build)

    if [ ! -f "$ENFGUARD_BIN" ] && [ -f "$ENFGUARD_DIR/_build/default/bin/enfguard.exe" ]; then
        mkdir -p "$ENFGUARD_DIR/bin"
        cp "$ENFGUARD_DIR/_build/default/bin/enfguard.exe" "$ENFGUARD_BIN"
    fi

    chmod +x "$ENFGUARD_BIN" 2>/dev/null || true
fi

if [ -x "$ENFGUARD_BIN" ]; then
    echo "EnfGuard ready: $ENFGUARD_BIN"
else
    echo "❌ EnfGuard build/install failed. Expected binary not found at: $ENFGUARD_BIN"
    exit 1
fi


echo "🔹 Installing SQLAlchemy in the virtual environment..."
pip install --upgrade pip
pip install sqlalchemy

echo "Verifying SQLAlchemy import..."
python3 -c "import sqlalchemy; print('SQLAlchemy imported successfully, version:', sqlalchemy.__version__)"
echo "---🔹 SQLAlchemy package details:---"
pip show sqlalchemy

echo "🔹 Installing Flask + Requests in the virtual environment..."
pip install flask requests 

echo "Verifying Flask installation..."
python3 -c "import flask; import requests; print('Flask version:', flask.__version__)"

echo "🔹 Installing Flask-SQLAlchemy in the virtual environment..."
pip install flask_sqlalchemy

echo "Verifying Flask-SQLAlchemy installation..."
python3 -c "import importlib.metadata; print('Flask-SQLAlchemy version:', importlib.metadata.version('flask-sqlalchemy'))"

echo "🔹 Installing Pydantic + Pydantic-AI..."
pip install "pydantic>=2" pydantic-ai openai python-docx odfpy pandas openpyxl pdfminer.six

python3 -c "import pydantic; print('Pydantic version:', pydantic.__version__)"
python3 -c "import pydantic_ai; print('Pydantic-AI imported successfully')"
python3 -c "import openai; print('OpenAI package version:', openai.__version__)"
python3 -c "import docx; print('python-docx package version:', docx.__version__)"
python3 -c "import odf; print('odfpy imported successfully')"
python3 -c "import pandas; print('pandas package version:', pandas.__version__)"
python3 -c "import openpyxl; print('openpyxl package version:', openpyxl.__version__)"
python3 -c "import pdfminer; print('pdfminer.six package version:', pdfminer.__version__)"

echo "Installing Levenshtein for improved string matching..."
pip install python-Levenshtein

echo "🔹 Installing pypdf..."
pip install pypdf

echo "🔹 Installing reportlab..."
pip install reportlab

echo "Verifying reportlab installation..."
python3 -c "import reportlab; print('reportlab imported successfully')"

echo "🔹 Generating redacted_template.pdf..."

python3 <<'EOF'
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4

c = canvas.Canvas("/tmp/redacted_template.pdf", pagesize=A4)
c.setFont("Helvetica", 16)
c.drawCentredString(A4[0] / 2, A4[1] / 2, "redacted by GDPRFS to avoid a privacy law violation")
c.save()
EOF

# Move into place with correct permissions
sudo mkdir -p /var/lib/gdprfs
sudo mv /tmp/redacted_template.pdf /var/lib/gdprfs/redacted_template.pdf
sudo chmod 644 /var/lib/gdprfs/redacted_template.pdf #permission: root: read/write, group: read, others: read
sudo chown root:root /var/lib/gdprfs/redacted_template.pdf
echo "redacted_template.pdf installed."

echo "🔹 Creating /var/lib/gdprfs/.gdprowner (if not already present) ..."
if [ ! -f /var/lib/gdprfs/.gdprowner ]; then
    echo "# GDPR manual PII declaration patterns" | sudo tee /var/lib/gdprfs/.gdprowner > /dev/null
    sudo chmod 600 /var/lib/gdprfs/.gdprowner
    sudo chown root:root /var/lib/gdprfs/.gdprowner
    echo ".gdprowner created at /var/lib/gdprfs/.gdprowner (root-only, API-managed)"
else
    echo ".gdprowner already exists, preserving existing rules"
fi

echo "Setup complete!"
