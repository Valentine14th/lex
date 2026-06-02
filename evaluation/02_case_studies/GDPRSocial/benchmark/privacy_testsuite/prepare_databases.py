#!/usr/bin/env python3
"""
Prepare reproducible database + enforcer-state snapshots for benchmarking.

For the **enforced** app every tweet and consent record must be created
through the Django views so that the enforcement monitor (enfflash)
records the corresponding events.  Snapshots therefore include both the
SQLite database *and* the ``enfflash.state`` file.

Steps per (u, n, consent) combination
--------------------------------------
1. Start from a clean migrated DB with *u* users (inserted via SQL).
2. Boot the enforced Django app (``manage.py runserver --noreload``).
3. For each user, log in and POST *n/u* tweets through ``/post/twit/``.
4. Give consent through ``/gdpr/consent/`` as required by the consent
   level.
5. Gracefully stop the server (SIGINT so the monitor flushes state).
6. Copy ``db.sqlite3`` and ``enfflash.state`` into ``db_snapshots/``.

Run from anywhere:
    python3 benchmark/privacy_testsuite/prepare_databases.py
"""

import os
import json
import shutil
import signal
import sqlite3
import sys
import time
from pathlib import Path
from subprocess import Popen, PIPE, STDOUT
import uuid
import re

import requests
from lorem_text import lorem
from tqdm import tqdm

# ── paths ────────────────────────────────────────────────────────────────
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent  # miniTwitter_gdpr/
SNAPSHOT_DIR = Path(__file__).resolve().parent / "db_snapshots"
TEMPLATE_DB  = SNAPSHOT_DIR / "_template.sqlite3"
MANAGE_PY    = PROJECT_ROOT / "manage.py"
LIVE_DB      = PROJECT_ROOT / "db.sqlite3"
STATE_FILE   = PROJECT_ROOT / "enfflash.state"
STATE_SEED_FILE = PROJECT_ROOT / "enfflash_seed.state"
POLICY_DIR   = PROJECT_ROOT / "policies"

ENFGUARD_EXE = os.environ.get(
    "INSTRLIB_EXE",
    str(Path.home() / "Git" / "whyenf" / "enfguard"),
)

# ── parameter space ─────────────────────────────────────────────────────
CONFIGS        = [(1, 100)]   # (users, tweets) (10, 1000), (100, 10000)
CONSENT_LEVELS = ["none"]#, "statistics", "statistics_ads"]

# ── URLs ─────────────────────────────────────────────────────────────────
BASE           = "http://127.0.0.1:8000"
LOGIN_URL      = f"{BASE}/accounts/login/"
POST_TWEET_URL = f"{BASE}/post/twit/"
CONSENT_URL    = f"{BASE}/gdpr/consent/"

PASSWORD_HASH = (
    "pbkdf2_sha256$12000$iV0sZ7R8KrVJ$"
    "xcIuLw2+ucijlFbCtpRFIy3DxlIANgGjZxJP1pa4kVo="
)

ADS_PER_USER = 2


def _sanitize_name(name):
    """Create filesystem-safe tags for snapshot filenames."""
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", name)


def _policy_formula_candidates():
    """Yield .mfotl policy files selected for snapshot generation.

    If PREPARE_POLICY_DIRS is set (comma-separated), only those entries
    under POLICY_DIR are considered. Each entry may be a subdirectory or
    a direct .mfotl file path. Otherwise, fall back to top-level policies.
    """
    raw = os.environ.get("PREPARE_POLICY_DIRS", "").strip()
    if raw:
        selected = []
        for entry in [x.strip() for x in raw.split(",") if x.strip()]:
            path = Path(entry)
            if not path.is_absolute():
                path = POLICY_DIR / path
            if path.is_dir():
                selected.extend(sorted(path.glob("*.mfotl")))
            elif path.is_file() and path.suffix == ".mfotl":
                selected.append(path)
            else:
                print(f"  [skip] PREPARE_POLICY_DIRS entry not found: {entry}")
        return selected

    return sorted(POLICY_DIR.glob("*.mfotl"))


def _discover_policy_groups():
    """Return [(group_name, formula_arg, sig_arg, [policy_names])].

    - If PREPARE_POLICY_DIRS is set, each directory entry is one group and all
      *.mfotl/*.sig files in it are run together in the same multi-enforcer run.
    - Otherwise, each top-level policy file is treated as a single-policy group.
    """
    groups = []
    raw = os.environ.get("PREPARE_POLICY_DIRS", "").strip()

    if raw:
        for entry in [x.strip() for x in raw.split(",") if x.strip()]:
            path = Path(entry)
            if not path.is_absolute():
                path = POLICY_DIR / path
            if not path.is_dir():
                print(f"  [skip] PREPARE_POLICY_DIRS entry is not a directory: {entry}")
                continue

            mfotls = sorted(path.glob("*.mfotl"))
            if not mfotls:
                print(f"  [skip] No .mfotl files in: {path}")
                continue

            missing = [m.stem for m in mfotls if not m.with_suffix(".sig").exists()]
            if missing:
                print(f"  [skip] Missing .sig files in {path}: {', '.join(missing)}")
                continue

            policy_names = [m.stem for m in mfotls]
            groups.append((path.name, path, path, policy_names))

        if groups:
            return groups

    singles = []
    for formula_path in sorted(POLICY_DIR.glob("*.mfotl")):
        sig_path = formula_path.with_suffix(".sig")
        if sig_path.exists():
            name = formula_path.stem
            singles.append((name, formula_path, sig_path, [name]))
        else:
            print(f"  [skip] Missing .sig for policy '{formula_path.stem}'")

    if singles:
        return singles

    fallback = "minitwit_gdpr"
    print("  [warn] No discoverable policies, using fallback")
    return [(
        fallback,
        POLICY_DIR / f"{fallback}.mfotl",
        POLICY_DIR / f"{fallback}.sig",
        [fallback],
    )]


def _runtime_state_for(policy_name):
    """Mirror twitt.enforcer._state_for for STATE_SEED_FILE base path."""
    base, ext = os.path.splitext(str(STATE_SEED_FILE))
    ext = ext or ".state"
    safe_name = "".join(ch if ch.isalnum() or ch in ("-", "_") else "_" for ch in policy_name)
    return Path(f"{base}__{safe_name}{ext}")


def _random_text():
    t = lorem.paragraph()
    if len(t) > 140:
        t = t[:137] + "..."
    return t


# ─────────────────────────────────────────────────────────────────────────
#  Template: a migrated DB with empty application tables
# ─────────────────────────────────────────────────────────────────────────

def _create_template_db():
    """Copy the existing DB and wipe all application data."""
    if TEMPLATE_DB.exists():
        print(f"  Template already exists: {TEMPLATE_DB.name}")
        return
    SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copy2(LIVE_DB, TEMPLATE_DB)
    db = sqlite3.connect(TEMPLATE_DB)
    cur = db.cursor()
    tables = [r[0] for r in cur.execute(
        "SELECT name FROM sqlite_master WHERE type='table' "
        "AND name NOT LIKE 'sqlite_%' "
        "AND name NOT LIKE 'django_%' "
        "AND name != 'auth_permission' "
        "AND name != 'auth_group'"
    ).fetchall()]
    for t in tables:
        try:
            cur.execute(f"DELETE FROM {t}")
        except Exception:
            pass
    try:
        cur.execute("DELETE FROM sqlite_sequence")
    except Exception:
        pass
    db.commit()
    db.close()
    print(f"  Template created: {TEMPLATE_DB.name}")


# ─────────────────────────────────────────────────────────────────────────
#  Server lifecycle helpers
# ─────────────────────────────────────────────────────────────────────────

def _kill_port():
    from subprocess import run
    run(["fuser", "-k", "8000/tcp"], stdout=PIPE, stderr=PIPE)
    time.sleep(0.5)


def _start_server(policy_formula, policy_sig, policy_names):
    """Start the enforced Django dev server, return (proc, log_fh)."""
    _kill_port()

    env = os.environ.copy()
    env["INSTRLIB_EXE"] = ENFGUARD_EXE
    env["INSTRLIB_FORMULA"] = str(policy_formula)
    env["INSTRLIB_SIG"] = str(policy_sig)

    multi_mode = len(policy_names) > 1
    if multi_mode:
        # Reset common seed for multi-enforcer cloning for each snapshot run.
        if STATE_FILE.exists():
            shutil.copy2(STATE_FILE, STATE_SEED_FILE)
        else:
            STATE_SEED_FILE.write_bytes(b"")
        env["INSTRLIB_STATE"] = str(STATE_SEED_FILE)

        # Remove stale per-enforcer states from previous runs.
        for policy_name in policy_names:
            runtime_state = _runtime_state_for(policy_name)
            if runtime_state.exists():
                runtime_state.unlink()
    else:
        # MultiPDP may still be active with a single formula and expects a
        # valid source state file to clone from.
        if STATE_FILE.exists():
            env["INSTRLIB_STATE"] = str(STATE_FILE)
        elif STATE_SEED_FILE.exists():
            env["INSTRLIB_STATE"] = str(STATE_SEED_FILE)
        else:
            raise RuntimeError(
                f"Missing baseline state file: {STATE_FILE}"
            )

    log_fh = open(SNAPSHOT_DIR / "_server.log", "w")
    proc = Popen(
        ["python3", str(MANAGE_PY), "runserver", "--noreload"],
        stdin=PIPE, stdout=log_fh, stderr=STDOUT, text=True,
        cwd=str(PROJECT_ROOT), env=env,
    )
    # Wait until the server is ready
    for _ in range(30):
        time.sleep(1)
        try:
            r = requests.get(LOGIN_URL, timeout=2)
            if r.status_code == 200:
                return proc, log_fh
        except requests.RequestException:
            pass
    raise RuntimeError("Django server did not start within 30 s")


def _stop_server(proc, log_fh):
    """Stop the server so that enfflash saves its state file.

    We find the enfflash child process, send it SIGTERM so it saves its
    state file, poll until it exits, and only then terminate Django.
    """
    import psutil
    try:
        parent = psutil.Process(proc.pid)
        children = parent.children(recursive=True)
        enfguard_procs = [c for c in children
                          if any(x in c.name() for x in ("enfguard", "enfflash"))
                          or any(x in " ".join(c.cmdline()) for x in ("enfguard", "enfflash"))]
        for ep in enfguard_procs:
            os.kill(ep.pid, signal.SIGINT)   # SIGINT triggers state save
        # Poll until enfflash exits (can't waitpid on grandchild)
        for _ in range(30):
            time.sleep(0.5)
            if all(not ep.is_running() for ep in enfguard_procs):
                break
    except (psutil.NoSuchProcess, psutil.AccessDenied, ProcessLookupError):
        pass

    # Now kill Django
    proc.terminate()
    try:
        proc.wait(timeout=10)
    except Exception:
        proc.kill()
        proc.wait()
    time.sleep(1)
    log_fh.close()
    _kill_port()


# ─────────────────────────────────────────────────────────────────────────
#  HTTP helpers
# ─────────────────────────────────────────────────────────────────────────

def _login(username):
    s = requests.Session()
    s.get(LOGIN_URL)
    csrf = s.cookies["csrftoken"]
    r = s.post(LOGIN_URL, data={
        "username": username,
        "password": "password",
        "csrfmiddlewaretoken": csrf,
    })
    assert r.ok, f"Login failed for {username}: {r.status_code}"
    return s


def _post_tweet(session, text):
    csrf = session.cookies["csrftoken"]
    r = session.post(POST_TWEET_URL, data={
        "content": text,
        "twit_uid": str(uuid.uuid4()),
        "csrfmiddlewaretoken": csrf,
    }, allow_redirects=False)
    assert r.status_code == 302, f"post_tweet failed: {r.status_code}"


def _give_consent(session, purpose):
    csrf = session.cookies["csrftoken"]
    r = session.post(CONSENT_URL, data={
        "give_consent": purpose,
        "csrfmiddlewaretoken": csrf,
    }, allow_redirects=False)
    assert r.status_code == 302, f"give_consent({purpose}) failed: {r.status_code}"


# ─────────────────────────────────────────────────────────────────────────
#  Seed users via SQL (before starting the server)
# ─────────────────────────────────────────────────────────────────────────

def _seed_users(db_path, u):
    db = sqlite3.connect(db_path)
    cur = db.cursor()
    for i in range(u):
        cur.execute(
            "INSERT INTO twitt_user "
            "(username, email, password, is_superuser, is_staff, "
            " first_name, last_name, is_active, date_joined) "
            "VALUES (?,?,?,?,?,?,?,?,?)",
            (f"user{i}", f"user{i}@example.com", PASSWORD_HASH,
             0, 0, f"First{i}", f"Last{i}", 1,
             "2023-01-01 00:00:00.000000"),
        )
    db.commit()
    db.close()


def _seed_ads(db_path, u, ads_per_user=ADS_PER_USER):
    """Seed simple active ads for recommendation and impression flows."""
    db = sqlite3.connect(db_path)
    cur = db.cursor()

    ad_count = max(1, u * ads_per_user)
    for i in range(ad_count):
        created_by_id = (i % u) + 1
        title = f"Sponsored post #{i + 1}"
        body = lorem.sentence()
        url = f"https://example.com/ad/{i + 1}"
        embedding = json.dumps([])
        cur.execute(
            "INSERT INTO twitt_ad "
            "(title, body, url, embedding, is_active, created_by_id, created_at) "
            "VALUES (?,?,?,?,?,?,?)",
            (
                title,
                body,
                url,
                embedding,
                1,
                created_by_id,
                "2023-01-01 00:00:00.000000",
            ),
        )

    db.commit()
    db.close()


# ─────────────────────────────────────────────────────────────────────────
#  Build one snapshot
# ─────────────────────────────────────────────────────────────────────────

def build_snapshot(u, n, consent, group_name, policy_formula, policy_sig, policy_names):
    group_tag = _sanitize_name(group_name)
    base_tag = f"u{u}_n{n}_c{consent}"
    db_dest = SNAPSHOT_DIR / f"db_{base_tag}.sqlite3"
    state_dests = [
        SNAPSHOT_DIR / f"state_p{_sanitize_name(policy_name)}_{base_tag}.bin"
        for policy_name in policy_names
    ]

    if db_dest.exists() and all(p.exists() for p in state_dests):
        print(f"  [skip] {group_tag}_{base_tag} already exists")
        return

    print(
        f"  [{group_tag}_{base_tag}] Preparing ({u} users, {n} tweets, consent={consent}, "
        f"group={group_name}, policies={len(policy_names)}) ..."
    )

    # 1. Fresh DB with users
    shutil.copy2(TEMPLATE_DB, LIVE_DB)
    _seed_users(LIVE_DB, u)
    _seed_ads(LIVE_DB, u)

    # 2. Start enforced server
    proc, log_fh = _start_server(policy_formula, policy_sig, policy_names)

    try:
        tweets_per_user = n // u
        extra = n % u

        # 4. Give consent
        if consent in ("statistics", "statistics_ads"):
            for i in tqdm(range(u)):
                session = _login(f"user{i}")
                _give_consent(session, "statistics")
            print(f"    Consent 'statistics' given for {u} users")

        if consent == "statistics_ads":
            for i in tqdm(range(u)):
                session = _login(f"user{i}")
                _give_consent(session, "personalized_ad")
            print(f"    Consent 'personalized_ad' given for {u} users")


        # 3. Log in as each user, post tweets
        for i in tqdm(range(u)):
            count = tweets_per_user + (1 if i < extra else 0)
            session = _login(f"user{i}")
            for j in tqdm(range(count)):
                _post_tweet(session, _random_text())
            if (i + 1) % max(1, u // 10) == 0 or i == u - 1:
                print(f"    user{i}: {count} tweets posted")

    finally:
        # 5. Graceful shutdown → monitor flushes enfflash.state
        _stop_server(proc, log_fh)

    # 6. Save snapshot DB + per-enforcer state files
    assert LIVE_DB.exists(), "DB not found after server stop"
    shutil.copy2(LIVE_DB, db_dest)

    if len(policy_names) > 1:
        for policy_name, state_dest in zip(policy_names, state_dests):
            runtime_state = _runtime_state_for(policy_name)
            assert runtime_state.exists(), f"State file not found after server stop: {runtime_state}"
            shutil.copy2(runtime_state, state_dest)
    else:
        runtime_state = _runtime_state_for(policy_names[0])
        if runtime_state.exists():
            shutil.copy2(runtime_state, state_dests[0])
        else:
            assert STATE_FILE.exists(), "enfflash.state not found after server stop"
            shutil.copy2(STATE_FILE, state_dests[0])

    print(f"  [{group_tag}_{base_tag}] Done ✓")


# ─────────────────────────────────────────────────────────────────────────
#  Main
# ─────────────────────────────────────────────────────────────────────────

def main():
    SNAPSHOT_DIR.mkdir(parents=True, exist_ok=True)
    print("Creating template database …")
    _create_template_db()

    policy_groups = _discover_policy_groups()
    print(f"Discovered {len(policy_groups)} policy group(s)")

    combos = [
        (group_name, policy_formula, policy_sig, policy_names, u, n, c)
        for (group_name, policy_formula, policy_sig, policy_names) in policy_groups
        for (u, n) in CONFIGS
        for c in CONSENT_LEVELS
    ]
    print(f"\nBuilding {len(combos)} snapshots (this will take a while) …\n")
    for group_name, policy_formula, policy_sig, policy_names, u, n, consent in combos:
        build_snapshot(u, n, consent, group_name, policy_formula, policy_sig, policy_names)

    print(f"\nAll snapshots ready in {SNAPSHOT_DIR}/")


if __name__ == "__main__":
    main()
