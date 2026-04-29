"""
Preload N files into GDPRFS for scalability benchmarking.

Creates N files distributed evenly across the 5 registered data subjects
(alice_a, bob_b, charlie_c, dave_d, eve_e) by writing them through the FUSE
mount with the LLM analyzer disabled, then waits until every file has a DB
row.  Ownership is resolved automatically via filename matching (tier 3):
e.g. "bob_b_scale_00042.txt" matches Person uid=bob_b.

Usage
-----
    python3 -m benchmark.preload_files --n 100
    python3 -m benchmark.preload_files --n 1000
    python3 -m benchmark.preload_files --n 10000
    python3 -m benchmark.preload_files --n 1000 --clean   # wipe scale files first

Can also be imported and called programmatically:
    from benchmark.preload_files import preload, clean_scale_files
"""

import argparse
import os
import sqlite3
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

import requests

BASE_DIR = Path(__file__).resolve().parent.parent
FUSE_MOUNT = Path("/tmp/mnt")
UPPER_DIR = Path("/var/lib/gdprfs/upper")
GDPRFS_DB = BASE_DIR / "gdprfs.db"
CONSENT_DB = (
    BASE_DIR / "external_consent_platform" / "instance" / "external_consent_platform.db"
)

INGEST_URL = "http://127.0.0.1:7000/ingest"
LLM_ANALYZER_URL = "http://127.0.0.1:5005"
CONSENT_PLATFORM_URL = "http://127.0.0.1:5000"

# All 5 registered data subjects
ALL_DS = [
    ("alice_a", "Alice", "A"),
    ("bob_b",   "Bob",   "B"),
    ("charlie_c", "Charlie", "C"),
    ("dave_d",  "Dave",  "D"),
    ("eve_e",   "Eve",   "E"),
]

SCALE_PREFIX = "scale_"    # files look like: bob_b_scale_00042.txt
PURPOSE = "marketing"
CONTROLLER_UID = "alice_a"
REASON = "direct_marketing"
CONTENT_TEMPLATE = b"Preloaded scale test file for {uid} index {idx:06d}.\n"
BATCH_SIZE = 50            # write in batches, waiting for DB after each


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _reachable(url: str) -> bool:
    try:
        requests.get(url, timeout=2)
        return True
    except Exception:
        return False


def _ingest(kind: str, **kwargs):
    resp = requests.post(INGEST_URL, json={"kind": kind, **kwargs}, timeout=15)
    resp.raise_for_status()
    return resp.json() if resp.text else {}


def _disable_llm():
    if _reachable(LLM_ANALYZER_URL):
        requests.post(f"{LLM_ANALYZER_URL}/disable", timeout=5)
        print("[PRELOAD] LLM analyzer disabled.")
    else:
        print("[PRELOAD] LLM analyzer not reachable — skipping disable (already off or not running).")


def _enable_llm():
    if _reachable(LLM_ANALYZER_URL):
        requests.post(f"{LLM_ANALYZER_URL}/enable", timeout=5)
        print("[PRELOAD] LLM analyzer re-enabled.")


def _ensure_persons_in_gdprfs_db():
    """
    Sync the 5 DS from the external consent platform DB into the GDPRFS DB
    (person table), so filename-based mapping can link files to them.
    """
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    conn = sqlite3.connect(str(GDPRFS_DB), timeout=10)
    cur = conn.cursor()
    for uid, first, last in ALL_DS:
        row = cur.execute("SELECT id FROM person WHERE uid=?", (uid,)).fetchone()
        if not row:
            cur.execute(
                "INSERT INTO person (uid, first_name, last_name, registered) VALUES (?,?,?,1)",
                (uid, first, last),
            )
            print(f"[PRELOAD] Inserted person: {uid}")
    conn.commit()
    conn.close()


def _grant_consent_all():
    """Grant marketing consent for every DS, both in enforcer and consent DB."""
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    consent_conn = sqlite3.connect(str(CONSENT_DB), timeout=10)
    c_cur = consent_conn.cursor()

    for uid, _, _ in ALL_DS:
        try:
            _ingest("Consent", uid=uid, purpose=PURPOSE)
        except Exception as e:
            print(f"[PRELOAD] Warning: ingest Consent for {uid} failed: {e}")

        # Upsert in consent DB
        row = c_cur.execute(
            "SELECT current_state_id FROM current_event_state WHERE uid=? AND purpose=? AND category='consent'",
            (uid, PURPOSE),
        ).fetchone()
        if row:
            c_cur.execute(
                "UPDATE current_event_state SET status='consented', updated_at=? WHERE current_state_id=?",
                (now, row[0]),
            )
        else:
            c_cur.execute(
                "INSERT INTO current_event_state (uid, purpose, category, status, updated_at) VALUES (?,?,?,?,?)",
                (uid, PURPOSE, "consent", "consented", now),
            )

    consent_conn.commit()
    consent_conn.close()
    print("[PRELOAD] Consent granted for all DS.")


def _scale_filenames(n: int) -> list[tuple[str, str]]:
    """
    Return list of (uid, filename) for n files, round-robin across DS.
    Each filename contains the uid so tier-3 filename matching fires.
    """
    pairs = []
    ds = [uid for uid, _, _ in ALL_DS]
    for i in range(n):
        uid = ds[i % len(ds)]
        fname = f"{uid}_{SCALE_PREFIX}{i:06d}.txt"
        pairs.append((uid, fname))
    return pairs


def _wait_for_rows(filenames: list[str], timeout: float = 120.0, poll: float = 0.5):
    """Block until all filenames have a row in the file table."""
    deadline = time.monotonic() + timeout
    remaining = set(filenames)
    while remaining and time.monotonic() < deadline:
        conn = sqlite3.connect(str(GDPRFS_DB), timeout=5)
        cur = conn.cursor()
        found = {
            row[0]
            for row in cur.execute(
                f"SELECT file_id FROM file WHERE file_id IN ({','.join('?' * len(remaining))})",
                list(remaining),
            ).fetchall()
        }
        conn.close()
        remaining -= found
        if remaining:
            time.sleep(poll)
    if remaining:
        print(f"[PRELOAD] Warning: {len(remaining)} files never appeared in DB within {timeout}s.")
    return len(remaining) == 0


def _count_scale_files_in_db() -> int:
    if not GDPRFS_DB.exists():
        return 0
    conn = sqlite3.connect(str(GDPRFS_DB), timeout=5)
    count = conn.execute(
        "SELECT COUNT(*) FROM file WHERE file_id LIKE ?", (f"%_{SCALE_PREFIX}%",)
    ).fetchone()[0]
    conn.close()
    return count


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def clean_scale_files(verbose: bool = True):
    """Remove all scale test files from FUSE mount, upper/mirror dirs and DB."""
    removed_fs = 0
    for p in FUSE_MOUNT.glob(f"*_{SCALE_PREFIX}*.txt"):
        try:
            p.unlink()
            removed_fs += 1
        except OSError:
            pass
    # Also sweep upper and mirror directly (in case FUSE is not mounted)
    for base in (UPPER_DIR, Path("/var/lib/gdprfs/mirror")):
        for p in base.glob(f"*_{SCALE_PREFIX}*.txt"):
            try:
                p.unlink(missing_ok=True)
            except OSError:
                pass

    if GDPRFS_DB.exists():
        conn = sqlite3.connect(str(GDPRFS_DB), timeout=10)
        cur = conn.cursor()
        rows = cur.execute(
            "SELECT id, file_id FROM file WHERE file_id LIKE ?", (f"%_{SCALE_PREFIX}%",)
        ).fetchall()
        for pk, fid in rows:
            cur.execute("DELETE FROM person_file_map WHERE file_id=?", (pk,))
            cur.execute("DELETE FROM person_file_special_category WHERE file_id=?", (pk,))
            cur.execute("DELETE FROM file WHERE id=?", (pk,))
        conn.commit()
        conn.close()
        if verbose:
            print(f"[PRELOAD] Cleaned {len(rows)} scale-file DB entries and {removed_fs} FS files.")
    elif verbose:
        print(f"[PRELOAD] Cleaned {removed_fs} FS files (DB not found).")


def preload(n: int, clean_first: bool = False, re_enable_llm: bool = False) -> int:
    """
    Preload `n` scale-test files into GDPRFS.

    Parameters
    ----------
    n               : number of files to preload
    clean_first     : remove existing scale files before preloading
    re_enable_llm   : re-enable LLM analyzer after preloading (default: leave disabled)

    Returns the number of files successfully registered in the DB.
    """
    # --- Preflight ---
    if not _reachable(INGEST_URL.replace("/ingest", "")):
        print("[PRELOAD] ERROR: FUSE ingest server not reachable at port 7000.", file=sys.stderr)
        sys.exit(1)
    if not FUSE_MOUNT.is_mount():
        print("[PRELOAD] ERROR: FUSE filesystem not mounted at /tmp/mnt.", file=sys.stderr)
        sys.exit(1)

    if clean_first:
        print("[PRELOAD] Cleaning existing scale files...")
        clean_scale_files()

    existing = _count_scale_files_in_db()
    if existing >= n:
        print(f"[PRELOAD] {existing} scale files already in DB (requested {n}). Nothing to do.")
        return existing

    to_create = n - existing
    print(f"[PRELOAD] {existing} scale files already in DB; creating {to_create} more (target: {n})")

    # --- Setup ---
    _disable_llm()
    _ensure_persons_in_gdprfs_db()
    _grant_consent_all()

    print(f"[PRELOAD] Starting session as {CONTROLLER_UID}...")
    _ingest("StartSession", uid=CONTROLLER_UID, purpose=PURPOSE, reason=REASON)

    # Determine which filenames are still missing
    all_pairs = _scale_filenames(n)
    if GDPRFS_DB.exists():
        conn = sqlite3.connect(str(GDPRFS_DB), timeout=5)
        existing_ids = {
            r[0]
            for r in conn.execute(
                "SELECT file_id FROM file WHERE file_id LIKE ?", (f"%_{SCALE_PREFIX}%",)
            ).fetchall()
        }
        conn.close()
    else:
        existing_ids = set()

    missing_pairs = [(uid, fname) for uid, fname in all_pairs if fname not in existing_ids]
    print(f"[PRELOAD] Writing {len(missing_pairs)} files in batches of {BATCH_SIZE}...")

    t_start = time.monotonic()
    written_filenames: list[str] = []
    batch_filenames: list[str] = []

    for i, (uid, fname) in enumerate(missing_pairs):
        dest = FUSE_MOUNT / fname
        content = CONTENT_TEMPLATE.replace(b"{uid}", uid.encode()).replace(
            b"{idx:06d}", f"{i:06d}".encode()
        )
        try:
            dest.write_bytes(content)
            written_filenames.append(fname)
            batch_filenames.append(fname)
        except OSError as e:
            print(f"[PRELOAD] Warning: could not write {fname}: {e}")

        # After each batch, wait for DB rows so we don't flood FUSE
        if len(batch_filenames) >= BATCH_SIZE or i == len(missing_pairs) - 1:
            _wait_for_rows(batch_filenames, timeout=60.0)
            done = existing + len(written_filenames)
            elapsed = time.monotonic() - t_start
            rate = len(written_filenames) / elapsed if elapsed > 0 else 0
            print(
                f"  {done}/{n} files registered  "
                f"({len(written_filenames)} new, {elapsed:.1f}s, {rate:.1f} files/s)",
                end="\r",
            )
            batch_filenames.clear()

    print()  # newline after \r progress

    # --- Teardown ---
    try:
        _ingest("StopSession", uid=CONTROLLER_UID)
    except Exception:
        pass

    if re_enable_llm:
        _enable_llm()

    final_count = _count_scale_files_in_db()
    elapsed = time.monotonic() - t_start
    print(
        f"[PRELOAD] Done. {final_count}/{n} scale files in DB "
        f"({elapsed:.1f}s total, {len(written_filenames)/elapsed:.1f} files/s)."
    )
    return final_count


# ---------------------------------------------------------------------------
# CLI entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Preload N scale-test files into GDPRFS for scalability benchmarking."
    )
    parser.add_argument(
        "--n",
        type=int,
        required=True,
        choices=[100, 1000, 10000],
        metavar="{100,1000,10000}",
        help="Number of files to preload.",
    )
    parser.add_argument(
        "--clean",
        action="store_true",
        help="Remove existing scale files before preloading.",
    )
    parser.add_argument(
        "--clean-only",
        action="store_true",
        help="Only remove scale files, do not preload.",
    )
    parser.add_argument(
        "--re-enable-llm",
        action="store_true",
        help="Re-enable the LLM analyzer after preloading (default: leave it disabled).",
    )
    args = parser.parse_args()

    if args.clean_only:
        clean_scale_files(verbose=True)
        return

    preload(args.n, clean_first=args.clean, re_enable_llm=args.re_enable_llm)


if __name__ == "__main__":
    main()
