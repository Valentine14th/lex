"""
Benchmark: Basic Operation Latencies

Measures the following primitive operations across three setups:
- read a file
- write a file
- give consent
- remove consent
- request erasure
- request rectification

Setups:
- baseline: local filesystem + local synthetic consent store
- gdpr_no_llm: GDPRFS/FUSE with LLM analyzer disabled
- gdpr_with_llm: GDPRFS/FUSE with LLM analyzer enabled
"""

import argparse
import base64
import csv
import os
import sqlite3
import statistics
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

import requests

BASE_DIR = Path(__file__).resolve().parent.parent
RESULTS_DIR = BASE_DIR / "benchmark" / "results"
GENERATED_DIR = BASE_DIR / "benchmark" / "generated" / "simple"

FUSE_MOUNT = Path("/tmp/mnt")
UPPER_DIR = Path("/var/lib/gdprfs/upper")
MIRROR_DIR = Path("/var/lib/gdprfs/mirror")

INGEST_URL = "http://127.0.0.1:7000/ingest"
UPLOAD_URL = "http://127.0.0.1:7000/upload_rectification"
CONSENT_PLATFORM_URL = "http://127.0.0.1:5000"
LLM_ANALYZER_URL = "http://127.0.0.1:5005"

CONSENT_DB = BASE_DIR / "external_consent_platform" / "instance" / "external_consent_platform.db"
GDPRFS_DB = BASE_DIR / "gdprfs.db"

MODE_BASELINE = "baseline"
MODE_GDPR_NO_LLM = "gdpr_no_llm"
MODE_GDPR_WITH_LLM = "gdpr_with_llm"
ALL_MODES = [MODE_BASELINE, MODE_GDPR_NO_LLM, MODE_GDPR_WITH_LLM]

DS_UID = "bob_b"
CONTROLLER_UID = "alice_a"
PURPOSE = "marketing"
REASON = "direct_marketing"
TEST_FILENAME = "bob_b_simple.txt"
RECTIFIED_FILENAME = "bob_b_simple_rectified.txt"
INITIAL_CONTENT = b"Bob B simple benchmark original content.\n"
UPDATED_CONTENT = b"Bob B simple benchmark updated content.\n"
RECTIFIED_CONTENT = b"Bob B rectified benchmark content.\n"

OPERATIONS = [
    "t_read_file",
    "t_write_file",
    "t_give_consent",
    "t_remove_consent",
    "t_request_erasure",
    "t_request_rectification",
    "t_total",
]

DEFAULT_WAIT_TIMEOUT = 15.0
LLM_WAIT_TIMEOUT = 20.0


def fuse_ingest(kind: str, timeout: float = 15, **kwargs) -> dict:
    payload = {"kind": kind, **kwargs}
    response = requests.post(INGEST_URL, json=payload, timeout=timeout)
    response.raise_for_status()
    return response.json() if response.text else {}



def update_consent_db(uid: str, purpose: str, status: str):
    conn = sqlite3.connect(str(CONSENT_DB))
    cur = conn.cursor()
    row = cur.execute(
        "SELECT current_state_id FROM current_event_state "
        "WHERE uid=? AND purpose=? AND category='consent'",
        (uid, purpose),
    ).fetchone()
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    if row:
        cur.execute(
            "UPDATE current_event_state SET status=?, updated_at=? "
            "WHERE current_state_id=?",
            (status, now, row[0]),
        )
    else:
        cur.execute(
            "INSERT INTO current_event_state "
            "(uid, purpose, category, status, updated_at) "
            "VALUES (?, ?, 'consent', ?, ?)",
            (uid, purpose, status, now),
        )
    conn.commit()
    conn.close()



def remove_consent_rows(uid: str, purpose: str):
    if not CONSENT_DB.exists():
        return
    conn = sqlite3.connect(str(CONSENT_DB))
    cur = conn.cursor()
    cur.execute(
        "DELETE FROM current_event_state WHERE uid=? AND purpose=? AND category='consent'",
        (uid, purpose),
    )
    conn.commit()
    conn.close()



def upload_rectification_file(filename: str, content: bytes, timeout: float = 15) -> str:
    payload = {
        "filename": filename,
        "content_b64": base64.b64encode(content).decode("ascii"),
    }
    response = requests.post(UPLOAD_URL, json=payload, timeout=timeout)
    response.raise_for_status()
    data = response.json()
    if not data.get("ok"):
        raise RuntimeError(f"upload_rectification failed: {data}")
    return data["fid_new"]



def _is_fuse_mounted() -> bool:
    try:
        with open("/proc/mounts", encoding="utf-8") as handle:
            return any("/tmp/mnt" in line for line in handle)
    except FileNotFoundError:
        return False



def _is_reachable(url: str) -> bool:
    try:
        requests.get(url, timeout=2)
        return True
    except Exception:
        return False



def configure_llm(mode: str):
    if mode == MODE_GDPR_NO_LLM and _is_reachable(LLM_ANALYZER_URL):
        requests.post(f"{LLM_ANALYZER_URL}/disable", timeout=5)
    elif mode == MODE_GDPR_WITH_LLM:
        if not _is_reachable(LLM_ANALYZER_URL):
            raise RuntimeError("LLM analyzer not reachable (port 5005)")
        requests.post(f"{LLM_ANALYZER_URL}/enable", timeout=5)



def preflight_checks(mode: str):
    if mode == MODE_BASELINE:
        return

    if not _is_fuse_mounted():
        raise RuntimeError("FUSE filesystem not mounted at /tmp/mnt")
    if not _is_reachable(CONSENT_PLATFORM_URL):
        raise RuntimeError("External consent platform not reachable (port 5000)")
    if not CONSENT_DB.exists():
        raise RuntimeError(f"Consent DB not found: {CONSENT_DB}")

    configure_llm(mode)



def start_session():
    fuse_ingest("StartSession", uid=CONTROLLER_UID, purpose=PURPOSE, reason=REASON)



def stop_session():
    try:
        fuse_ingest("StopSession", uid=CONTROLLER_UID)
    except Exception:
        pass



def _grant_consent():
    fuse_ingest("Consent", uid=DS_UID, purpose=PURPOSE)
    update_consent_db(DS_UID, PURPOSE, "consented")



def _revoke_consent():
    fuse_ingest("Revoke", uid=DS_UID, purpose=PURPOSE)
    update_consent_db(DS_UID, PURPOSE, "revoked")



def _write_via_temp_rename(target: Path, content: bytes):
    tmp_name = target.parent / ".goutputstream-simple"
    tmp_name.write_bytes(content)
    if target.exists():
        os.unlink(str(target))
    os.rename(str(tmp_name), str(target))



def _wait_for_file_row(file_id: str, timeout: float = DEFAULT_WAIT_TIMEOUT, poll_interval: float = 0.25):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if GDPRFS_DB.exists():
            conn = sqlite3.connect(str(GDPRFS_DB))
            cur = conn.cursor()
            row = cur.execute("SELECT id FROM file WHERE file_id=?", (file_id,)).fetchone()
            conn.close()
            if row:
                return
        time.sleep(poll_interval)
    raise TimeoutError(f"Timed out waiting for file row for {file_id}")



def _ensure_file_row_and_owner_link(file_id: str, abs_path: Path):
    """Best-effort fallback if FUSE DB mapping is delayed.
    Ensures a File row exists and links it to DS_UID so benchmark flows can proceed."""
    if not GDPRFS_DB.exists():
        return

    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    for _ in range(12):
        conn = None
        try:
            conn = sqlite3.connect(str(GDPRFS_DB), timeout=5)
            cur = conn.cursor()

            row = cur.execute("SELECT id FROM file WHERE file_id=?", (file_id,)).fetchone()
            if row:
                file_pk = row[0]
            else:
                cur.execute(
                    "INSERT INTO file (file_id, abs_path, created_at, modified_at, accessed_at, last_action, special_categories) "
                    "VALUES (?, ?, ?, ?, ?, ?, '')",
                    (file_id, str(abs_path), now, now, now, "write"),
                )
                file_pk = cur.lastrowid

            person_row = cur.execute("SELECT id FROM person WHERE uid=?", (DS_UID,)).fetchone()
            if person_row:
                person_pk = person_row[0]
                cur.execute(
                    "INSERT OR IGNORE INTO person_file_map (person_id, file_id) VALUES (?, ?)",
                    (person_pk, file_pk),
                )

            conn.commit()
            return
        except sqlite3.OperationalError:
            time.sleep(0.25)
        finally:
            if conn is not None:
                conn.close()



def _wait_for_content(path: Path, expected: bytes, timeout: float = DEFAULT_WAIT_TIMEOUT, poll_interval: float = 0.25):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        try:
            if path.exists() and expected.strip() in path.read_bytes():
                return
        except OSError:
            pass
        time.sleep(poll_interval)
    raise TimeoutError(f"Timed out waiting for rectified content in {path}")



def _wait_for_deletion(path: Path, timeout: float = DEFAULT_WAIT_TIMEOUT, poll_interval: float = 0.25):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if not path.exists():
            return
        time.sleep(poll_interval)
    raise TimeoutError(f"Timed out waiting for deletion of {path}")



def cleanup_gdpr_state():
    stop_session()

    for path in (FUSE_MOUNT / TEST_FILENAME, FUSE_MOUNT / ".goutputstream-simple"):
        try:
            if path.exists():
                path.unlink()
        except OSError:
            pass

    if GDPRFS_DB.exists():
        conn = sqlite3.connect(str(GDPRFS_DB))
        cur = conn.cursor()
        row = cur.execute("SELECT id FROM file WHERE file_id=?", (TEST_FILENAME,)).fetchone()
        if row:
            file_pk = row[0]
            cur.execute("DELETE FROM person_file_map WHERE file_id=?", (file_pk,))
            cur.execute("DELETE FROM person_file_special_category WHERE file_id=?", (file_pk,))
            cur.execute("DELETE FROM file WHERE id=?", (file_pk,))
        cur.execute("DELETE FROM person WHERE registered=0")
        conn.commit()
        conn.close()

    remove_consent_rows(DS_UID, PURPOSE)



def prepare_consented_file(content: bytes = INITIAL_CONTENT, wait_timeout: float = DEFAULT_WAIT_TIMEOUT):
    target = FUSE_MOUNT / TEST_FILENAME
    upper_target = UPPER_DIR / TEST_FILENAME

    for attempt in range(5):
        # Full reset every attempt: flushes FUSE dentry/inode state, DB rows,
        # and consent entries so write_bytes() always starts from a clean slate.
        cleanup_gdpr_state()
        # Brief settle: give FUSE time to finish processing the preceding unlink()
        # so the dentry cache is coherent before the next write_bytes().
        time.sleep(2)
        start_session()
        _grant_consent()

        try:
            target.write_bytes(content)
        except OSError as exc:
            # ENOSYS can occur when the kernel VFS inode was invalidated by the
            # enforcer's async _do_delete_file() and FUSE can't process the op.
            # Loop back so cleanup_gdpr_state() flushes the stale inode.
            print(f"  [prepare] write_bytes failed ({exc}), retrying (attempt {attempt + 1}) …")
            continue

        try:
            _wait_for_file_row(TEST_FILENAME, timeout=wait_timeout)
        except TimeoutError:
            # Fallback for occasional DB mapping races/locks under gdpr_with_llm.
            _ensure_file_row_and_owner_link(TEST_FILENAME, target.resolve())
            _wait_for_file_row(TEST_FILENAME, timeout=5)

        # Stability check: give the enforcer's proactive-causation thread a moment
        # to fire any pending Delete caused by accumulated Revoke/RequestErasure
        # history from previous iterations.
        time.sleep(0.8)
        if upper_target.exists():
            return target

        print(f"  [prepare] file deleted by enforcer after write (attempt {attempt + 1}), retrying …")

    raise RuntimeError(f"prepare_consented_file: {TEST_FILENAME} unavailable after 5 attempts")




def init_baseline_consent_db(db_path: Path):
    conn = sqlite3.connect(str(db_path))
    cur = conn.cursor()
    cur.execute(
        "CREATE TABLE IF NOT EXISTS consent_state (uid TEXT, purpose TEXT, status TEXT, updated_at TEXT)"
    )
    conn.commit()
    conn.close()



def baseline_upsert_consent(db_path: Path, status: str):
    conn = sqlite3.connect(str(db_path))
    cur = conn.cursor()
    cur.execute("DELETE FROM consent_state WHERE uid=? AND purpose=?", (DS_UID, PURPOSE))
    cur.execute(
        "INSERT INTO consent_state (uid, purpose, status, updated_at) VALUES (?, ?, ?, ?)",
        (DS_UID, PURPOSE, status, datetime.now(timezone.utc).isoformat()),
    )
    conn.commit()
    conn.close()



class BaselineRunner:
    def run_iteration(self) -> dict:
        results = {}
        t0 = time.perf_counter()

        with tempfile.TemporaryDirectory(prefix="simple_baseline_") as tmpdir:
            tmpdir_path = Path(tmpdir)
            consent_db = tmpdir_path / "consent.db"
            init_baseline_consent_db(consent_db)
            file_path = tmpdir_path / TEST_FILENAME
            file_path.write_bytes(INITIAL_CONTENT)

            t1 = time.perf_counter()
            with open(file_path, "rb") as handle:
                handle.read()
            results["t_read_file"] = time.perf_counter() - t1

            t2 = time.perf_counter()
            with open(file_path, "wb") as handle:
                handle.write(UPDATED_CONTENT)
            results["t_write_file"] = time.perf_counter() - t2

            t3 = time.perf_counter()
            baseline_upsert_consent(consent_db, "consented")
            results["t_give_consent"] = time.perf_counter() - t3

            t4 = time.perf_counter()
            baseline_upsert_consent(consent_db, "revoked")
            results["t_remove_consent"] = time.perf_counter() - t4

            t5 = time.perf_counter()
            os.unlink(file_path)
            results["t_request_erasure"] = time.perf_counter() - t5

            rectified_path = tmpdir_path / TEST_FILENAME
            rectified_path.write_bytes(INITIAL_CONTENT)
            t6 = time.perf_counter()
            with open(rectified_path, "wb") as handle:
                handle.write(RECTIFIED_CONTENT)
            results["t_request_rectification"] = time.perf_counter() - t6

        results["t_total"] = time.perf_counter() - t0
        return results



class GDPRRunner:
    def __init__(self, mode: str):
        self.mode = mode

    def _wait_timeout(self) -> float:
        if self.mode == MODE_GDPR_WITH_LLM:
            return LLM_WAIT_TIMEOUT
        return DEFAULT_WAIT_TIMEOUT

    def measure_give_consent(self) -> float:
        cleanup_gdpr_state()
        start = time.perf_counter()
        _grant_consent()
        return time.perf_counter() - start

    def measure_remove_consent(self) -> float:
        cleanup_gdpr_state()
        _grant_consent()
        start = time.perf_counter()
        _revoke_consent()
        return time.perf_counter() - start

    def measure_read_file(self) -> float:
        for _attempt in range(3):
            target = prepare_consented_file(INITIAL_CONTENT, wait_timeout=self._wait_timeout())
            try:
                start = time.perf_counter()
                with open(target, "rb") as handle:
                    handle.read()
                return time.perf_counter() - start
            except FileNotFoundError:
                # Enforcer deleted the file between prepare and open — retry.
                print(f"  [read] ENOENT after prepare (attempt {_attempt + 1}), retrying …")
                cleanup_gdpr_state()
                time.sleep(1.0)
            finally:
                cleanup_gdpr_state()
        raise RuntimeError("measure_read_file: file unavailable after 3 attempts")

    def measure_write_file(self) -> float:
        target = prepare_consented_file(INITIAL_CONTENT, wait_timeout=self._wait_timeout())
        try:
            start = time.perf_counter()
            _write_via_temp_rename(target, UPDATED_CONTENT)
            return time.perf_counter() - start
        finally:
            cleanup_gdpr_state()

    def measure_request_erasure(self) -> float:
        prepare_consented_file(INITIAL_CONTENT, wait_timeout=self._wait_timeout())
        _revoke_consent()
        mount_target = FUSE_MOUNT / TEST_FILENAME
        try:
            start = time.perf_counter()
            fuse_ingest("RequestErasure", timeout=self._wait_timeout(), uid=DS_UID, fid=TEST_FILENAME)
            _wait_for_deletion(mount_target, timeout=self._wait_timeout())
            return time.perf_counter() - start
        finally:
            cleanup_gdpr_state()

    def measure_request_rectification(self) -> float:
        prepare_consented_file(INITIAL_CONTENT, wait_timeout=self._wait_timeout())
        upper_target = UPPER_DIR / TEST_FILENAME
        try:
            start = time.perf_counter()
            fid_new = upload_rectification_file(RECTIFIED_FILENAME, RECTIFIED_CONTENT, timeout=self._wait_timeout())
            fuse_ingest(
                "RequestRectification",
                timeout=self._wait_timeout(),
                uid=DS_UID,
                fid_old=TEST_FILENAME,
                fid_new=fid_new,
            )
            _wait_for_content(upper_target, RECTIFIED_CONTENT, timeout=self._wait_timeout())
            return time.perf_counter() - start
        finally:
            cleanup_gdpr_state()

    def run_iteration(self) -> dict:
        configure_llm(self.mode)
        results = {}
        t0 = time.perf_counter()
        print("read...", end="", flush=True)
        results["t_read_file"] = self.measure_read_file()
        print(" ok write...", end="", flush=True)
        results["t_write_file"] = self.measure_write_file()
        print(" ok consent...", end="", flush=True)
        results["t_give_consent"] = self.measure_give_consent()
        print(" ok revoke...", end="", flush=True)
        results["t_remove_consent"] = self.measure_remove_consent()
        print(" ok erasure...", end="", flush=True)
        results["t_request_erasure"] = self.measure_request_erasure()
        print(" ok rectification...", end="", flush=True)
        results["t_request_rectification"] = self.measure_request_rectification()
        print(" ok", end="", flush=True)
        results["t_total"] = time.perf_counter() - t0
        return results



class BenchmarkRunner:
    def __init__(self, mode: str, iterations: int):
        self.mode = mode
        self.iterations = iterations

    def _make_runner(self):
        if self.mode == MODE_BASELINE:
            return BaselineRunner()
        return GDPRRunner(self.mode)

    def run(self) -> list[dict]:
        preflight_checks(self.mode)
        # Give FUSE a moment to settle after any mode switch (LLM enable/disable,
        # previous mode's cleanup, etc.) before the first iteration starts.
        if self.mode != MODE_BASELINE:
            time.sleep(1.0)
        results = []
        runner = self._make_runner()

        for index in range(self.iterations):
            print(f"  [{self.mode}] iteration {index + 1}/{self.iterations} ... ", end="", flush=True)
            try:
                timings = runner.run_iteration()
                timings["iteration"] = index + 1
                timings["mode"] = self.mode
                results.append(timings)
                print(f"total={timings['t_total']:.4f}s")
            except Exception as exc:
                print(f"FAILED: {exc}")
                if self.mode != MODE_BASELINE:
                    cleanup_gdpr_state()
        return results



class BenchmarkReporter:
    def __init__(self, all_results: dict[str, list[dict]], output_dir: Path):
        self.all_results = all_results
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def save_csv(self):
        csv_path = self.output_dir / "simple_perf_results.csv"
        fieldnames = ["mode", "iteration"] + OPERATIONS
        with open(csv_path, "w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            for mode, rows in self.all_results.items():
                for row in rows:
                    writer.writerow({key: row.get(key, "") for key in fieldnames})
        print(f"\n  CSV saved to {csv_path}")

    def print_summary(self):
        modes = list(self.all_results.keys())
        col_w = 18

        print(f"\n{'=' * 78}")
        print("  Mean ± Std latency per operation (seconds)")
        print(f"{'=' * 78}")
        header = f"  {'Operation':<26}" + "".join(f"{mode:>{col_w}}" for mode in modes)
        print(header)
        print("  " + "-" * (26 + col_w * len(modes)))

        for operation in OPERATIONS:
            row = f"  {operation:<26}"
            for mode in modes:
                values = [entry[operation] for entry in self.all_results[mode]]
                mean = statistics.mean(values)
                std = statistics.stdev(values) if len(values) > 1 else 0.0
                row += f"{mean:>{col_w - 8}.4f}±{std:<7.4f}"
            print(row)
        print()



class _ScaleReporter:
    """
    Collects results across multiple preload sizes and writes a single
    CSV with a 'preload' column alongside mode/iteration/operations.
    Sizes can be a single int (backwards-compat) or a list of ints.
    """

    def __init__(self, output_dir: Path, sizes: list[int]):
        self.output_dir = output_dir
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.sizes = sizes
        # all_rows: list of dicts, each with 'preload', 'mode', 'iteration', + OPERATIONS
        self.all_rows: list[dict] = []

    def add_results(self, preload_n: int, mode_results: dict[str, list[dict]]):
        for mode, rows in mode_results.items():
            for row in rows:
                entry = {"preload": preload_n, "mode": mode}
                entry.update({k: row.get(k, "") for k in ["iteration"] + OPERATIONS})
                self.all_rows.append(entry)

    def save_csv(self):
        tag = "-".join(str(s) for s in self.sizes)
        csv_path = self.output_dir / f"simple_perf_results_preload{tag}.csv"
        fieldnames = ["preload", "mode", "iteration"] + OPERATIONS
        with open(csv_path, "w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(self.all_rows)
        print(f"\n  CSV saved to {csv_path}")

    def print_summary(self):
        col_w = 18
        print(f"\n{'=' * 78}")
        print("  Mean ± Std latency per operation (seconds)  [preload sizes: " +
              ", ".join(str(s) for s in self.sizes) + "]")
        print(f"{'=' * 78}")

        # Group rows by (preload, mode)
        from collections import defaultdict
        grouped: dict[tuple, list[dict]] = defaultdict(list)
        for row in self.all_rows:
            grouped[(row["preload"], row["mode"])].append(row)

        for preload_n in self.sizes:
            modes_present = [m for m in ALL_MODES if (preload_n, m) in grouped]
            if not modes_present:
                continue
            print(f"\n  -- preload={preload_n} --")
            header = f"  {'Operation':<26}" + "".join(f"{m:>{col_w}}" for m in modes_present)
            print(header)
            print("  " + "-" * (26 + col_w * len(modes_present)))
            for op in OPERATIONS:
                line = f"  {op:<26}"
                for m in modes_present:
                    vals = [r[op] for r in grouped[(preload_n, m)] if r.get(op) != ""]
                    if vals:
                        mean = statistics.mean(vals)
                        std = statistics.stdev(vals) if len(vals) > 1 else 0.0
                        line += f"{mean:>{col_w - 8}.4f}±{std:<7.4f}"
                    else:
                        line += f"{'N/A':>{col_w}}"
                print(line)
        print()



def _parse_preload(value: str) -> list[int]:
    """Parse --preload as a single int or comma-separated list of ints."""
    parts = [p.strip() for p in value.split(",") if p.strip()]
    sizes = []
    for p in parts:
        try:
            sizes.append(int(p))
        except ValueError:
            raise argparse.ArgumentTypeError(f"Invalid preload value: {p!r} (must be an integer)")
    return sizes


def parse_args():
    parser = argparse.ArgumentParser(description="Benchmark basic operations across three setups")
    parser.add_argument(
        "--mode",
        choices=ALL_MODES + ["all"],
        default="all",
        help="Which setup(s) to benchmark (default: all)",
    )
    parser.add_argument("--n", type=int, default=3, help="Iterations per setup (default: 3)")
    parser.add_argument(
        "--output",
        type=str,
        default=str(RESULTS_DIR),
        help="Output directory for CSV results",
    )
    parser.add_argument(
        "--preload",
        type=_parse_preload,
        default=None,
        metavar="N[,N...]",
        help="Pre-register N files before benchmarking (e.g. 100 or 100,1000,10000). "
             "When multiple sizes are given the full benchmark is repeated for each. "
             "LLM is disabled during preloading.",
    )
    parser.add_argument(
        "--preload-clean",
        action="store_true",
        help="Remove existing scale files before each preload step.",
    )
    return parser.parse_args()



def main():
    args = parse_args()
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)

    preload_sizes: list[int] | None = args.preload  # None | [100] | [100, 1000, 10000]
    modes = ALL_MODES if args.mode == "all" else [args.mode]
    out_dir = Path(args.output)

    # ── No preload: single benchmark run ────────────────────────────────────
    if not preload_sizes:
        all_results: dict[str, list[dict]] = {}
        for mode in modes:
            print(f"\n{'=' * 60}")
            print(f"  Mode: {mode}  |  Iterations: {args.n}")
            print(f"{'=' * 60}")
            runner = BenchmarkRunner(mode, args.n)
            try:
                results = runner.run()
            except RuntimeError as exc:
                print(f"  SKIPPED: {exc}")
                continue
            if results:
                all_results[mode] = results
                print(f"  Completed {len(results)}/{args.n} iterations")
        if all_results:
            reporter = BenchmarkReporter(all_results, out_dir)
            reporter.save_csv()
            reporter.print_summary()
            print("Done.")
        else:
            print("\nNo results collected.")
        return

    # ── Preload: repeat benchmark for every requested size ───────────────────
    from benchmark.preload_files import preload as _preload, clean_scale_files

    scale_reporter = _ScaleReporter(out_dir, preload_sizes)
    any_results = False

    for preload_n in preload_sizes:
        print(f"\n{'#' * 60}")
        print(f"  PRELOAD SIZE: {preload_n} files")
        print(f"{'#' * 60}")

        # Preload phase
        print(f"\n{'=' * 60}")
        print(f"  Preloading {preload_n} scale files (LLM disabled)")
        print(f"{'=' * 60}")
        _preload(preload_n, clean_first=args.preload_clean, re_enable_llm=False)

        # Benchmark all modes at this preload size
        size_results: dict[str, list[dict]] = {}
        for mode in modes:
            print(f"\n{'=' * 60}")
            print(f"  Mode: {mode}  |  Iterations: {args.n}  |  Preloaded: {preload_n}")
            print(f"{'=' * 60}")
            runner = BenchmarkRunner(mode, args.n)
            try:
                results = runner.run()
            except RuntimeError as exc:
                print(f"  SKIPPED: {exc}")
                continue
            if results:
                size_results[mode] = results
                print(f"  Completed {len(results)}/{args.n} iterations")

        if size_results:
            scale_reporter.add_results(preload_n, size_results)
            any_results = True

    if any_results:
        scale_reporter.save_csv()
        scale_reporter.print_summary()
        print("Done.")
    else:
        print("\nNo results collected.")



if __name__ == "__main__":
    main()
