"""
Performance-benchmark driver for miniTwitter_gdpr.

Scenarios
---------
  timeline          – GET the home timeline
    own_tweets        – GET  /accounts/twit/  (current user's tweets)
  post_tweet        – POST a new tweet
  erase_tweet       – DELETE a specific tweet  (via /twit/delete/<uuid>/)
  right_to_info     – GET  /gdpr/request/access/  (Art. 15 access request)
  privacy_notices   – GET  /gdpr/notifications/
  give_consent      – POST /gdpr/consent/  (give consent for statistics)
  revoke_consent    – POST /gdpr/consent/  (revoke consent for statistics)

Each scenario is measured under every combination of:
  u  in {1, 10, 100}       users
  n  in {100, 1000, 10000}  total tweets
  c  in {none, statistics, statistics_ads}  consent level
"""

import os
import re
import signal
import shutil
import sqlite3
import random
from datetime import datetime
from pathlib import Path
from subprocess import Popen, PIPE, STDOUT, run as sp_run
from time import sleep
import uuid

import requests
from lorem_text import lorem
from random import randint
from tools import Task, Subtask

# ── Paths ────────────────────────────────────────────────────────────────
_DRIVER_DIR   = Path(__file__).resolve().parent            # drivers/
_SUITE_DIR    = _DRIVER_DIR.parent                         # privacy_testsuite/
_PROJECT_ROOT = _SUITE_DIR.parent.parent                   # miniTwitter_gdpr/
_SNAPSHOT_DIR = _SUITE_DIR / "db_snapshots"
_BASELINE_ROOT = _SUITE_DIR / "baseline" / "minitwitter_bl"  # stripped copy (no enforcement)

# ── URLs ─────────────────────────────────────────────────────────────────
BASE            = "http://127.0.0.1:8000"
LOGIN_URL       = f"{BASE}/accounts/login/"
TIMELINE_URL    = f"{BASE}/"
OWN_TWEETS_URL  = f"{BASE}/accounts/twit/"
POST_TWEET_URL  = f"{BASE}/post/twit/"
DELETE_TWEET_URL = f"{BASE}/twit/delete/"          # + <uuid>/
ACCESS_URL      = f"{BASE}/gdpr/request/access/"
NOTIFICATIONS_URL    = f"{BASE}/gdpr/notifications/"
CONSENT_URL          = f"{BASE}/gdpr/consent/"
SPEC_CONSENT_URL     = f"{BASE}/gdpr/consent/special/"
FOLLOW_URL           = f"{BASE}/search/user/"
LIKE_URL             = f"{BASE}/twit/"              # + <uuid>/like/
SEND_MSG_URL         = f"{BASE}/messages/send/"
RECTIFICATION_URL    = f"{BASE}/gdpr/request/rectification/"
ERASURE_URL          = f"{BASE}/gdpr/request/erasure/"
OBJECTION_URL        = f"{BASE}/gdpr/request/objection/"

# ── Constants ────────────────────────────────────────────────────────────
CONFIGS        = [(1, 100), (10, 1000), (100, 10000)]   # (users, tweets) (1000, 10000)
CONSENT_LEVELS = ["none"]#, "statistics", "statistics_ads"]


# =========================================================================
#  Scenario
# =========================================================================

class Scenario:

    def __init__(self, sc, app_cmd, database, policy, consent, env=None,
                 project_root=None):
        self.sc = sc
        self.app_cmd = app_cmd
        self.database = database          # path to the *live* DB used by Django
        self.policy = policy
        self.consent = consent            # consent level tag
        self.env = env or dict(os.environ)
        self.project_root = project_root or _PROJECT_ROOT
        self.log_filename = None
        self.proc = None
        self.u = None
        self.n = None

    # ── helpers ──────────────────────────────────────────────────────
    def _snapshot_path(self):
        return _SNAPSHOT_DIR / f"db_u{self.u}_n{self.n}_c{self.consent}.sqlite3"

    def _state_snapshot_path(self):
        return _SNAPSHOT_DIR / f"state_u{self.u}_n{self.n}_c{self.consent}.bin"

    def _restore_db(self):
        """Copy the pre-built snapshot (DB + enforcer state) over live files."""
        src = self._snapshot_path()
        assert src.exists(), f"Snapshot not found: {src}"
        shutil.copy2(src, self.database)
        # Restore enforcer state for enforced runs
        state_src = self._state_snapshot_path()
        state_dst = self.project_root / "enfflash.state"
        if state_src.exists():
            shutil.copy2(state_src, state_dst)
        elif state_dst.exists():
            state_dst.unlink()

    def _user_session(self, i):
        session = requests.Session()
        r = session.get(LOGIN_URL)
        csrf = session.cookies.get("csrftoken")
        r = session.post(LOGIN_URL, data={
            "username": f"user{i}",
            "password": "password",
            "csrfmiddlewaretoken": csrf,
        })
        assert r.ok, f"Login failed for user{i}: {r.status_code}"
        return session

    def _random_user_session(self):
        return self._user_session(randint(0, self.u - 1))

    def _pick_random_tweet_id(self):
        """Return a random tweet UUID (hyphenated) from the live database."""
        db = sqlite3.connect(self.database)
        ids = [r[0] for r in db.execute(
            "SELECT id FROM twitt_twit ORDER BY RANDOM() LIMIT 1").fetchall()]
        db.close()
        if not ids:
            return None
        # Django stores UUIDs as 32-char hex without hyphens in SQLite;
        # normalise so the value matches Django's <uuid:pk> URL converter.
        try:
            return str(uuid.UUID(ids[0]))
        except ValueError:
            return ids[0]

    def _pick_random_other_user_pk(self, exclude_username):
        """Return the PK of a random user that is not exclude_username."""
        db = sqlite3.connect(self.database)
        rows = [r[0] for r in db.execute(
            "SELECT id FROM twitt_user WHERE username != ? ORDER BY RANDOM() LIMIT 1",
            (exclude_username,)).fetchall()]
        db.close()
        return rows[0] if rows else None

    @staticmethod
    def _extract_hidden(html, field_name):
        """Extract a hidden <input> value from an HTML page."""
        m = re.search(
            rf'name="{re.escape(field_name)}"[^>]*value="([^"]+)"'
            rf'|value="([^"]+)"[^>]*name="{re.escape(field_name)}"',
            html)
        if m:
            return m.group(1) or m.group(2)
        return ""

    # ── lifecycle ────────────────────────────────────────────────────
    def initialize(self, config):
        self.u, self.n = config
        pref = f"minitwit.init (sc={self.sc}, u={self.u}, n={self.n}, c={self.consent})"

        with Task(pref, "Restoring database snapshot"):
            self._restore_db()

        log_dir = _SUITE_DIR / "logs" / "multi_runs"
        log_dir.mkdir(parents=True, exist_ok=True)
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_filename = str(log_dir / f"{ts}_{self.sc}_{self.consent}_{self.policy}.log")
        self._start_server()

    def _start_server(self):
        pref = f"minitwit.init (sc={self.sc}, u={self.u}, n={self.n})"
        with Task(pref, "Starting Django server"):
            # Kill anything already on port 8000
            sp_run(["fuser", "-k", "8000/tcp"],
                   stdout=PIPE, stderr=PIPE)
            sleep(0.5)
            self._log_fh = open(self.log_filename, "a")
            self.proc = Popen(self.app_cmd, stdin=PIPE,
                              stdout=self._log_fh, stderr=STDOUT, text=True,
                              cwd=str(self.project_root), env=self.env)
            self._wait_for_server_ready(timeout_s=30)

    def _wait_for_server_ready(self, timeout_s=30):
        deadline = datetime.now().timestamp() + timeout_s
        while datetime.now().timestamp() < deadline:
            if not self.is_process_running():
                return
            try:
                r = requests.get(LOGIN_URL, timeout=0.5)
                if r.status_code < 500:
                    return
            except requests.exceptions.RequestException:
                pass
            sleep(0.2)

    def continue_(self):
        """Between repeated measurements – restore DB for destructive scenarios."""
        if self.sc in ("erase_tweet", "request_erasure"):
            # Data may have been deleted; restore DB and restart server
            self.proc.kill()
            self.proc.wait()
            self._log_fh.close()
            self._restore_db()
            self._start_server()

    def finalize(self):
        with Task("minitwit.finalize", "Killing Django server"):
            if self.proc:
                self.proc.kill()
                self.proc.wait()
                self.proc = None
            if hasattr(self, '_log_fh') and self._log_fh:
                self._log_fh.close()
                self._log_fh = None
            # Make sure port is freed
            sp_run(["fuser", "-k", "8000/tcp"], stdout=PIPE, stderr=PIPE)
            sleep(0.5)

    def is_process_running(self):
        return self.proc is not None and self.proc.poll() is None

    # ── measurement ──────────────────────────────────────────────────
    def run(self):
        result_base = {"sc": self.sc, "u": self.u, "n": self.n,
                       "c": self.consent}

        if not self.is_process_running():
            print("Django server is not running!")
            return None

        try:
            if self.sc == "timeline":
                return self._run_timeline(result_base)
            elif self.sc == "own_tweets":
                return self._run_own_tweets(result_base)
            elif self.sc == "post_tweet":
                return self._run_post_tweet(result_base)
            elif self.sc == "erase_tweet":
                return self._run_erase_tweet(result_base)
            elif self.sc == "right_to_info":
                return self._run_right_to_info(result_base)
            elif self.sc == "privacy_notices":
                return self._run_privacy_notices(result_base)
            elif self.sc == "give_consent":
                return self._run_give_consent(result_base)
            elif self.sc == "revoke_consent":
                return self._run_revoke_consent(result_base)
            elif self.sc == "follow_user":
                return self._run_follow_user(result_base)
            elif self.sc == "search_user":
                return self._run_search_user(result_base)
            elif self.sc == "like_tweet":
                return self._run_like_tweet(result_base)
            elif self.sc == "send_message":
                return self._run_send_message(result_base)
            elif self.sc == "special_consent":
                return self._run_special_consent(result_base)
            elif self.sc == "request_rectification":
                return self._run_request_rectification(result_base)
            elif self.sc == "request_erasure":
                return self._run_request_erasure(result_base)
            elif self.sc == "request_objection":
                return self._run_request_objection(result_base)
        except requests.exceptions.RequestException as e:
            print(f"Request error in {self.sc}: {e}")
            return None

    # ── individual workflows ─────────────────────────────────────────
    def _run_timeline(self, base):
        with Task("run", 'Scenario "timeline"'):
            s = self._random_user_session()
            r = s.get(TIMELINE_URL)
            assert r.ok
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_own_tweets(self, base):
        with Task("run", 'Scenario "own_tweets"'):
            s = self._random_user_session()
            r = s.get(OWN_TWEETS_URL)
            assert r.ok
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_post_tweet(self, base):
        with Task("run", 'Scenario "post_tweet"'):
            s = self._random_user_session()
            csrf = s.cookies.get("csrftoken")
            txt = lorem.paragraph()[:137] + "..."
            r = s.post(POST_TWEET_URL, data={
                "content": txt,
                "twit_uid": str(uuid.uuid4()),  
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"post_tweet failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_erase_tweet(self, base):
        with Task("run", 'Scenario "erase_tweet"'):
            twit_id = self._pick_random_tweet_id()
            if twit_id is None:
                print("No tweets to delete")
                return None
            # Log in as the author of that tweet
            db = sqlite3.connect(self.database)
            # SQLite stores UUIDs without hyphens; strip them for the query
            twit_id_raw = twit_id.replace("-", "")
            row = db.execute(
                "SELECT author_id FROM twitt_twit WHERE id=? OR id=?",
                (twit_id, twit_id_raw)
            ).fetchone()
            author_id_raw = row[0]
            username = db.execute(
                "SELECT username FROM twitt_user WHERE id=? OR id=?",
                (author_id_raw, author_id_raw.replace("-", ""))
            ).fetchone()[0]
            db.close()

            s = requests.Session()
            r = s.get(LOGIN_URL)
            csrf = s.cookies.get("csrftoken")
            s.post(LOGIN_URL, data={
                "username": username,
                "password": "password",
                "csrfmiddlewaretoken": csrf,
            })
            csrf = s.cookies.get("csrftoken")
            url = f"{DELETE_TWEET_URL}{twit_id}/"
            r = s.post(url, data={"csrfmiddlewaretoken": csrf},
                       allow_redirects=False)
            assert r.status_code == 302, f"erase_tweet failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_right_to_info(self, base):
        with Task("run", 'Scenario "right_to_info"'):
            s = self._random_user_session()
            r = s.get(ACCESS_URL)
            assert r.ok
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_privacy_notices(self, base):
        with Task("run", 'Scenario "privacy_notices"'):
            s = self._random_user_session()
            r = s.get(NOTIFICATIONS_URL)
            assert r.ok
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_give_consent(self, base):
        with Task("run", 'Scenario "give_consent"'):
            s = self._random_user_session()
            csrf = s.cookies.get("csrftoken")
            r = s.post(CONSENT_URL, data={
                "give_consent": "statistics",
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"give_consent failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_revoke_consent(self, base):
        with Task("run", 'Scenario "revoke_consent"'):
            s = self._random_user_session()
            csrf = s.cookies.get("csrftoken")
            r = s.post(CONSENT_URL, data={
                "revoke_consent": "statistics",
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"revoke_consent failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_follow_user(self, base):
        """POST a follow (triggers input enforcement for FollowUserView)."""
        with Task("run", 'Scenario "follow_user"'):
            sender_i = randint(0, self.u - 1)
            sender_username = f"user{sender_i}"
            # Pick a user that sender is not already following
            db = sqlite3.connect(self.database)
            row = db.execute("""
                SELECT u.id FROM twitt_user u
                WHERE u.username != ?
                  AND u.id NOT IN (
                      SELECT f.following_id FROM twitt_follow f
                      JOIN twitt_user fu ON fu.id = f.follower_id
                      WHERE fu.username = ?
                  )
                ORDER BY RANDOM() LIMIT 1
            """, (sender_username, sender_username)).fetchone()
            db.close()
            if row is None:
                print(f"follow_user: {sender_username} already follows everyone")
                return None
            target_pk = row[0]
            s = self._user_session(sender_i)
            csrf = s.cookies.get("csrftoken")
            r = s.post(FOLLOW_URL, data={
                "pk": target_pk,
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"follow_user failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_search_user(self, base):
        """GET user search/list page."""
        with Task("run", 'Scenario "search_user"'):
            s = self._random_user_session()
            r = s.get(FOLLOW_URL)
            assert r.ok, f"search_user failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_like_tweet(self, base):
        """POST a like on a random tweet (triggers Read enforcement event)."""
        with Task("run", 'Scenario "like_tweet"'):
            twit_id = self._pick_random_tweet_id()
            if twit_id is None:
                print("No tweets to like")
                return None
            s = self._random_user_session()
            csrf = s.cookies.get("csrftoken")
            r = s.post(f"{LIKE_URL}{twit_id}/like/", data={
                "csrfmiddlewaretoken": csrf,
                "next": "/",
            }, allow_redirects=False)
            assert r.status_code == 302, f"like_tweet failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_send_message(self, base):
        """POST a direct message (triggers Write/Collect enforcement events)."""
        with Task("run", 'Scenario "send_message"'):
            sender_i = randint(0, self.u - 1)
            s = self._user_session(sender_i)
            recipient_pk = self._pick_random_other_user_pk(f"user{sender_i}")
            if recipient_pk is None:
                print("No other users for send_message")
                return None
            csrf = s.cookies.get("csrftoken")
            r = s.post(SEND_MSG_URL, data={
                "recipient": recipient_pk,
                "content": "Hello, this is a benchmark message.",
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"send_message failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_special_consent(self, base):
        """POST special consent for a data category (triggers SpecialConsent event)."""
        with Task("run", 'Scenario "special_consent"'):
            s = self._random_user_session()
            csrf = s.cookies.get("csrftoken")
            r = s.post(SPEC_CONSENT_URL, data={
                "purpose": "statistics",
                "special_category": "health",
                "submit": "true",
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"special_consent failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_request_rectification(self, base):
        """GET + POST rectification request (triggers RequestRectification + Rectify causation)."""
        with Task("run", 'Scenario "request_rectification"'):
            s = self._random_user_session()
            # GET creates the GDPRRequest and embeds its ID in the form
            r_get = s.get(RECTIFICATION_URL)
            assert r_get.ok, f"request_rectification GET failed: {r_get.status_code}"
            rq_id = self._extract_hidden(r_get.text, "gdpr_request_id")
            csrf = s.cookies.get("csrftoken")
            r = s.post(RECTIFICATION_URL, data={
                "field": "User.first_name",
                "object_id": "",
                "new_data": "Alice",
                "gdpr_request_id": rq_id,
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"request_rectification POST failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_request_erasure(self, base):
        """GET + POST erasure request for a random tweet (triggers RequestErasure + Delete causation)."""
        with Task("run", 'Scenario "request_erasure"'):
            twit_id = self._pick_random_tweet_id()
            if twit_id is None:
                print("No tweets for request_erasure")
                return None
            s = self._random_user_session()
            r_get = s.get(ERASURE_URL)
            assert r_get.ok, f"request_erasure GET failed: {r_get.status_code}"
            rq_id = self._extract_hidden(r_get.text, "gdpr_request_id")
            csrf = s.cookies.get("csrftoken")
            r = s.post(ERASURE_URL, data={
                "scope": "Twit",
                "object_id": str(twit_id),
                "gdpr_request_id": rq_id,
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"request_erasure POST failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}

    def _run_request_objection(self, base):
        """GET + POST objection request (triggers RequestObjection event)."""
        with Task("run", 'Scenario "request_objection"'):
            s = self._random_user_session()
            r_get = s.get(OBJECTION_URL)
            assert r_get.ok, f"request_objection GET failed: {r_get.status_code}"
            rq_id = self._extract_hidden(r_get.text, "gdpr_request_id")
            csrf = s.cookies.get("csrftoken")
            r = s.post(OBJECTION_URL, data={
                "purpose": "statistics",
                "reason": "I object to processing for analytics purposes.",
                "gdpr_request_id": rq_id,
                "csrfmiddlewaretoken": csrf,
            }, allow_redirects=False)
            assert r.status_code == 302, f"request_objection POST failed: {r.status_code}"
            return {**base, "t": r.elapsed.total_seconds()}


# =========================================================================
#  Application
# =========================================================================

class Application:

    app_cmd  = ["python3", "manage.py", "runserver", "127.0.0.1:8000", "--noreload"]

    # Default enforcer path matching the project Makefile (ENFGUARD ?= ~/Git/whyenf/enfguard)
    enfguard_exe = str(Path.home() / "Git" / "whyenf" / "enfguard")

    def start(self, policy, exe, instrlib=None, formula=None, sig=None):
        self.policy = policy
        self.is_baseline = (policy == "baseline")
        self._project_root = _BASELINE_ROOT if self.is_baseline else _PROJECT_ROOT
        self.database = str(self._project_root / "db.sqlite3")
        self._base_cmd = list(self.app_cmd)
        self._env = dict(os.environ)
        self._formula_override = formula
        self._sig_override = sig
        if not self.is_baseline:
            self._env["INSTRLIB_EXE"] = exe if exe else self.enfguard_exe
        if instrlib is not None:
            instrlib_path = Path(instrlib).resolve()
            # Prepend the parent directory so `import instrlib` finds this version.
            existing_pythonpath = self._env.get("PYTHONPATH", "")
            self._env["PYTHONPATH"] = (
                str(instrlib_path.parent) + (":" + existing_pythonpath if existing_pythonpath else "")
            )
        with Task("minitwit.start", "Preparing evaluation"):
            pass   # DB preparation is per-snapshot, handled in Scenario.initialize

    def stop(self):
        with Task("minitwit.stop", "Evaluation finished"):
            pass

    def scenarios(self, policy, config=None):
        with Task("minitwit.scenarios", "Building scenario list"):
            cmd = list(self._base_cmd)
            env = dict(self._env)
            if not self.is_baseline and policy and policy != "uninstrumented":
                env["INSTRLIB_FORMULA"] = self._formula_override if self._formula_override else f"policies/{policy}.mfotl"
                env["INSTRLIB_SIG"] = self._sig_override if self._sig_override else "policies/consent.sig"

            u = config[0] if config is not None else 1

            # Scenarios that require at least 2 users in the database.
            _MULTI_USER = {"follow_user", "send_message"}

            scenario_names = [
                "timeline",
                "post_tweet",
                #"erase_tweet",
                "follow_user",
                #"search_user",
                "like_tweet",
                "send_message",
                "right_to_info",
                "privacy_notices",
                "give_consent",
                "revoke_consent",
                "special_consent",
                "request_rectification",
                "request_erasure",
                "request_objection",
            ]

            scenarios = []
            for sc_name in scenario_names:
                if sc_name in _MULTI_USER and u < 2:
                    continue
                for consent in CONSENT_LEVELS:
                    scenarios.append(
                        Scenario(sc_name, cmd, self.database, policy, consent,
                                 env, project_root=self._project_root)
                    )
        return scenarios

    def configurations(self):
        with Task("minitwit.configurations", "Building configurations"):
            configs = list(CONFIGS)
        return configs

    def dep_vars(self):
        return ["t"]

    def indep_vars(self):
        return ["sc", "u", "n", "c"]
