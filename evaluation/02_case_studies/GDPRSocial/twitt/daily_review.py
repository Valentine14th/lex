"""
Periodic DailyErasureReview process (Art. 17 GDPR).

Spawns a daemon thread that, once per day, iterates over all personal data
in the database and logs batches of DailyErasureReview(data_id) events via
the enforcement logger.  The enforcer may then cause actions such as erasure.
"""

import threading
import time as _time

from instrlib.event import Event

# Interval in seconds between review cycles (default: 24 h).
REVIEW_INTERVAL_SECONDS = 24 * 60 * 60

# Maximum number of DailyErasureReview events per logger.log() call.
BATCH_SIZE = 50


# Registry of (Model, fields) to review.  Populated lazily to avoid
# importing models at module level.
_MODEL_FIELDS: list[tuple[type, tuple[str, ...]]] | None = None


def _get_model_fields():
    global _MODEL_FIELDS
    if _MODEL_FIELDS is None:
        from twitt.models import (
            User, Follow, Twit, Like, Reply, Repost, DirectMessage,
            AdImpression, AdClick, PageVisit,
        )
        _MODEL_FIELDS = [
            (User,           ('username', 'first_name', 'last_name', 'email', 'last_login')),
            (Follow,         ('follower', 'following', 'date')),
            (Twit,           ('content', 'posted_on', 'updated_on', 'author')),
            (Like,           ('user', 'twit', 'created_at')),
            (Reply,          ('content', 'created_at', 'author', 'parent')),
            (Repost,         ('original', 'user', 'message', 'created_at')),
            (DirectMessage,  ('sender', 'recipient', 'content', 'is_read', 'created_at')),
            (AdImpression,   ('ad', 'created_at')),
            (AdClick,        ('ad', 'created_at')),
            (PageVisit,      ('path', 'method', 'status_code', 'referrer',
                              'user_agent', 'session_key', 'ip_hash',
                              'response_time_ms', 'created_at')),
        ]
    return _MODEL_FIELDS


def _iter_data_ids():
    """Yield data_id strings lazily, one at a time."""
    for Model, fields in _get_model_fields():
        model_name = Model.__name__
        for pk in Model.objects.values_list('pk', flat=True).iterator():
            for field in fields:
                yield f'{model_name}.{field}:{pk}'


def _run_daily_review() -> None:
    """Execute one full review cycle: stream all data IDs and submit them
    as DailyErasureReview events in batches to the enforcement logger."""
    from twitt.enforcer import logger

    total = 0
    batch: list[Event] = []

    for did in _iter_data_ids():
        batch.append(Event('DailyErasureReview', did))
        if len(batch) >= BATCH_SIZE:
            evt = threading.Event()
            try:
                logger.log(batch, evt, False)
                evt.wait(timeout=30)
            except Exception as exc:
                print(f"[GDPR] DailyReview batch error: {exc}", flush=True)
            total += len(batch)
            batch = []

    if batch:
        evt = threading.Event()
        try:
            logger.log(batch, evt, False)
            evt.wait(timeout=30)
        except Exception as exc:
            print(f"[GDPR] DailyReview batch error: {exc}", flush=True)
        total += len(batch)

    if total == 0:
        print("[GDPR] DailyReview: no data to review.", flush=True)
    else:
        print(f"[GDPR] DailyReview: cycle complete ({total} items).", flush=True)


def _review_loop() -> None:
    """Background loop: sleep → review → repeat."""
    import django
    django.setup()  # ensure apps are fully loaded in this thread

    while True:
        try:
            _run_daily_review()
        except Exception as exc:
            print(f"[GDPR] DailyReview error: {exc}", flush=True)
        _time.sleep(REVIEW_INTERVAL_SECONDS)


_started = False
_lock = threading.Lock()


def start_daily_review_thread() -> None:
    """Start the background review thread (idempotent)."""
    global _started
    with _lock:
        if _started:
            return
        _started = True
    t = threading.Thread(target=_review_loop, daemon=True, name='gdpr-daily-review')
    t.start()
    print("[GDPR] DailyReview thread started.", flush=True)
