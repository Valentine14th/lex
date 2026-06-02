"""
Enforcement instrumentation for the minitwit_gdpr policy.

Maps all 64 events from minitwit_gdpr.sig to application-level actions,
providing schema definitions, suppression/causation handlers, and the
instrumentation mapping that transforms low-level ORM / URL events into
policy events understood by the EnfGuard enforcement engine.
"""

import json
import os
import shutil
import uuid
import zipfile
from io import BytesIO
from typing import Any, Dict, List

from instrlib.event import Event
from instrlib.pdp import EnfGuard
try:
    from instrlib.pdp import MultiPDP
    _MULTI_PDP_AVAILABLE = True
except ImportError:
    _MULTI_PDP_AVAILABLE = False

try:
    from instrlib.logger import MultiLogger
    _MULTI_LOGGER_AVAILABLE = True
except ImportError:
    _MULTI_LOGGER_AVAILABLE = False
from instrlib.logger import Logger
from instrlib.pep import InstrumentationMapping, PEP
from instrlib.schema import Schema
from instrlib.middleware import _thread_locals

from Twitter.settings import INSTRLIB_EXE, INSTRLIB_FORMULA, INSTRLIB_LOG, INSTRLIB_SIG, INSTRLIB_FUNC, INSTRLIB_STATE


# =========================================================================
#  HELPERS
# =========================================================================

def _generate_id() -> str:
    return str(uuid.uuid4())[:8]


def _get_request():
    return getattr(_thread_locals, 'request', None)


def _active_purposes(username: str) -> list[str]:
    """Return the list of purposes the user has currently consented to."""
    from twitt.models import ConsentRecord
    purposes = list(
        ConsentRecord.objects.filter(user__username=username, is_active=True,
                                     special_category='')
        .values_list('purpose', flat=True)
    )
    return purposes + ['service']


def _active_purposes_for_special(username: str, special_categories: list[str]) -> list[str]:
    """Like _active_purposes but, when *special_categories* is non-empty,
    only returns purposes for which the user holds active SpecialConsent
    for **every** detected category.  'service' is always included since
    it is a legitimate-interest basis (not consent-based)."""
    if not special_categories:
        return _active_purposes(username)
    from twitt.models import ConsentRecord
    base = _active_purposes(username)
    # For each non-service purpose, require special consent for ALL categories
    approved: list[str] = ['service']
    for p in base:
        if p == 'service':
            continue
        consented_cats = set(
            ConsentRecord.objects.filter(
                user__username=username, purpose=p,
                is_active=True,
            ).exclude(special_category='').values_list('special_category', flat=True)
        )
        if all(cat in consented_cats for cat in special_categories):
            approved.append(p)
    return approved


def _extract_events(args: tuple) -> Dict[str, List]:
    """Normalise proactive (list-of-dicts) and reactive (orig,dict,resp,...) args."""
    if len(args) == 1 and isinstance(args[0], list):
        result: Dict[str, List] = {}
        for ej in args[0]:
            result.setdefault(ej['name'], []).append(tuple(ej['args']))
        return result
    if len(args) >= 2 and isinstance(args[1], dict):
        return args[1]
    return {}


# =========================================================================
#  SUPPRESSION HANDLERS  (6 suppressable events)
# =========================================================================

def suppress_read_handler(orig, event_args, response, *a, **kw):
    return None

def suppress_write_handler(orig, event_args, response, *a, **kw):
    return orig

def suppress_collect_handler(orig, event_args, response, *a, **kw):
    return None

def suppress_consent_handler(orig, event_args, response, *a, **kw):
    return None

def suppress_revoke_handler(orig, event_args, response, *a, **kw):
    return None

def suppress_special_consent_handler(orig, event_args, response, *a, **kw):
    return None

def suppress_lift_restriction_handler(orig, event_args, response, *a, **kw):
    return None


# =========================================================================
#  CAUSATION HANDLERS  (28 causable)
# =========================================================================

_declarations: Dict[str, Dict[str, Any]] = {}

def _ensure_decl(d):
    if d not in _declarations:
        _declarations[d] = {'text': [], 'contains': [], 'contains_data': []}


def noop_handler(*a, **kw):
    pass


def delete_handler(*args, **kwargs):
    from twitt.models import User, Twit, Reply, DirectMessage, Like, Repost
    _model_map = {'Twit': Twit, 'Reply': Reply, 'DirectMessage': DirectMessage,
                  'Like': Like, 'Repost': Repost}
    for da in _extract_events(args).get('Delete', []):
        did = str(da[0])
        if did.startswith('User:all:'):
            try: User.objects.get(username=did.split(':', 2)[2]).delete_data()
            except User.DoesNotExist: pass
        elif '.' in did and ':' in did:
            cls = did.split('.')[0]
            pk_str = did.rsplit(':', 1)[-1]
            Model = _model_map.get(cls)
            if Model:
                try: Model.objects.filter(pk=pk_str).delete()
                except (ValueError, IndexError): pass


def rectify_handler(*args, **kwargs):
    from twitt.models import User, Twit, Reply, DirectMessage
    _model_map = {'User': User, 'Twit': Twit, 'Reply': Reply, 'DirectMessage': DirectMessage}
    for ra in _extract_events(args).get('Rectify', []):
        d_old, d_new = str(ra[0]), str(ra[1])
        if '.' in d_old and ':' in d_old:
            cf, oid = d_old.rsplit(':', 1)
            cn, fn = cf.split('.', 1)
            try:
                Model = _model_map.get(cn)
                if Model:
                    pk = oid if cn in ('Twit', 'Reply', 'DirectMessage') else int(oid)
                    obj = Model.objects.get(pk=pk)
                    setattr(obj, fn, d_new)
                    obj.save(update_fields=[fn])
            except (ValueError, Model.DoesNotExist): pass


def declaration_handler(*args, **kwargs):
    for da in _extract_events(args).get('Declaration', []):
        _ensure_decl(str(da[0]))


def has_text_handler(*args, **kwargs):
    for ta in _extract_events(args).get('HasText', []):
        d, t = str(ta[0]), str(ta[1])
        _ensure_decl(d)
        _declarations[d]['text'].append(t)


def contains_handler(*args, **kwargs):
    for ca in _extract_events(args).get('Contains', []):
        d = str(ca[0])
        _ensure_decl(d)
        _declarations[d]['contains'].append(str(ca[1]))


EXPORT_DIR = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'exports')

def _export_path(request_id: str) -> str:
    """Canonical export file path for a given request ID."""
    return os.path.join(EXPORT_DIR, f'gdpr_export_{request_id}.json')


def personal_data_copy_handler(*args, **kwargs):
    """Create JSON export(s) for PersonalDataCopy events and return their file paths."""
    from twitt.models import (
        User, Twit, Follow, Like, Reply, Repost, DirectMessage,
        ConsentRecord, Ad, AdImpression, AdClick, PageVisit,
    )
    export_paths: list[str] = []
    for pa in _extract_events(args).get('PersonalDataCopy', []):
        fid, ds = str(pa[0]), str(pa[1])
        try:
            u = User.objects.get(username=ds)
            data = {
                # ── account ──────────────────────────────────────────
                'username': u.username,
                'first_name': u.first_name,
                'last_name': u.last_name,
                'email': u.email,
                'date_joined': str(u.date_joined),
                'last_login': str(u.last_login),

                # ── tweets ───────────────────────────────────────────
                'twits': list(
                    Twit.objects.filter(author=u)
                    .values('id', 'content', 'posted_on')
                ),

                # ── social graph ─────────────────────────────────────
                'following': list(
                    Follow.objects.filter(follower=u)
                    .values('id', 'following__username')
                ),
                'followers': list(
                    Follow.objects.filter(following=u)
                    .values('id', 'follower__username')
                ),

                # ── likes ────────────────────────────────────────────
                'likes_given': list(
                    Like.objects.filter(user=u)
                    .values('id', 'twit_id', 'created_at')
                ),
                'likes_received': list(
                    Like.objects.filter(twit__author=u)
                    .values('id', 'twit_id', 'user__username', 'created_at')
                ),

                # ── replies ──────────────────────────────────────────
                'replies': list(
                    Reply.objects.filter(author=u)
                    .values('id', 'parent_id', 'content', 'created_at')
                ),

                # ── reposts ──────────────────────────────────────────
                'reposts': list(
                    Repost.objects.filter(user=u)
                    .values('id', 'original_id', 'message', 'created_at')
                ),

                # ── direct messages ──────────────────────────────────
                'direct_messages_sent': list(
                    DirectMessage.objects.filter(sender=u)
                    .values('id', 'recipient__username', 'content', 'created_at')
                ),
                'direct_messages_received': list(
                    DirectMessage.objects.filter(recipient=u)
                    .values('id', 'sender__username', 'content', 'created_at')
                ),

                # ── consent records ──────────────────────────────────
                'consent_records': list(
                    ConsentRecord.objects.filter(user=u)
                    .values('id', 'purpose', 'is_active', 'created_at')
                ),

                # ── ad interactions ──────────────────────────────────
                'ad_impressions': list(
                    AdImpression.objects.filter(user=u)
                    .values('id', 'ad__title', 'created_at')
                ),
                'ad_clicks': list(
                    AdClick.objects.filter(user=u)
                    .values('id', 'ad__title', 'created_at')
                ),

                # ── page visits ──────────────────────────────────────
                'page_visits': list(
                    PageVisit.objects.filter(user=u)
                    .values('id', 'path', 'method', 'created_at')
                ),
            }
            os.makedirs(EXPORT_DIR, exist_ok=True)
            fp = _export_path(fid)
            with open(fp, 'w') as f:
                json.dump(data, f, indent=2, default=str)
            export_paths.append(fp)
            print(f"[GDPR] PersonalDataCopy → {fp}")
        except User.DoesNotExist:
            pass
    return export_paths


def contains_data_handler(*args, **kwargs):
    for ca in _extract_events(args).get('ContainsData', []):
        d = str(ca[0])
        _ensure_decl(d)
        _declarations[d]['contains_data'].append(str(ca[1]))


def _flush_information_handlers(*args, **kwargs) -> list[str]:
    """Process Declaration/HasText/Contains/PersonalDataCopy/ContainsData.
    Returns the list of export file paths produced by PersonalDataCopy.
    Clears _declarations first so stale data from previous timepoints
    does not bleed into the current batch."""
    _declarations.clear()
    declaration_handler(*args, **kwargs)
    has_text_handler(*args, **kwargs)
    contains_handler(*args, **kwargs)
    export_paths = personal_data_copy_handler(*args, **kwargs)
    contains_data_handler(*args, **kwargs)
    return export_paths if export_paths else []


def inform_handler(*args, **kwargs):
    from twitt.models import GDPRNotification, User
    _flush_information_handlers(*args, **kwargs)
    events = _extract_events(args)
    for ia in events.get('Inform', []):
        ds, decl_id = str(ia[1]), str(ia[2])
        texts = set(_declarations.get(decl_id, {}).get('text', []))
        text = '<br>'.join(sorted(texts)) if texts else f'[Declaration {decl_id}]'
        try:
            GDPRNotification.objects.create(
                user=User.objects.get(username=ds),
                declaration_id=decl_id, text=text)
        except User.DoesNotExist: pass


def activity_record_handler(*args, **kwargs):
    from twitt.models import ActivityLog
    for ar in _extract_events(args).get('ActivityRecord', []):
        ActivityLog.objects.create(
            activity=str(ar[0]), property_name=str(ar[1]), value=str(ar[2]))

def notify_erasure_handler(*args, **kwargs):
    for ne in _extract_events(args).get('NotifyErasure', []):
        print(f"[GDPR] NotifyErasure → entity={ne[0]} data={ne[1]}")


def notify_rectification_handler(*args, **kwargs):
    for nr in _extract_events(args).get('NotifyRectification', []):
        print(f"[GDPR] NotifyRectification → entity={nr[0]} old={nr[1]} new={nr[2]}")


def notify_restriction_handler(*args, **kwargs):
    for nr in _extract_events(args).get('NotifyRestriction', []):
        print(f"[GDPR] NotifyRestriction → entity={nr[0]} data={nr[1]} purpose={nr[2]}")


def send_file_handler(*args, **kwargs):
    for sf in _extract_events(args).get('SendFile', []):
        entity, fid = str(sf[0]), str(sf[1])
        fp = _export_path(fid)
        if os.path.isfile(fp):
            print(f"[GDPR] SendFile → entity={entity} file={fp} (ready to transmit)", flush=True)
        else:
            print(f"[GDPR] SendFile → entity={entity} file_id={fid} (export file not found at {fp})", flush=True)


def request_response_handler(*args, **kwargs):
    """Handle RequestResponse events.

    A batch may contain Declaration/HasText (notification text),
    PersonalDataCopy (export JSON), and RequestResponse itself.
    We flush them first, then assemble:
      - response_text  = joined declaration texts
      - response_file  = zip archive containing the export JSON(s)

    Note: In the proactive dispatch path, each handler receives only its own
    filtered events.  The Declaration/HasText/PersonalDataCopy handlers will
    have already run (populating _declarations and creating export files on
    disk) but _flush_information_handlers here will only find what is in *our*
    args.  The reactive path (which runs after the proactive path) receives
    ALL events and will overwrite with the full data.
    """
    from django.conf import settings
    from django.core.files.base import ContentFile
    from twitt.models import GDPRRequest

    export_paths = _flush_information_handlers(*args, **kwargs)
    events = _extract_events(args)

    for rr in events.get('RequestResponse', []):
        ds, rq_id, resp_text = str(rr[0]), str(rr[1]), str(rr[2])
        print(f"[GDPR] request_response_handler: ds={ds} rq_id={rq_id}", flush=True)
        try:
            r = GDPRRequest.objects.get(pk=rq_id)
        except GDPRRequest.DoesNotExist:
            print(f"[GDPR] request_response_handler: GDPRRequest {rq_id} NOT FOUND", flush=True)
            continue

        # ── Collect declaration texts (may be populated by prior handler calls) ──
        all_decl_texts: list[str] = []
        for decl_id_set in _declarations.values():
            all_decl_texts.extend(decl_id_set.get('text', []))
        # Use declaration texts if available, else the explicit response text
        text = '\n'.join(dict.fromkeys(all_decl_texts)) if all_decl_texts else resp_text
        r.response_text = text

        # ── Build zip if there are exported data files ──
        # Only attach data exports for access/portability requests
        if r.request_type in ('access', 'portability'):
            # Look up export files via ContainsData events (links response to file IDs)
            if not export_paths:
                for cd in events.get('ContainsData', []):
                    fp = _export_path(str(cd[1]))
                    if os.path.isfile(fp):
                        export_paths.append(fp)

            if export_paths:
                buf = BytesIO()
                with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as zf:
                    for fp in export_paths:
                        if os.path.isfile(fp):
                            zf.write(fp, os.path.basename(fp))
                buf.seek(0)
                filename = f'gdpr_response_{rq_id}.zip'
                r.response_file.save(filename, ContentFile(buf.read()), save=False)

        r.status = 'completed'
        r.save()
        print(f"[GDPR] RequestResponse → rq={rq_id} ds={ds} "
              f"text_len={len(text)} files={len(export_paths)}", flush=True)


def daily_erasure_review_handler(*args, **kwargs):
    for dr in _extract_events(args).get('DailyErasureReview', []):
        print(f"[GDPR] DailyErasureReview → data={dr[0]}")


def is_portability_request_handler(*args, **kwargs):
    for ip in _extract_events(args).get('IsPortabilityRequest', []):
        print(f"[GDPR] IsPortabilityRequest → rq={ip[0]}")


# =========================================================================
#  SCHEMA  – all events from minitwit_gdpr.sig
# =========================================================================

schema = Schema()

# suppressable (–)
schema.add('Read',                  [str, str, str, str, str])
schema.add('Write',                 [str, str, str, str, str])
schema.add('Collect',               [str, str, str, str])
schema.add('Consent',               [str, str])
schema.add('Revoke',                [str, str])
schema.add('SpecialConsent',        [str, str, str])
schema.add('LiftRestriction',       [str, str, str])

# causable (+)
schema.add('ActivityRecord',        [str, str, str])
schema.add('Contains',              [str, str])
schema.add('ContainsData',          [str, str])
schema.add('DailyErasureReview',    [str])
schema.add('Declaration',           [str])
schema.add('Delete',                [str])
schema.add('HasText',               [str, str])
schema.add('Inform',                [str, str, str])
schema.add('IsLastResortTransfer',  [str, str, str, str, int, int, str])
schema.add('IsPortabilityRequest',  [str])
schema.add('IsStatutoryContractualRequirement', [str, str, str, str])
schema.add('NoteCategory',          [str])
schema.add('NoteCriteria',          [str])
schema.add('NoteDS',                [str])
schema.add('NoteData',              [str])
schema.add('NoteEntity',            [str])
schema.add('NoteInterest',          [str])
schema.add('NoteLegalBasis',        [str])
schema.add('NotePurpose',           [str])
schema.add('NoteRequest',           [str])
schema.add('NoteSpan',              [int])
schema.add('NotifyErasure',         [str, str])
schema.add('NotifyRectification',   [str, str, str])
schema.add('NotifyRestriction',     [str, str, str])
schema.add('PersonalDataCopy',      [str, str])
schema.add('Rectify',               [str, str])
schema.add('RequestResponse',       [str, str, str])
schema.add('SendFile',              [str, str])

# observable (no +/–)
schema.add('AcceptDataUsage',       [str])
schema.add('ContestAccuracy',       [str, str, str])
schema.add('HasCategory',           [str, str])
schema.add('HasIntendedRecipient',  [str, str])
schema.add('IsAdministrativeArrangement', [int, int, int])
schema.add('IsContractualClauses',  [int, str, str, str, str, int])
schema.add('IsHealthRelated',       [str])
schema.add('IsNecessaryForImportantPublicInterest', [str, str])
schema.add('IsNecessaryForJudicialClaims',          [str])
schema.add('IsNecessaryForLegalObligation',         [str, str])
schema.add('IsNecessaryForProtectionOfRights',      [str, str])
schema.add('IsNecessaryForPublicInterest',          [str, str])
schema.add('IsNecessaryForSpecialMedicalReasons',   [str])
schema.add('IsNecessaryForSubstantialPublicInterest', [str])
schema.add('IsNecessaryForVitalInterests',          [str, str, str])
schema.add('IsRestrictionRequest',  [str, str, str])
schema.add('IsSpecialData',         [str, str])
schema.add('PersonalData',          [str, str])
schema.add('RelatesToCriminalConvictionsOrOffences', [str])
schema.add('RequestAccess',         [str, str])
schema.add('RequestObjection',      [str, str, str, str])
schema.add('RequestRectification',  [str, str, str, str])
schema.add('RequestErasure',        [str, str, str])
schema.add('RequestRecipientInformation', [str, str])
schema.add('Send',                  [str, str])
schema.add('SpecialRevoke',         [str, str, str])
schema.add('SpecifiesNewController',[str, str])
schema.add('TP',                    [int])

# =========================================================================
#  PDP
# =========================================================================

_formulas = [f.strip() for f in INSTRLIB_FORMULA.split(',') if f.strip()]
_sigs = [s.strip() for s in INSTRLIB_SIG.split(',') if s.strip()]

# Expand a single directory to all .mfotl / .sig files within it.
import glob as _glob
if len(_formulas) == 1 and os.path.isdir(_formulas[0]):
    _dir = _formulas[0]
    _formulas = sorted(_glob.glob(os.path.join(_dir, '*.mfotl')))
    if not _formulas:
        raise RuntimeError(f"[Enforcer] No .mfotl files found in directory: {_dir}")
    # Always prefer .sig files found in the formula directory over the default.
    _dir_sigs = sorted(_glob.glob(os.path.join(_dir, '*.sig')))
    if _dir_sigs:
        _sigs = _dir_sigs
if len(_sigs) == 1 and os.path.isdir(_sigs[0]):
    _dir = _sigs[0]
    _sigs = sorted(_glob.glob(os.path.join(_dir, '*.sig')))
    if not _sigs:
        raise RuntimeError(f"[Enforcer] No .sig files found in directory: {_dir}")

def _sig_for(idx: int) -> str:
    """Return the signature file for formula index idx, falling back to the last one."""
    if idx < len(_sigs):
        return _sigs[idx]
    return _sigs[-1] if _sigs else INSTRLIB_SIG


def _state_for(name: str) -> str | None:
    """Return a per-enforcer state path to avoid cross-enforcer contention."""
    if not INSTRLIB_STATE:
        return None
    base, ext = os.path.splitext(INSTRLIB_STATE)
    ext = ext or ".state"
    safe_name = "".join(ch if ch.isalnum() or ch in ("-", "_") else "_" for ch in name)
    return f"{base}__{safe_name}{ext}"


def _seed_state_for(name: str) -> str | None:
    """Copy the common source state file into a per-enforcer state file."""
    state_path = _state_for(name)
    if state_path is None:
        return None
    if not os.path.isfile(INSTRLIB_STATE):
        raise RuntimeError(
            f"[Enforcer] INSTRLIB_STATE must exist for multi mode seeding: {INSTRLIB_STATE}"
        )
    state_dir = os.path.dirname(state_path)
    if state_dir:
        os.makedirs(state_dir, exist_ok=True)
    shutil.copy2(INSTRLIB_STATE, state_path)
    return state_path

if _MULTI_PDP_AVAILABLE: #and len(_formulas) > 1:
    print(f"[Enforcer] Multi-enforcer mode: {len(_formulas)} formulas detected")
    pdp = MultiPDP(log_file=INSTRLIB_LOG)
    for _idx, _formula in enumerate(_formulas):
        _name = os.path.splitext(os.path.basename(_formula))[0]
        _state = _seed_state_for(_name)
        pdp.add_enforcer(
            name=_name,
            exe=INSTRLIB_EXE,
            sig=_sig_for(_idx),
            formula=_formula,
            func=INSTRLIB_FUNC,
            state_file=_state,
        )
else:
    if len(_formulas) > 1:
        print(f"[Enforcer] Warning: multiple formulas specified but MultiPDP not available; using first formula only")
    print(f"[Enforcer] Single enforcer mode: {_formulas[0]}")
    if INSTRLIB_STATE and not os.path.isfile(INSTRLIB_STATE):
        raise RuntimeError(
            f"[Enforcer] INSTRLIB_STATE must exist for single-enforcer mode: {INSTRLIB_STATE}"
        )
    pdp = EnfGuard(
        INSTRLIB_EXE,
        _sig_for(0),
        _formulas[0],
        log_file=INSTRLIB_LOG,
        func=INSTRLIB_FUNC,
        state_file=INSTRLIB_STATE,
    )


# =========================================================================
#  PEP
# =========================================================================

suppression_handlers: dict[str | tuple[str, ...], Any] = {
    'Read':            suppress_read_handler,
    'Write':           suppress_write_handler,
    'Collect':         suppress_collect_handler,
    'Consent':         suppress_consent_handler,
    'Revoke':          suppress_revoke_handler,
    'SpecialConsent':  suppress_special_consent_handler,
    'LiftRestriction': suppress_lift_restriction_handler,
}

causation_handlers: dict[str | tuple[str, ...], Any] = {
    'Delete':                delete_handler,
    'Rectify':               rectify_handler,
    'Declaration':           declaration_handler,
    'HasText':               has_text_handler,
    'Contains':              contains_handler,
    'ContainsData':          contains_data_handler,
    'Inform':                inform_handler,
    'ActivityRecord':        activity_record_handler,
    'NotifyErasure':         notify_erasure_handler,
    'NotifyRectification':   notify_rectification_handler,
    'NotifyRestriction':     notify_restriction_handler,
    'PersonalDataCopy':      personal_data_copy_handler,
    'SendFile':              send_file_handler,
    'RequestResponse':       request_response_handler,
    'DailyErasureReview':    daily_erasure_review_handler,
    'IsPortabilityRequest':  is_portability_request_handler,
    'IsStatutoryContractualRequirement': noop_handler,
    'IsLastResortTransfer':  noop_handler,
    'IsConsentRequest':      noop_handler,
    'NoteCategory':          noop_handler,
    'NoteCriteria':          noop_handler,
    'NoteDS':                noop_handler,
    'NoteData':              noop_handler,
    'NoteEntity':            noop_handler,
    'NoteInterest':          noop_handler,
    'NoteLegalBasis':        noop_handler,
    'NotePurpose':           noop_handler,
    'NoteRequest':           noop_handler,
    'NoteSpan':              noop_handler,
}


# =========================================================================
#  INSTRUMENTATION MAPPING
# =========================================================================

def _special_category_events(data_id: str, owner: str) -> list:
    """If the object identified by data_id has special categories, return IsSpecialData events."""
    evts = []
    try:
        # model_field, oid = data_id.rsplit(':', 1)
        # model_name = model_field.split('.')[0]
        model_name, oid = data_id.split(':')
        if model_name in ('Twit', 'Reply', 'DirectMessage'):
            from twitt.models import Twit, Reply, DirectMessage
            model_map = {'Twit': Twit, 'Reply': Reply, 'DirectMessage': DirectMessage}
            cls = model_map[model_name]
            obj = cls.objects.filter(pk=oid).values_list('special_categories', flat=True).first()
            if obj:
                for cat in obj:
                    evts.append(Event('IsSpecialData', data_id, cat))
    except Exception:
        pass
    return evts


def read_mapping(action):
    c, f, oid, caller, owner, purpose = (str(a) for a in action.args[:6])
    # did = f"{c}.{f}:{oid}"
    did = f"{c}:{oid}"
    evts = [Event('Read', did, owner, f"view_{c}", purpose, caller),
            Event('PersonalData', did, owner)]
    evts.extend(_special_category_events(did, owner))
    return evts


def write_mapping(action):
    c, f, oid, caller, _val, owner, purpose = (str(a) for a in action.args[:7])
    # did = f"{c}.{f}:{oid}"
    did = f"{c}:{oid}"
    aid = f"edit_{c}"
    evts = [Event('Write', did, owner, aid, purpose, caller),
            Event('PersonalData', did, owner)]
    sp_cats = _special_category_events(did, owner)
    evts.extend(sp_cats)
    cat_names = [e.args[1] for e in sp_cats]  # extract category strings
    for p in _active_purposes_for_special(owner, cat_names):
        evts.append(Event('Collect', aid, did, owner, p))
    # Simulate sharing page-visit data with the analytics provider
    if purpose == 'statistics' and c == 'PageVisit':
        evts.append(Event('Send', 'Analytics, Inc.', did))
        print(f"[GDPR] Send → entity=Analytics, Inc.  data={did}", flush=True)
    return evts


def input_mapping(action):
    v, k, val, caller = (str(a) for a in action.args[:4])

    # ── Cookie Consent ──
    if v == 'SetCookieConsentView':
        if k == 'accept' and val == 'true':
            return Event('Consent', caller, 'personalized_ad')
        if k == 'decline' and val == 'true':
            return Event('Revoke', caller, 'personalized_ad')

    # ── Delete All ──
    if v == 'DeleteAllView' and k == 'delete' and val == 'true':
        return Event('IsErasureRequest', _generate_id(), f'User:all:{caller}')

    # ── Consent Management ──
    if v == 'ConsentManagementView':
        if k == 'give_consent':  return Event('Consent', caller, val)
        if k == 'revoke_consent': return Event('Revoke', caller, val)

    # ── Special Consent ──
    if v == 'SpecialConsentView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r: return Event('SpecialConsent', caller,
                           r.POST.get('purpose', ''), r.POST.get('special_category', ''))
        
    if v == 'SpecialConsentView' and k == 'revoke':
        r = _get_request()
        if r:
            purpose = r.POST.get('purpose', '')
            sp_cat = r.POST.get('special_category', '')
            return [Event('Revoke', caller, purpose),
                    Event('SpecialRevoke', caller, purpose, sp_cat)]

    # ── Request Access (+ Portability) ──
    if v == 'RequestAccessView' and k == 'submit' and val == 'true':
        r = _get_request()
        rid = r.POST.get('gdpr_request_id', _generate_id()) if r else _generate_id()
        evts = [Event('RequestAccess', caller, rid)]
        nc = r.POST.get('new_controller', '').strip() if r else ''
        if nc:
            evts.append(Event('IsPortabilityRequest', rid))
            evts.append(Event('SpecifiesNewController', rid, nc))
        return evts

    # ── Request Rectification ──
    if v == 'RequestRectificationView' and k == 'new_data':
        r = _get_request()
        if r:
            rid = r.POST.get('gdpr_request_id', _generate_id())
            field = r.POST.get('field', '')
            object_id = r.POST.get('object_id', '')
            data_id = f"{field}:{object_id}"
            new_data = r.POST.get('new_data', '')
            return Event('RequestRectification', caller, data_id, new_data, rid)

    # ── Contest Accuracy + Restriction ──
    if v == 'ContestAccuracyView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r:
            rid = r.POST.get('gdpr_request_id', _generate_id())
            data_id = r.POST.get('data_id', '')
            new_data = r.POST.get('new_data', '')
            purpose = r.POST.get('purpose', '')
            return [Event('ContestAccuracy', caller, data_id, new_data),
                    Event('IsRestrictionRequest', '', data_id, purpose)]

    # ── Request Objection ──
    if v == 'RequestObjectionView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r:
            did = f"objection_{_generate_id()}"
            rid = r.POST.get('gdpr_request_id', _generate_id())
            return [Event('Declaration', did),
                    Event('HasText', did, r.POST.get('reason', '')),
                    Event('RequestObjection', caller, r.POST.get('purpose', ''), did, rid)]

    # ── Request Erasure ──
    if v == 'RequestErasureView' and k == 'gdpr_request_id':
        r = _get_request()
        print(r.POST)
        if r:
            from twitt.forms import ErasureForm
            form = ErasureForm(r.POST)
            if form.is_valid():
                data_id = form.get_data_id(r.user)
                rid = r.POST.get('gdpr_request_id', _generate_id())
                return Event('RequestErasure', caller, data_id, rid)
        
    # ── Request Recipient Info ──
    if v == 'RequestRecipientInfoView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r:
            rid = r.POST.get('gdpr_request_id', _generate_id())
            return Event('RequestRecipientInformation', caller, rid)

    # ── Signup ──
    if v == 'SignUpView' and k == 'username':
        u = val
        fields = ['User.username', 'User.first_name', 'User.last_name']
        purposes = _active_purposes(u)  # new user → fallback ['service']
        evts = [
            Event('AcceptDataUsage', u),
            Event('Consent', u, 'service'),
        ]
        for f in fields:
            did = f'{f}:{u}'
            evts.append(Event('PersonalData', did, u))
            for p in purposes:
                evts.append(Event('Collect', 'register', did, u, p))
        return evts

    # ── Post Twit ──
    if v == 'PostTwitView' and k == 'content':
        r = _get_request()
        tid = r.POST.get('twit_uid', _generate_id()) if r else _generate_id()
        # did = f'Twit.content:{tid}'
        did = f'Twit:{tid}'
        evts = [Event('PersonalData', did, caller)]
        from twitt.classifier import classify_text
        cats = classify_text(val)
        for cat in cats:
            evts.append(Event('IsSpecialData', did, cat))
        for p in _active_purposes_for_special(caller, cats):
            evts.append(Event('Collect', 'post_twit', did, caller, p))
        return evts

    # ── Follow User ──
    if v == 'FollowUserView' and k == 'pk':
        # did = f'Follow.following:{caller}_{val}'
        did = f'Follow:{caller}_{val}'
        evts = [Event('PersonalData', did, caller)]
        for p in _active_purposes(caller):
            evts.append(Event('Collect', 'follow', did, caller, p))
        return evts

    # ── Admin Claim ──
    if v == 'AdminClaimView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r:
            ct   = r.POST.get('claim_type', '')
            act  = r.POST.get('activity', '')
            did  = r.POST.get('data_id', '')
            ent  = r.POST.get('entity', '')
            purp = r.POST.get('purpose', '')
            det  = r.POST.get('detail', '')
            det2 = r.POST.get('detail2', '')
            m = {
                'judicial':                    lambda: Event('IsNecessaryForJudicialClaims', act),
                'legal_obligation':            lambda: Event('IsNecessaryForLegalObligation', act, det),
                'public_interest':             lambda: Event('IsNecessaryForPublicInterest', act, det),
                'important_public_interest':   lambda: Event('IsNecessaryForImportantPublicInterest', act, det),
                'medical':                     lambda: Event('IsNecessaryForSpecialMedicalReasons', act),
                'substantial_public_interest': lambda: Event('IsNecessaryForSubstantialPublicInterest', act),
                'vital_interests':             lambda: Event('IsNecessaryForVitalInterests', act, ent, det),
                'protection_of_rights':        lambda: Event('IsNecessaryForProtectionOfRights', act, ent),
                'data_category':               lambda: Event('HasCategory', did, det),
                'intended_recipient':          lambda: Event('HasIntendedRecipient', did, ent),
                'health_related':              lambda: Event('IsHealthRelated', det),
                'special_data':                lambda: Event('IsSpecialData', did, det),
                'criminal_data':               lambda: Event('RelatesToCriminalConvictionsOrOffences', did),
                'administrative_arrangement':  lambda: Event('IsAdministrativeArrangement',
                                                             int(det or 0), int(det2 or 0),
                                                             int(r.POST.get('int_field3', 0))),
                'contractual_clauses':         lambda: Event('IsContractualClauses',
                                                             int(det or 0), ent, purp, det2,
                                                             r.POST.get('extra1', ''),
                                                             int(r.POST.get('int_field3', 0))),
            }
            h = m.get(ct)
            if h: return h()

    # ── Admin Lift Restriction ──
    if v == 'AdminLiftRestrictionView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r: return Event('LiftRestriction', 'GDPRSocial, Inc.',
                           r.POST.get('data_id', ''), r.POST.get('request_id', ''))

    # ── Admin Send Data ──
    if v == 'AdminSendDataView' and k == 'submit' and val == 'true':
        r = _get_request()
        if r: return Event('Send', r.POST.get('entity', ''), r.POST.get('data_id', ''))

    return None


def execute_mapping(action):
    method = str(action.args[1])
    owner  = str(action.args[4])
    if method == 'delete_data':
        return Event('Delete', f'User:all:{owner}')
    return None


instrumentation_mapping = InstrumentationMapping({
    'read':    read_mapping,
    'write':   write_mapping,
    'input':   input_mapping,
    'execute': execute_mapping,
})

pep = PEP(
    suppression_handlers    = suppression_handlers,
    causation_handlers      = causation_handlers,
    instrumentation_mapping = instrumentation_mapping,
)

# =========================================================================
#  LOGGER
# =========================================================================

if _MULTI_PDP_AVAILABLE and _MULTI_LOGGER_AVAILABLE and isinstance(pdp, MultiPDP):
    logger = MultiLogger(pep, schema, pdp)
else:
    logger = Logger(pep, schema, pdp)
