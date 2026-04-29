"""
twitt.models package — re-exports every model so that existing imports like
``from twitt.models import User`` continue to work, and Django's migration
framework sees all models under the 'twitt' app_label.
"""

# -- Social / core (instrumented) -----------------------------------------
from twitt.models.social import (                       # noqa: F401
    User,
    Follow,
    Twit,
    Like,
    Reply,
    Repost,
    DirectMessage,
    info_user,
    info_follow,
    info_twit,
)

# -- GDPR -----------------------------------------------------------------
from twitt.models.gdpr import (                         # noqa: F401
    GDPRRequest,
    DataRestriction,
    AdminClaim,
    GDPRNotification,
    ActivityLog,
    ConsentRecord,
    _gdpr_id,
)

# -- Advertising -----------------------------------------------------------
from twitt.models.ads import (                          # noqa: F401
    Ad,
    AdImpression,
    AdClick,
)

# -- Statistics / analytics ------------------------------------------------
from twitt.models.statistics import (                   # noqa: F401
    PageVisit,
)
