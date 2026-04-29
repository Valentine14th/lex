"""
twitt.forms package — re-exports every form so that existing imports like
``from twitt.forms import SignUpForm`` continue to work.
"""

# -- Social ----------------------------------------------------------------
from twitt.forms.social import (                        # noqa: F401
    SignUpForm,
    TwitForm,
    ReplyForm,
    RepostForm,
    DirectMessageForm,
)

# -- GDPR ------------------------------------------------------------------
from twitt.forms.gdpr import (                          # noqa: F401
    PURPOSE_CHOICES,
    SPECIAL_CATEGORY_CHOICES,
    CLAIM_TYPE_CHOICES,
    SpecialConsentForm,
    RectificationForm,
    ContestAccuracyForm,
    ObjectionForm,
    ErasureForm,
    PortabilityForm,
    RecipientInfoForm,
    AdminClaimForm,
    AdminLiftRestrictionForm,
    AdminSendDataForm,
)

# -- Advertising -----------------------------------------------------------
from twitt.forms.ads import (                           # noqa: F401
    AdForm,
)
