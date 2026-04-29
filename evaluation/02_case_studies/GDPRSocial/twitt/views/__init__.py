"""
twitt.views package – re-exports every view so that existing import paths
like ``twitt.views.HomeView`` or ``twitt.views.SetCookieConsentView``
continue to work.  This is critical because:

  * ``Twitter/urls.py`` ``to_instrument`` set uses ``"twitt.views.XxxView"``
  * ``twitt/enforcer.py`` ``input_mapping`` matches on view __qualname__
  * ``twitt/urls.py`` imports directly from ``twitt.views``
"""

# -- social ---------------------------------------------------------------
from twitt.views.social import (                       # noqa: F401
    LoginRequiredMixin,
    StaffRequiredMixin,
    HomeView,
    FeedMoreView,
    SignUpView,
    custom_logout,
    AccountProfileView,
    FollowUserView,
    FollowListView,
    MyTwitsView,
    PostTwitView,
    EditTwitView,
    delete_twit,
    TwitDetailView,
    LikeTwitView,
    UnlikeTwitView,
    PostReplyView,
    RepostTwitView,
    InboxView,
    SendMessageView,
)

# -- gdpr -----------------------------------------------------------------
from twitt.views.gdpr import (                         # noqa: F401
    GDPRDashboardView,
    ConsentManagementView,
    SpecialConsentView,
    RequestAccessView,
    RequestRectificationView,
    ContestAccuracyView,
    RequestObjectionView,
    RequestErasureView,
    RequestPortabilityView,
    RequestRestrictionView,
    RequestRecipientInfoView,
    MyRequestsView,
    NotificationsView,
    AdminDashboardView,
    AdminClaimView,
    AdminLiftRestrictionView,
    AdminSendDataView,
    AdminRequestsView,
)

# -- ads ------------------------------------------------------------------
from twitt.views.ads import (                          # noqa: F401
    AdListView,
    AdCreateView,
    AdClickView,
)

# -- statistics ------------------------------------------------------------
from twitt.views.statistics import (                   # noqa: F401
    UserStatsView,
    AdminStatsView,
    AdAnalyticsView,
)
