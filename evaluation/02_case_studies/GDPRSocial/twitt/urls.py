"""""""""""""""""""""""""""""""""""""""""
# @author  sonus
# @date 02 - Apr - 2016
# @copyright sonus
# GitHub http://github.com/sonus21
"""""""""""""""""""""""""""""""""""""""""

from django.urls import path, include # type: ignore

from .views import (
	# Social / core
	SignUpView, FollowUserView, custom_logout, AccountProfileView,
	PostTwitView, FollowListView, EditTwitView, HomeView, FeedMoreView, MyTwitsView,
	delete_twit,
	TwitDetailView, LikeTwitView, UnlikeTwitView, PostReplyView,
	RepostTwitView, InboxView, SendMessageView,
	# GDPR user views
	GDPRDashboardView, ConsentManagementView, SpecialConsentView,
	RequestAccessView, RequestRectificationView, ContestAccuracyView,
	RequestObjectionView, RequestErasureView, RequestPortabilityView,
	RequestRestrictionView, RequestRecipientInfoView,
	MyRequestsView, NotificationsView,
	# Admin views
	AdminDashboardView, AdminClaimView, AdminLiftRestrictionView,
	AdminSendDataView, AdminRequestsView,
	# Ads
	AdListView, AdCreateView, AdClickView,
	# Statistics
	UserStatsView, AdminStatsView, AdAnalyticsView,
)
from django.contrib.auth.views import LoginView # type: ignore

urlpatterns = [

	# ── Home ─────────────────────────────────────────────────────────
	path('', HomeView.as_view(), name='home'),
	path('feed/more/', FeedMoreView.as_view(), name='feed_more'),

	# ── Auth / Account ───────────────────────────────────────────────
	path('accounts/profile/', AccountProfileView.as_view(), name='profile'),
	path('accounts/login/', LoginView.as_view(), name='login'),
	path('accounts/signup/', SignUpView.as_view(), name='signup'),
	path('accounts/logout/', custom_logout, name='logout'),
	path('accounts/twit/', MyTwitsView.as_view(), name='my_twits'),

	# ── Twits CRUD ───────────────────────────────────────────────────
	path('post/twit/', PostTwitView.as_view(), name='post_twit'),
	path('edit/twit/<uuid:pk>/', EditTwitView.as_view(), name='edit_twit'),
	path('twit/<uuid:pk>/', TwitDetailView.as_view(), name='twit_detail'),
	path('twit/delete/<uuid:pk>/', delete_twit, name='delete_twit'),

	# ── Social interactions ──────────────────────────────────────────
	path('following/', FollowListView.as_view(), name='following_list'),
	path('search/user/', FollowUserView.as_view(), name='follow_user'),
	path('search/twit/', include('haystack.urls')),
	path('twit/<uuid:pk>/like/', LikeTwitView.as_view(), name='like_twit'),
	path('twit/<uuid:pk>/unlike/', UnlikeTwitView.as_view(), name='unlike_twit'),
	path('twit/<uuid:pk>/reply/', PostReplyView.as_view(), name='post_reply'),
	path('twit/<uuid:pk>/repost/', RepostTwitView.as_view(), name='repost_twit'),

	# ── Direct messages ──────────────────────────────────────────────
	path('messages/', InboxView.as_view(), name='inbox'),
	path('messages/send/', SendMessageView.as_view(), name='send_message'),

	# ── GDPR user-facing routes ──────────────────────────────────────
	path('gdpr/', GDPRDashboardView.as_view(), name='gdpr_dashboard'),
	path('gdpr/consent/', ConsentManagementView.as_view(), name='gdpr_consent'),
	path('gdpr/consent/special/', SpecialConsentView.as_view(), name='gdpr_special_consent'),
	path('gdpr/request/access/', RequestAccessView.as_view(), name='gdpr_request_access'),
	path('gdpr/request/rectification/', RequestRectificationView.as_view(), name='gdpr_request_rectification'),
	path('gdpr/request/contest/', ContestAccuracyView.as_view(), name='gdpr_contest_accuracy'),
	path('gdpr/request/objection/', RequestObjectionView.as_view(), name='gdpr_request_objection'),
	path('gdpr/request/erasure/', RequestErasureView.as_view(), name='gdpr_request_erasure'),
	path('gdpr/request/portability/', RequestPortabilityView.as_view(), name='gdpr_request_portability'),
	path('gdpr/request/restriction/', RequestRestrictionView.as_view(), name='gdpr_request_restriction'),
	path('gdpr/request/recipient/', RequestRecipientInfoView.as_view(), name='gdpr_request_recipient'),
	path('gdpr/requests/', MyRequestsView.as_view(), name='gdpr_my_requests'),
	path('gdpr/notifications/', NotificationsView.as_view(), name='gdpr_notifications'),

	# ── Admin / controller panel ─────────────────────────────────────
	path('controller/', AdminDashboardView.as_view(), name='admin_dashboard'),
	path('controller/claim/', AdminClaimView.as_view(), name='admin_claim'),
	path('controller/lift-restriction/', AdminLiftRestrictionView.as_view(), name='admin_lift_restriction'),
	path('controller/send-data/', AdminSendDataView.as_view(), name='admin_send_data'),
	path('controller/requests/', AdminRequestsView.as_view(), name='admin_requests'),

	# ── Ads ──────────────────────────────────────────────────────────
	path('ads/', AdListView.as_view(), name='ad_list'),
	path('ads/create/', AdCreateView.as_view(), name='ad_create'),
	path('ads/<int:pk>/click/', AdClickView.as_view(), name='ad_click'),

	# ── Statistics ───────────────────────────────────────────────────
	path('stats/', UserStatsView.as_view(), name='user_stats'),
	path('stats/admin/', AdminStatsView.as_view(), name='admin_stats'),
	path('stats/ad/<int:pk>/', AdAnalyticsView.as_view(), name='ad_analytics'),
]
