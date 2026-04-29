"""
Statistics views: user-level and admin-level analytics dashboards.
"""
from datetime import timedelta

from django.db.models import Count, Sum, Avg, Q, F
from django.db.models.functions import TruncDate
from django.template.response import TemplateResponse
from django.utils.timezone import now
from django.views import View
from django.views.generic import TemplateView

from instrlib.django.purposes import with_purpose

from twitt.models import (
    User, Twit, Follow, Like, Reply, Repost, DirectMessage,
    Ad, AdImpression, AdClick, PageVisit,
)
from twitt.views.social import LoginRequiredMixin, StaffRequiredMixin


class UserStatsView(LoginRequiredMixin, TemplateView):
    """Personal statistics dashboard for a user."""
    template_name = 'statistics/user_stats.html'

    @with_purpose('statistics')
    def get_context_data(self, **kwargs):
        user = self.request.user
        thirty_days_ago = now() - timedelta(days=30)
        seven_days_ago = now() - timedelta(days=7)

        twit_count = Twit.objects.filter(author=user).count()
        twit_last_30 = Twit.objects.filter(author=user, posted_on__gte=thirty_days_ago).count()
        twit_last_7 = Twit.objects.filter(author=user, posted_on__gte=seven_days_ago).count()
        followers_count = Follow.objects.filter(following=user).count()
        following_count = Follow.objects.filter(follower=user).count()
        likes_received = Like.objects.filter(twit__author=user).count()
        likes_given = Like.objects.filter(user=user).count()
        replies_received = Reply.objects.filter(parent__author=user).count()
        replies_given = Reply.objects.filter(author=user).count()
        reposts_received = Repost.objects.filter(original__author=user).count()
        dm_sent = DirectMessage.objects.filter(sender=user).count()
        dm_received = DirectMessage.objects.filter(recipient=user).count()

        # Top twits by like count
        top_twits = (
            Twit.objects.filter(author=user)
            .annotate(like_count=Count('likes'))
            .order_by('-like_count')[:5]
        )

        # Daily activity (last 30 days)
        daily_posts = list(
            Twit.objects.filter(author=user, posted_on__gte=thirty_days_ago)
            .annotate(day=TruncDate('posted_on'))
            .values('day')
            .annotate(count=Count('id'))
            .order_by('day')
        )

        # Pages the user visited most (if they consented)
        my_top_pages = list(
            PageVisit.objects.filter(user=user, created_at__gte=thirty_days_ago)
            .values('path')
            .annotate(count=Count('id'))
            .order_by('-count')[:10]
        )

        return {
            'twit_count': twit_count,
            'twit_last_30': twit_last_30,
            'twit_last_7': twit_last_7,
            'followers_count': followers_count,
            'following_count': following_count,
            'likes_received': likes_received,
            'likes_given': likes_given,
            'replies_received': replies_received,
            'replies_given': replies_given,
            'reposts_received': reposts_received,
            'dm_sent': dm_sent,
            'dm_received': dm_received,
            'top_twits': top_twits,
            'daily_posts': daily_posts,
            'my_top_pages': my_top_pages,
        }


class AdminStatsView(StaffRequiredMixin, TemplateView):
    """Admin analytics dashboard with platform-wide statistics."""
    template_name = 'statistics/admin_stats.html'

    @with_purpose('statistics')
    def get_context_data(self, **kwargs):
        thirty_days_ago = now() - timedelta(days=30)
        seven_days_ago = now() - timedelta(days=7)

        total_users = User.objects.count()
        new_users_30d = User.objects.filter(date_joined__gte=thirty_days_ago).count()
        total_twits = Twit.objects.count()
        twits_30d = Twit.objects.filter(posted_on__gte=thirty_days_ago).count()
        total_likes = Like.objects.count()
        total_replies = Reply.objects.count()
        total_reposts = Repost.objects.count()
        total_dms = DirectMessage.objects.count()

        # ── Ad metrics (aggregate) ──────────────────────────────────
        total_ads = Ad.objects.filter(is_active=True).count()
        impressions_30d = AdImpression.objects.filter(created_at__gte=thirty_days_ago).count()
        clicks_30d = AdClick.objects.filter(created_at__gte=thirty_days_ago).count()
        ctr = (clicks_30d / impressions_30d * 100) if impressions_30d > 0 else 0.0

        # ── Per-ad breakdown ────────────────────────────────────────
        per_ad_stats = (
            Ad.objects.filter(is_active=True)
            .annotate(
                imp_count=Count('impressions', filter=Q(impressions__created_at__gte=thirty_days_ago)),
                click_count=Count('clicks', filter=Q(clicks__created_at__gte=thirty_days_ago)),
                unique_impressions=Count('impressions__user', distinct=True,
                    filter=Q(impressions__created_at__gte=thirty_days_ago)),
                unique_clicks=Count('clicks__user', distinct=True,
                    filter=Q(clicks__created_at__gte=thirty_days_ago)),
            )
            .order_by('-imp_count')
        )
        # Compute CTR & conv_rate per ad in Python (avoid DB division)
        ad_rows = []
        for ad in per_ad_stats:
            ad.ad_ctr = round(ad.click_count / ad.imp_count * 100, 2) if ad.imp_count else 0.0
            ad_rows.append(ad)

        # ── Page-visit analytics ────────────────────────────────────
        visits_30d = PageVisit.objects.filter(created_at__gte=thirty_days_ago).count()
        visits_7d = PageVisit.objects.filter(created_at__gte=seven_days_ago).count()
        unique_visitors_30d = (
            PageVisit.objects.filter(created_at__gte=thirty_days_ago)
            .values('session_key').distinct().count()
        )
        avg_response_time = (
            PageVisit.objects.filter(created_at__gte=thirty_days_ago)
            .aggregate(avg=Avg('response_time_ms'))['avg'] or 0
        )

        top_pages = (
            PageVisit.objects.filter(created_at__gte=thirty_days_ago)
            .values('path')
            .annotate(
                total_hits=Count('id'),
                unique_users=Count('user', distinct=True),
                avg_ms=Avg('response_time_ms'),
            )
            .order_by('-total_hits')[:15]
        )

        # Top visitors (by page visits)
        top_visitors = (
            PageVisit.objects.filter(created_at__gte=thirty_days_ago, user__isnull=False)
            .values('user__username')
            .annotate(visit_count=Count('id'))
            .order_by('-visit_count')[:10]
        )

        # Daily visits trend
        daily_visits = list(
            PageVisit.objects.filter(created_at__gte=thirty_days_ago)
            .annotate(day=TruncDate('created_at'))
            .values('day')
            .annotate(count=Count('id'))
            .order_by('day')
        )

        # Most active users (by twits)
        top_posters = (
            User.objects.annotate(post_count=Count('twit'))
            .order_by('-post_count')[:10]
        )

        return {
            'total_users': total_users,
            'new_users_30d': new_users_30d,
            'total_twits': total_twits,
            'twits_30d': twits_30d,
            'total_likes': total_likes,
            'total_replies': total_replies,
            'total_reposts': total_reposts,
            'total_dms': total_dms,
            # Ad aggregates
            'total_ads': total_ads,
            'impressions_30d': impressions_30d,
            'clicks_30d': clicks_30d,
            'ctr': round(ctr, 2),
            # Per-ad table
            'ad_rows': ad_rows,
            # Page visits
            'visits_30d': visits_30d,
            'visits_7d': visits_7d,
            'unique_visitors_30d': unique_visitors_30d,
            'avg_response_time': round(avg_response_time),
            'top_pages': top_pages,
            'top_visitors': top_visitors,
            'daily_visits': daily_visits,
            'top_posters': top_posters,
        }


class AdAnalyticsView(StaffRequiredMixin, View):
    """Detailed per-ad analytics page."""
    template_name = 'statistics/ad_analytics.html'

    @with_purpose('statistics')
    def get(self, request, pk, *args, **kwargs):
        from django.shortcuts import get_object_or_404
        ad = get_object_or_404(Ad, pk=pk)
        thirty_days_ago = now() - timedelta(days=30)

        impressions = AdImpression.objects.filter(ad=ad, created_at__gte=thirty_days_ago)
        clicks = AdClick.objects.filter(ad=ad, created_at__gte=thirty_days_ago)

        imp_total = impressions.count()
        click_total = clicks.count()
        unique_imp = impressions.values('user').distinct().count()
        unique_click = clicks.values('user').distinct().count()
        ctr = round(click_total / imp_total * 100, 2) if imp_total else 0.0

        # Daily breakdown
        daily_imp = list(
            impressions.annotate(day=TruncDate('created_at'))
            .values('day').annotate(count=Count('id')).order_by('day')
        )
        daily_clicks = list(
            clicks.annotate(day=TruncDate('created_at'))
            .values('day').annotate(count=Count('id')).order_by('day')
        )

        return TemplateResponse(request, self.template_name, {
            'ad': ad,
            'imp_total': imp_total,
            'click_total': click_total,
            'unique_imp': unique_imp,
            'unique_click': unique_click,
            'ctr': ctr,
            'daily_imp': daily_imp,
            'daily_clicks': daily_clicks,
        })
