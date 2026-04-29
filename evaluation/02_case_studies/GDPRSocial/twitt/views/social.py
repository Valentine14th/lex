"""
Social views: feed, posts, follows, likes, replies, reposts, direct messages.
"""
import uuid

from django.contrib.auth import logout
from django.contrib.auth.decorators import login_required
from django.http import Http404, HttpResponse, HttpResponseBadRequest, JsonResponse
from django.shortcuts import get_object_or_404
from django.template.response import TemplateResponse
from django.utils.decorators import method_decorator
from django.views import View
from django.views.generic import TemplateView, CreateView, FormView, UpdateView

from instrlib.django.purposes import with_purpose

from django.db.models import Count

from twitt.models import (Twit, Follow, User, Like, Reply, Repost, DirectMessage,
                         ConsentRecord, AdImpression)
from twitt.forms import (SignUpForm, TwitForm, ReplyForm, RepostForm, DirectMessageForm)
from instrlib.django.custom_http import redirect, render


# =========================================================================
#  Mixins
# =========================================================================

class LoginRequiredMixin:
    @method_decorator(login_required)
    def dispatch(self, request, *args, **kwargs):
        return super().dispatch(request, *args, **kwargs)


class StaffRequiredMixin:
    @method_decorator(login_required)
    def dispatch(self, request, *args, **kwargs):
        if not request.user.is_staff:
            return TemplateResponse(request, 'error_page.html',
                                    {'error': 'Staff access required.'}, status=403)
        return super().dispatch(request, *args, **kwargs)


# =========================================================================
#  Home / Feed
# =========================================================================

FEED_PAGE_SIZE = 10


def _feed_queryset(user):
    """Base queryset for a user's home feed."""
    followed_users = list(
        Follow.objects.filter(follower=user).values_list('following', flat=True))
    followed_users.append(user.pk)
    return (
        Twit.objects.filter(author__in=followed_users)
        .annotate(
            like_count=Count('likes', distinct=True),
            reply_count=Count('replies', distinct=True),
            repost_count=Count('reposts', distinct=True),
        )
        .order_by('-posted_on')
    )


class HomeView(LoginRequiredMixin, TemplateView):
    template_name = 'social/index.html'

    @with_purpose('statistics')
    def record_ad_impressions(self, ads):
        """Record ad impressions for the given list of ads."""
        for ad in ads:
            try:
                AdImpression.objects.create(ad=ad, user=self.request.user)
            except Exception as e:
                print(f"Cannot record ad impression for ad {ad.pk}: {e}")

    @with_purpose('personalized_ad')
    def generate_advertisement(self):
        """Return a list of recommended Ad objects using the TF-IDF recommender."""
        from twitt.views.ads import recommend_ads
        recommended_ads = recommend_ads(self.request.user, n=3)
        self.record_ad_impressions(recommended_ads)
        return recommended_ads

    def get_context_data(self, **kwargs):
        qs = _feed_queryset(self.request.user)
        twits = Twit.filter_check(qs[:FEED_PAGE_SIZE + 1])
        has_more = len(twits) > FEED_PAGE_SIZE
        twits = twits[:FEED_PAGE_SIZE]

        # Only show personalised ads when the user has given consent
        has_ad_consent = ConsentRecord.objects.filter(
            user=self.request.user, purpose='personalized_ad', is_active=True
        ).exists()
        recommended_ads = []
        if has_ad_consent:
            recommended_ads = self.generate_advertisement()

        return {
            'title': 'Your GDPRSocial Home',
            'twits': twits,
            'has_more': has_more,
            'post_form': TwitForm,
            'twit_uid': uuid.uuid4(),
            'recommended_ads': recommended_ads,
            'has_ad_consent': has_ad_consent,
        }


class FeedMoreView(LoginRequiredMixin, View):
    """Return a page of tweets as an HTML fragment for infinite scroll."""

    def get(self, request):
        offset = int(request.GET.get('offset', 0))
        qs = _feed_queryset(request.user)
        twits = Twit.filter_check(qs[offset:offset + FEED_PAGE_SIZE + 1])
        has_more = len(twits) > FEED_PAGE_SIZE
        twits = twits[:FEED_PAGE_SIZE]
        return TemplateResponse(request, 'social/_tweet_list.html', {
            'twits': twits,
            'has_more': has_more,
        })


# =========================================================================
#  Auth
# =========================================================================

class SignUpView(FormView):
    template_name = 'registration/signup.html'

    def get(self, request, *args, **kwargs):
        if request.user.is_authenticated:
            return redirect('/')
        return TemplateResponse(request, self.template_name, {'form': SignUpForm()})

    def post(self, request, *args, **kwargs):
        form = SignUpForm(request.POST)
        if form.is_valid():
            user = form.save()
            # Create consent records based on signup preferences
            if form.cleaned_data.get('consent_personalized_ad'):
                ConsentRecord.objects.create(
                    user=user, purpose='personalized_ad', is_active=True)
            if form.cleaned_data.get('consent_statistics'):
                ConsentRecord.objects.create(
                    user=user, purpose='statistics', is_active=True)
            return redirect('login')
        return TemplateResponse(request, self.template_name, {'form': form})


def custom_logout(request):
    logout(request)
    return redirect('/')


# =========================================================================
#  Profile & Follow
# =========================================================================

class AccountProfileView(TemplateView):
    template_name = 'social/account_profile.html'

    def get(self, request, *args, **kwargs):
        return TemplateResponse(request, self.template_name, {'user': request.user})


class FollowUserView(LoginRequiredMixin, CreateView):
    def get(self, request, *args, **kwargs):
        following_list = list(
            Follow.objects.filter(follower=request.user).values_list('following__pk', flat=True))
        following_list.append(request.user.pk)
        users = User.objects.exclude(pk__in=following_list)
        return TemplateResponse(request, 'social/follow.html', {'user_list': users})

    def post(self, request, *args, **kwargs):
        user = get_object_or_404(User, pk=request.POST.get('pk'))
        Follow(follower=request.user, following=user).save()
        return redirect('/')


class FollowListView(LoginRequiredMixin, TemplateView):
    template_name = 'social/following.html'

    def get_context_data(self, **kwargs):
        ids = Follow.objects.filter(follower=self.request.user).values_list('following', flat=True)
        return {'following_list': User.objects.filter(pk__in=ids)}


# =========================================================================
#  Twits – CRUD
# =========================================================================

class MyTwitsView(LoginRequiredMixin, TemplateView):
    template_name = 'social/my_twits.html'

    def get_context_data(self, **kwargs):
        return {'twit_list': Twit.objects.filter(author=self.request.user).order_by('-posted_on')}


class PostTwitView(LoginRequiredMixin, FormView):
    def get(self, request, *args, **kwargs):
        raise Http404

    def post(self, request, *args, **kwargs):
        twit_uid = request.POST.get('twit_uid')
        pk = uuid.UUID(twit_uid) if twit_uid else uuid.uuid4()
        instance = Twit(id=pk, author=request.user)
        twit_form = TwitForm(request.POST, instance=instance)
        if twit_form.is_valid():
            twit_form.save()
        else:
            print(twit_form.errors)
        return redirect('/')


class EditTwitView(LoginRequiredMixin, UpdateView):
    template_name = 'social/edit_twit.html'

    def get(self, request, *args, **kwargs):
        twit = self._get_twit(request, **kwargs)
        if isinstance(twit, HttpResponse):
            return twit
        form = TwitForm(instance=twit)
        return TemplateResponse(request, self.template_name, {'form': form})

    def post(self, request, *args, **kwargs):
        twit = self._get_twit(request, **kwargs)
        if isinstance(twit, HttpResponse):
            return twit
        form = TwitForm(request.POST, instance=twit)
        if form.is_valid():
            form.save()
            return redirect('/')
        return TemplateResponse(request, self.template_name, {'form': form})

    def _get_twit(self, request, **kwargs):
        twit = get_object_or_404(Twit, pk=kwargs.get('pk'))
        if twit.author != request.user:
            return redirect('/')
        return twit


@login_required
def delete_twit(request, pk):
    return redirect('/')


# =========================================================================
#  Twit detail with replies
# =========================================================================

class TwitDetailView(LoginRequiredMixin, View):
    """Show a single twit with its replies."""
    template_name = 'social/twit_detail.html'

    def get(self, request, pk, *args, **kwargs):
        twit = get_object_or_404(Twit, pk=pk)
        replies = Reply.objects.filter(parent=twit).order_by('created_at')
        reposts = Repost.objects.filter(original=twit).count()
        likes = Like.objects.filter(twit=twit).count()
        user_liked = Like.objects.filter(twit=twit, user=request.user).exists()
        return TemplateResponse(request, self.template_name, {
            'twit': twit,
            'replies': replies,
            'reply_form': ReplyForm(),
            'repost_count': reposts,
            'like_count': likes,
            'user_liked': user_liked,
        })


# =========================================================================
#  Likes
# =========================================================================

class LikeTwitView(LoginRequiredMixin, View):
    def post(self, request, pk, *args, **kwargs):
        twit = get_object_or_404(Twit, pk=pk)
        Like.objects.get_or_create(user=request.user, twit=twit)
        next_url = request.POST.get('next', '/')
        return redirect(next_url)


class UnlikeTwitView(LoginRequiredMixin, View):
    def post(self, request, pk, *args, **kwargs):
        Like.objects.filter(user=request.user, twit_id=pk).delete()
        next_url = request.POST.get('next', '/')
        return redirect(next_url)


# =========================================================================
#  Replies
# =========================================================================

class PostReplyView(LoginRequiredMixin, View):
    def post(self, request, pk, *args, **kwargs):
        twit = get_object_or_404(Twit, pk=pk)
        form = ReplyForm(request.POST)
        if form.is_valid():
            Reply.objects.create(
                parent=twit, author=request.user,
                content=form.cleaned_data['content'])
        return redirect('twit_detail', pk=pk)


# =========================================================================
#  Reposts
# =========================================================================

class RepostTwitView(LoginRequiredMixin, View):
    template_name = 'social/repost.html'

    def get(self, request, pk, *args, **kwargs):
        twit = get_object_or_404(Twit, pk=pk)
        return TemplateResponse(request, self.template_name, {
            'twit': twit, 'form': RepostForm()})

    def post(self, request, pk, *args, **kwargs):
        twit = get_object_or_404(Twit, pk=pk)
        form = RepostForm(request.POST)
        if form.is_valid():
            Repost.objects.create(
                original=twit, user=request.user,
                message=form.cleaned_data.get('message', ''))
        return redirect('/')


# =========================================================================
#  Direct Messages
# =========================================================================

class InboxView(LoginRequiredMixin, TemplateView):
    template_name = 'social/inbox.html'

    def get_context_data(self, **kwargs):
        received = DirectMessage.objects.filter(recipient=self.request.user).order_by('-created_at')[:50]
        sent = DirectMessage.objects.filter(sender=self.request.user).order_by('-created_at')[:50]
        for msg in received:
            if not msg.is_read:
                msg.is_read = True
                msg.save(update_fields=['is_read'])        
        return {'received': received, 'sent': sent}


class SendMessageView(LoginRequiredMixin, View):
    template_name = 'social/send_message.html'

    def get(self, request, *args, **kwargs):
        recipient_pk = request.GET.get('to')
        initial = {}
        if recipient_pk:
            try:
                initial['recipient'] = User.objects.get(pk=recipient_pk)
            except User.DoesNotExist:
                pass
        return TemplateResponse(request, self.template_name, {
            'form': DirectMessageForm(user=request.user),
            'initial_recipient': initial.get('recipient'),
        })

    def post(self, request, *args, **kwargs):
        form = DirectMessageForm(request.POST, user=request.user)
        if form.is_valid():
            DirectMessage.objects.create(
                sender=request.user,
                recipient=form.cleaned_data['recipient'],
                content=form.cleaned_data['content'])
            return redirect('inbox')
        return TemplateResponse(request, self.template_name, {'form': form})
