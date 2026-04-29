"""
Ads views: TF-IDF embedding-based recommender, ad listing, click tracking.
"""
import json
import logging

import numpy as np
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity

from django.http import JsonResponse
from django.template.response import TemplateResponse
from django.views import View
from django.views.generic import TemplateView

from instrlib.django.custom_http import redirect
from instrlib.django.purposes import with_purpose

from twitt.models import Ad, AdImpression, AdClick, Twit, User
from twitt.forms import AdForm
from twitt.views.social import LoginRequiredMixin, StaffRequiredMixin

logger = logging.getLogger(__name__)


# =========================================================================
#  TF-IDF embedding helpers
# =========================================================================

# Module-level vectorizer fitted on demand and cached.
_vectorizer: TfidfVectorizer | None = None
_vectorizer_fitted_on: int = 0  # number of ads when last fitted


def _get_vectorizer(force_refit: bool = False) -> TfidfVectorizer:
    """Return a TF-IDF vectorizer fitted on all ad texts and recent twits.

    We refit when the number of active ads changes (cheap heuristic to pick
    up new vocabulary).
    """
    global _vectorizer, _vectorizer_fitted_on

    ad_count = Ad.objects.filter(is_active=True).count()
    if _vectorizer is not None and not force_refit and ad_count == _vectorizer_fitted_on:
        return _vectorizer

    # Collect a corpus: all ad texts + a sample of recent twits for richer vocabulary
    corpus: list[str] = []
    for ad in Ad.objects.filter(is_active=True):
        corpus.append(f"{ad.title} {ad.body}")
    recent_twits = Twit.objects.order_by('-posted_on').values_list('content', flat=True)[:500]
    corpus.extend([t for t in recent_twits if t])

    if not corpus:
        _vectorizer = TfidfVectorizer()
        _vectorizer.fit(["placeholder"])
        _vectorizer_fitted_on = ad_count
        return _vectorizer

    _vectorizer = TfidfVectorizer(
        max_features=5000,
        stop_words='english',
        ngram_range=(1, 2),
        sublinear_tf=True,
    )
    _vectorizer.fit(corpus)
    _vectorizer_fitted_on = ad_count
    return _vectorizer


def _text_to_embedding(text: str) -> list[float]:
    """Transform a string into a TF-IDF vector (stored as a plain list)."""
    vec = _get_vectorizer()
    matrix = vec.transform([text])
    return matrix.toarray()[0].tolist()


def _embedding_to_array(embedding) -> np.ndarray:
    """Convert a stored JSON embedding (list) to a numpy array."""
    if embedding is None:
        return np.zeros(0)
    if isinstance(embedding, list):
        return np.array(embedding, dtype=np.float64)
    # Legacy BOW dict — fall back to zero vector of correct size
    vec = _get_vectorizer()
    return np.zeros(len(vec.get_feature_names_out()))


def _user_profile_embedding(user) -> np.ndarray:
    """Build a user profile by averaging TF-IDF vectors of their recent twits."""
    twits = Twit.objects.filter(author=user).order_by('-posted_on')[:30]
    twits = Twit.filter_check(twits)
    texts = [t.content for t in twits if t.content]
    if not texts:
        vec = _get_vectorizer()
        return np.zeros(len(vec.get_feature_names_out()))
    vec = _get_vectorizer()
    matrix = vec.transform(texts)
    return np.asarray(matrix.mean(axis=0)).flatten()


def recommend_ads(user, n: int = 3) -> list[Ad]:
    """Return top-n ads ranked by cosine similarity to the user's TF-IDF profile."""
    active_ads = list(Ad.objects.filter(is_active=True))
    if not active_ads:
        return []

    profile = _user_profile_embedding(user)
    if profile.size == 0:
        return active_ads[:n]

    scored: list[tuple[Ad, float]] = []
    for ad in active_ads:
        ad_emb = _embedding_to_array(ad.embedding)
        if ad_emb.size == 0 or ad_emb.size != profile.size:
            # Recompute embedding for this ad (legacy or dimension mismatch)
            ad_emb = np.array(_text_to_embedding(f"{ad.title} {ad.body}"))
            ad.embedding = ad_emb.tolist()
            ad.save(update_fields=['embedding'])
        sim = cosine_similarity(profile.reshape(1, -1), ad_emb.reshape(1, -1))[0, 0]
        scored.append((ad, float(sim)))

    scored.sort(key=lambda x: x[1], reverse=True)
    return [ad for ad, _ in scored[:n]]


# =========================================================================
#  Views
# =========================================================================

class AdListView(LoginRequiredMixin, TemplateView):
    """Show recommended ads to the user."""
    template_name = 'ads/ad_list.html'

    @with_purpose('personalized_ad')
    def get_context_data(self, **kwargs):
        user = self.request.user
        ads = recommend_ads(user, n=5)
        # Record impressions
        for ad in ads:
            try:
                AdImpression.objects.create(ad=ad, user=user)
            except Exception as e:
                pass  # Don't break the user experience if logging fails
        return {'ads': ads}


class AdCreateView(StaffRequiredMixin, View):
    """Staff can create a new ad."""
    template_name = 'ads/ad_create.html'

    @with_purpose('personalized_ad')
    def get(self, request, *args, **kwargs):
        return TemplateResponse(request, self.template_name, {'form': AdForm()})

    @with_purpose('personalized_ad')
    def post(self, request, *args, **kwargs):
        form = AdForm(request.POST)
        if form.is_valid():
            ad = form.save(commit=False)
            ad.created_by = request.user
            # Compute TF-IDF embedding from title+body
            ad.embedding = _text_to_embedding(f"{ad.title} {ad.body}")
            ad.save()
            return redirect('ad_list')
        return TemplateResponse(request, self.template_name, {'form': form})


class AdClickView(LoginRequiredMixin, View):
    """Record an ad click and redirect to the ad URL."""

    @with_purpose('personalized_ad')
    def get(self, request, pk, *args, **kwargs):
        from django.shortcuts import get_object_or_404
        ad = get_object_or_404(Ad, pk=pk)
        AdClick.objects.create(ad=ad, user=request.user)
        if ad.url:
            from django.shortcuts import redirect as dj_redirect
            return dj_redirect(ad.url)
        return redirect('ad_list')
