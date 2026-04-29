"""
Advertising models: Ad, AdImpression, AdClick.
"""
from django.db import models  # type: ignore
from django.utils.timezone import now  # type: ignore

from twitt.models.social import User
from instrlib.django.orm import InstrumentORM
from twitt.enforcer import logger


class Ad(models.Model):
	"""An advertisement created by an admin."""
	title = models.CharField(max_length=200)
	body = models.TextField()
	url = models.URLField(blank=True, default='')
	embedding = models.JSONField(default=list, blank=True,
		help_text='Precomputed embedding vector (list of floats)')
	is_active = models.BooleanField(default=True)
	created_by = models.ForeignKey(User, on_delete=models.CASCADE, related_name='created_ads')
	created_at = models.DateTimeField(default=now)

	def __str__(self):
		return self.title


def info_ad_impression(imp):
    try:
        return str(object.__getattribute__(imp, 'user'))
    except:
        return ""


@InstrumentORM(
    logger,
    {"AdImpression.ad", "AdImpression.created_at"},
    info=info_ad_impression, events={'read', 'write'}
)
class AdImpression(models.Model):
	"""Records that an ad was shown to a user."""
	ad = models.ForeignKey(Ad, on_delete=models.CASCADE, related_name='impressions')
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='ad_impressions')
	created_at = models.DateTimeField(default=now)
	

def info_ad_click(click):
    try:
        return str(object.__getattribute__(click, 'user'))
    except:
        return ""


@InstrumentORM(
    logger,
    {"AdClick.ad", "AdClick.created_at"},
    info=info_ad_click, events={'read', 'write'}
)
class AdClick(models.Model):
	"""Records that a user clicked on an ad."""
	ad = models.ForeignKey(Ad, on_delete=models.CASCADE, related_name='clicks')
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='ad_clicks')
	created_at = models.DateTimeField(default=now)
