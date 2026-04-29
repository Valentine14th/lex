"""
Core social models: User, Follow, Twit (instrumented by InstrumentORM),
plus Like, Reply, Repost, DirectMessage.
"""
from __future__ import unicode_literals
import uuid

from django.contrib.auth.models import AbstractUser  # type: ignore
from django.db import models  # type: ignore
from django.utils.timezone import now  # type: ignore
from ambient_toolbox.models import CommonInfo  # type: ignore

from twitt.classifier import classify_text


# =========================================================================
#  Instrumented core models
# =========================================================================

def info_user(user):
	try:
		return str(user)
	except:
		return ""


class User(AbstractUser):

	def delete_data(self):
		"""Delete ALL personal data associated with this user (Art. 17 GDPR)."""
		# Content authored by the user
		self.twit.all().delete()
		self.reply_set.all().delete()
		self.reposts.all().delete()
		self.likes.all().delete()
		# Direct messages (sent and received)
		self.sent_messages.all().delete()
		self.received_messages.all().delete()
		# Social graph
		self.follower.all().delete()
		self.following.all().delete()
		# GDPR / consent records
		from twitt.models.gdpr import ConsentRecord, GDPRNotification
		ConsentRecord.objects.filter(user=self).delete()
		GDPRNotification.objects.filter(user=self).delete()
		# Ad interactions
		from twitt.models.ads import AdImpression, AdClick
		AdImpression.objects.filter(user=self).delete()
		AdClick.objects.filter(user=self).delete()
		# Statistics
		from twitt.models.statistics import PageVisit
		PageVisit.objects.filter(user=self).delete()
		# User object
		self.delete()

def info_follow(follow):
	try:
		return str(object.__getattribute__(follow, 'follower'))
	except:
		return ""


class Follow(CommonInfo):
	"""Follow model: follower/following relationships."""
	follower  : models.ForeignKey    = models.ForeignKey(User, related_name='follower', db_index=True, on_delete=models.CASCADE)
	following : models.ForeignKey    = models.ForeignKey(User, related_name='following', db_index=True, on_delete=models.CASCADE)
	date      : models.DateTimeField = models.DateTimeField(default=now)

	class Meta:
		unique_together = ('follower', 'following')


def info_twit(twit):
	try:
		return str(object.__getattribute__(twit, 'author'))
	except:
		return ""


class Twit(CommonInfo):
	"""Twit model: a short post."""
	id         : models.UUIDField     = models.UUIDField(primary_key=True, default=uuid.uuid4, editable=False)
	content    : models.CharField     = models.CharField(max_length=140)
	posted_on  : models.DateTimeField = models.DateTimeField(default=now)
	updated_on : models.DateTimeField = models.DateTimeField(default=now, db_index=True)
	author     : models.ForeignKey    = models.ForeignKey(User, related_name='twit', db_index=True, on_delete=models.CASCADE)
	special_categories = models.JSONField(default=list, blank=True,
		help_text='Auto-detected special data categories (Art. 9 GDPR)')

	def save(self, *args, **kwargs):
		if self.posted_on is None:
			self.posted_on = now()
			self.updated_on = now()
		else:
			self.updated_on = now()
		self.special_categories = classify_text(self.content)
		super(Twit, self).save(*args, **kwargs)


# =========================================================================
#  Social-interaction models
# =========================================================================

def info_like(like):
    try:
        return str(f"{object.__getattribute__(like, 'user')}")
    except:
        return ""


class Like(models.Model):
	"""A user 'likes' a twit."""
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='likes')
	twit = models.ForeignKey(Twit, on_delete=models.CASCADE, related_name='likes')
	created_at = models.DateTimeField(default=now)

	class Meta:
		unique_together = ('user', 'twit')

	def __str__(self):
		return f"{self.user} ♥ {self.twit_id}"


def info_reply(reply):
    try:
        return str(f"{object.__getattribute__(reply, 'author')}")
    except:
        return ""


class Reply(models.Model):
	"""A reply (answer) to an existing twit."""
	id = models.UUIDField(primary_key=True, default=uuid.uuid4, editable=False)
	parent = models.ForeignKey(Twit, on_delete=models.CASCADE, related_name='replies')
	author = models.ForeignKey(User, on_delete=models.CASCADE, related_name='reply_set')
	content = models.CharField(max_length=280)
	created_at = models.DateTimeField(default=now)
	special_categories = models.JSONField(default=list, blank=True,
		help_text='Auto-detected special data categories (Art. 9 GDPR)')

	def save(self, *args, **kwargs):
		self.special_categories = classify_text(self.content)
		super().save(*args, **kwargs)


def info_repost(repost):
    try:
        return str(f"{object.__getattribute__(repost, 'user')}")
    except:
        return ""


class Repost(models.Model):
	"""A repost (retweet) of an existing twit, optionally with a message."""
	id = models.UUIDField(primary_key=True, default=uuid.uuid4, editable=False)
	original = models.ForeignKey(Twit, on_delete=models.CASCADE, related_name='reposts')
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='reposts')
	message = models.CharField(max_length=280, blank=True, default='')
	created_at = models.DateTimeField(default=now)


def info_dm(dm):
    try:
        return str(f"{object.__getattribute__(dm, 'sender')}")
    except:
        return ""
	

class DirectMessage(models.Model):
	"""A private direct message between two users."""
	sender = models.ForeignKey(User, on_delete=models.CASCADE, related_name='sent_messages')
	recipient = models.ForeignKey(User, on_delete=models.CASCADE, related_name='received_messages')
	content = models.TextField(max_length=1000)
	is_read = models.BooleanField(default=False)
	created_at = models.DateTimeField(default=now)
	special_categories = models.JSONField(default=list, blank=True,
		help_text='Auto-detected special data categories (Art. 9 GDPR)')

	def save(self, *args, **kwargs):
		self.special_categories = classify_text(self.content)
		super().save(*args, **kwargs)

	class Meta:
		ordering = ['-created_at']