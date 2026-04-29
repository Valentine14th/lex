"""
Statistics / analytics models: PageVisit.
"""
from django.db import models  # type: ignore
from django.utils.timezone import now  # type: ignore

from twitt.models.social import User


def info_page_visit(visit):
    try:
        return str(f"{object.__getattribute__(visit, 'user')}")
    except:
        return ""
    

class PageVisit(models.Model):
	"""Tracks page visits for analytics (subject to consent)."""
	id = models.CharField(max_length=8, primary_key=True)
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='page_visits',
							 null=True, blank=True)
	path = models.CharField(max_length=500)
	method = models.CharField(max_length=10, default='GET')
	status_code = models.PositiveSmallIntegerField(default=200)
	referrer = models.CharField(max_length=1000, blank=True, default='')
	user_agent = models.CharField(max_length=500, blank=True, default='')
	session_key = models.CharField(max_length=40, blank=True, default='')
	ip_hash = models.CharField(max_length=64, blank=True, default='',
		help_text='SHA-256 hash of client IP for anonymous analytics')
	response_time_ms = models.PositiveIntegerField(default=0,
		help_text='Approximate server response time in milliseconds')
	created_at = models.DateTimeField(default=now)

	class Meta:
		indexes = [
			models.Index(fields=['path', 'created_at']),
			models.Index(fields=['user', 'created_at']),
		]
