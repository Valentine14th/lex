"""
GDPR-related models (NOT instrumented by InstrumentORM to avoid loops).
"""
import uuid

from django.db import models  # type: ignore
from django.utils.timezone import now  # type: ignore

from twitt.models.social import User


# =========================================================================
#  Helpers
# =========================================================================

def _gdpr_id():
	return str(uuid.uuid4())[:8]


# =========================================================================
#  GDPR models
# =========================================================================

class GDPRRequest(models.Model):
	"""Tracks all GDPR data-subject requests."""
	REQUEST_TYPES = [
		('access', 'Access Request'),
		('rectification', 'Rectification Request'),
		('erasure', 'Erasure Request'),
		('restriction', 'Restriction Request'),
		('portability', 'Portability Request'),
		('objection', 'Objection'),
		('recipient', 'Recipient Info Request'),
	]
	STATUS_CHOICES = [
		('pending', 'Pending'),
		('completed', 'Completed'),
	]
	id = models.CharField(primary_key=True, max_length=36, default=_gdpr_id)
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='gdpr_requests')
	request_type = models.CharField(max_length=20, choices=REQUEST_TYPES)
	status = models.CharField(max_length=20, default='pending', choices=STATUS_CHOICES)
	data_id = models.CharField(max_length=255, blank=True, default='')
	new_data = models.CharField(max_length=255, blank=True, default='')
	purpose = models.CharField(max_length=100, blank=True, default='')
	declaration_text = models.TextField(blank=True, default='')
	new_controller = models.CharField(max_length=255, blank=True, default='')
	response_text = models.TextField(blank=True, default='')
	response_file = models.FileField(upload_to='gdpr_responses/', blank=True, null=True)
	created_at = models.DateTimeField(default=now)

	def __str__(self):
		return f"{self.request_type}:{self.id}"


class DataRestriction(models.Model):
	"""Tracks active data-processing restrictions."""
	request = models.ForeignKey(GDPRRequest, on_delete=models.CASCADE, related_name='restrictions')
	data_id = models.CharField(max_length=255)
	purpose = models.CharField(max_length=100)
	is_active = models.BooleanField(default=True)
	created_at = models.DateTimeField(default=now)


class AdminClaim(models.Model):
	"""Tracks controller claims for legal bases, special categories, etc."""
	CLAIM_TYPES = [
		('judicial', 'Necessary for Judicial Claims'),
		('legal_obligation', 'Necessary for Legal Obligation'),
		('public_interest', 'Necessary for Public Interest'),
		('important_public_interest', 'Necessary for Important Public Interest'),
		('medical', 'Necessary for Special Medical Reasons'),
		('substantial_public_interest', 'Necessary for Substantial Public Interest'),
		('vital_interests', 'Necessary for Vital Interests'),
		('protection_of_rights', 'Necessary for Protection of Rights'),
		('compatible_purpose', 'Compatible with Purpose'),
		('health_related', 'Health Related'),
		('special_data', 'Special Data Category'),
		('criminal_data', 'Relates to Criminal Convictions'),
		('data_category', 'Has Data Category'),
		('intended_recipient', 'Has Intended Recipient'),
		('administrative_arrangement', 'Administrative Arrangement'),
		('contractual_clauses', 'Contractual Clauses'),
	]
	id = models.CharField(primary_key=True, max_length=36, default=_gdpr_id)
	claim_type = models.CharField(max_length=50, choices=CLAIM_TYPES)
	activity = models.CharField(max_length=255, blank=True, default='')
	data_id = models.CharField(max_length=255, blank=True, default='')
	entity = models.CharField(max_length=255, blank=True, default='')
	purpose = models.CharField(max_length=255, blank=True, default='')
	detail = models.TextField(blank=True, default='')
	detail2 = models.TextField(blank=True, default='')
	created_by = models.ForeignKey(User, on_delete=models.CASCADE, related_name='admin_claims')
	created_at = models.DateTimeField(default=now)

	def __str__(self):
		return f"{self.get_claim_type_display()} ({self.id})"


class GDPRNotification(models.Model):
	"""Stores enforcement notifications for users."""
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='gdpr_notifications')
	declaration_id = models.CharField(max_length=255)
	text = models.TextField()
	is_read = models.BooleanField(default=False)
	created_at = models.DateTimeField(default=now)


class ActivityLog(models.Model):
	"""ROPA (Record of Processing Activities) entries."""
	activity = models.CharField(max_length=255)
	property_name = models.CharField(max_length=255)
	value = models.TextField()
	created_at = models.DateTimeField(default=now)

	def __str__(self):
		return f"{self.activity}.{self.property_name}={self.value}"


class ConsentRecord(models.Model):
	"""Tracks all consents (including special) given by users."""
	user = models.ForeignKey(User, on_delete=models.CASCADE, related_name='consent_records')
	purpose = models.CharField(max_length=100)
	special_category = models.CharField(max_length=100, blank=True, default='')
	is_active = models.BooleanField(default=True)
	created_at = models.DateTimeField(default=now)

	class Meta:
		unique_together = ('user', 'purpose', 'special_category')
