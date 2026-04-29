"""
GDPR forms: consent, rectification, erasure, portability, restriction, etc.
"""
from django import forms  # type: ignore


PURPOSE_CHOICES = [
	('personalized_ad', 'Personalized Advertising'),
	('statistics', 'Statistics / Analytics'),
]

SPECIAL_PURPOSE_CHOICES = [
    ('service', 'Core Functionality'),
	('personalized_ad', 'Personalized Advertising'),
	('statistics', 'Statistics / Analytics'),
]


SPECIAL_CATEGORY_CHOICES = [
	('racial_ethnic', 'Racial or Ethnic Origin'),
	('political', 'Political Opinions'),
	('religious', 'Religious or Philosophical Beliefs'),
	('trade_union', 'Trade Union Membership'),
	('genetic', 'Genetic Data'),
	('biometric', 'Biometric Data'),
	('health', 'Health Data'),
	('sexual', 'Sex Life or Sexual Orientation'),
]

CLAIM_TYPE_CHOICES = [
	('judicial', 'Necessary for Judicial Claims'),
	('legal_obligation', 'Necessary for Legal Obligation'),
	('public_interest', 'Necessary for Public Interest'),
	('important_public_interest', 'Necessary for Important Public Interest'),
	('medical', 'Necessary for Special Medical Reasons'),
	('substantial_public_interest', 'Necessary for Substantial Public Interest'),
	('vital_interests', 'Necessary for Vital Interests'),
	('protection_of_rights', 'Necessary for Protection of Rights'),
	('compatible_purpose', 'Compatible with Purpose'),
	('data_category', 'Has Data Category'),
	('intended_recipient', 'Has Intended Recipient'),
	('health_related', 'Health Related'),
	('special_data', 'Special Data Category'),
	('criminal_data', 'Relates to Criminal Convictions'),
	('administrative_arrangement', 'Administrative Arrangement'),
	('contractual_clauses', 'Contractual Clauses'),
]


class SpecialConsentForm(forms.Form):
	purpose = forms.ChoiceField(choices=SPECIAL_PURPOSE_CHOICES)
	special_category = forms.ChoiceField(choices=SPECIAL_CATEGORY_CHOICES)


class RectificationForm(forms.Form):
	FIELD_CHOICES = [
		('User.first_name', 'First name'),
		('User.last_name', 'Last name'),
		('User.email', 'Email address'),
		('Twit.content', 'A specific twit (enter its ID below)'),
		('Reply.content', 'A specific reply (enter its ID below)'),
		('DirectMessage.content', 'A specific direct message (enter its ID below)'),
	]
	field = forms.ChoiceField(choices=FIELD_CHOICES, label='What do you want to correct?')
	object_id = forms.CharField(max_length=255, required=False, label='Object ID',
								help_text='Required for twits, replies, and messages. Leave blank for your own profile fields.')
	new_data = forms.CharField(max_length=255, label='Corrected value')

	def clean(self):
		cleaned = super().clean()
		field = cleaned.get('field', '')
		obj_id = cleaned.get('object_id', '').strip()
		if field and not field.startswith('User.') and not obj_id:
			self.add_error('object_id', 'An object ID is required for this field.')
		return cleaned

	def get_data_id(self, user):
		"""Build the internal data_id string from form fields."""
		field = self.cleaned_data['field']
		obj_id = self.cleaned_data.get('object_id', '').strip()
		if field.startswith('User.'):
			return f"{field}:{user.pk}"
		return f"{field}:{obj_id}"


class ContestAccuracyForm(forms.Form):
	data_id = forms.CharField(max_length=255, label='Data identifier',
							  help_text='e.g. Twit.content:42 or User.email:3')
	new_data = forms.CharField(max_length=255, label='Value you believe is correct')
	purpose = forms.ChoiceField(choices=PURPOSE_CHOICES,
								label='Purpose to restrict while accuracy is contested')


class ObjectionForm(forms.Form):
	purpose = forms.ChoiceField(choices=PURPOSE_CHOICES)
	reason = forms.CharField(widget=forms.Textarea, label='Reason for objection')


ERASURE_CHOICES = [
	('all', 'Delete ALL my data (right to be forgotten)'),
	('Twit', 'Delete a specific twit'),
	('Reply', 'Delete a specific reply'),
	('DirectMessage', 'Delete a specific direct message'),
]


class ErasureForm(forms.Form):
	scope = forms.ChoiceField(choices=ERASURE_CHOICES, label='What do you want to delete?',
							  widget=forms.RadioSelect)
	object_id = forms.CharField(max_length=255, required=False, label='Object ID',
								help_text='Required when deleting a specific twit, reply, or message.')

	def clean(self):
		cleaned = super().clean()
		scope = cleaned.get('scope', '')
		obj_id = cleaned.get('object_id', '').strip()
		if scope != 'all' and not obj_id:
			self.add_error('object_id', 'Please enter the ID of the item to delete.')
		return cleaned

	def get_data_id(self, user):
		"""Build the internal data_id string from form fields."""
		scope = self.cleaned_data['scope']
		if scope == 'all':
			return f"User:all:{user.username}"
		obj_id = self.cleaned_data['object_id'].strip()
		return f"{scope}.content:{obj_id}"


class PortabilityForm(forms.Form):
	new_controller = forms.CharField(max_length=255, required=False,
									 label='New controller (optional)',
									 help_text='Leave blank for a copy only')


class RecipientInfoForm(forms.Form):
    pass

class AdminClaimForm(forms.Form):
	claim_type = forms.ChoiceField(choices=CLAIM_TYPE_CHOICES)
	activity = forms.CharField(max_length=255, required=False, label='Activity')
	data_id = forms.CharField(max_length=255, required=False, label='Data identifier')
	entity = forms.CharField(max_length=255, required=False, label='Entity')
	purpose = forms.CharField(max_length=255, required=False, label='Purpose')
	detail = forms.CharField(widget=forms.Textarea, required=False, label='Detail / Legal basis')
	detail2 = forms.CharField(widget=forms.Textarea, required=False, label='Detail 2')


class AdminLiftRestrictionForm(forms.Form):
	data_id = forms.CharField(max_length=255, label='Data identifier')
	request_id = forms.CharField(max_length=36, label='Original restriction request ID')


class AdminSendDataForm(forms.Form):
	entity = forms.CharField(max_length=255, label='Recipient entity')
	data_id = forms.CharField(max_length=255, label='Data identifier to send')
