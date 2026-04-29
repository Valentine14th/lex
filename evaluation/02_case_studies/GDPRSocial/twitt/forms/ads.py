"""
Advertising forms.
"""
from django import forms  # type: ignore
from twitt.models import Ad


class AdForm(forms.ModelForm):
	class Meta:
		model = Ad
		fields = ['title', 'body', 'url', 'is_active']
