"""
Social / auth forms: SignUpForm, TwitForm, ReplyForm, RepostForm, DirectMessageForm.
"""
from django import forms  # type: ignore
from django.contrib.auth.forms import UserCreationForm  # type: ignore
from django.contrib.auth import get_user_model  # type: ignore

from twitt.models import Twit

User = get_user_model()


class SignUpForm(UserCreationForm):
	consent_personalized_ad = forms.BooleanField(
		required=False,
		label='I consent to personalized advertising',
		help_text='We use your posts to recommend relevant ads.',
	)
	consent_statistics = forms.BooleanField(
		required=False,
		label='I consent to usage statistics collection',
		help_text='We collect anonymous page-visit analytics to improve the service.',
	)

	class Meta:
		model = User
		fields = ["username", 'first_name', 'last_name']


class TwitForm(forms.ModelForm):
	class Meta:
		model = Twit
		fields = ['content']


class ReplyForm(forms.Form):
	content = forms.CharField(
		max_length=280,
		widget=forms.Textarea(attrs={'rows': 2, 'placeholder': 'Write a reply…'}),
		label='Reply',
	)


class RepostForm(forms.Form):
	message = forms.CharField(
		max_length=280, required=False,
		widget=forms.Textarea(attrs={'rows': 2, 'placeholder': 'Add a comment (optional)…'}),
		label='Comment',
	)


class DirectMessageForm(forms.Form):
	recipient = forms.ModelChoiceField(
		queryset=User.objects.all(),
		label='To',
	)
	content = forms.CharField(
		max_length=1000,
		widget=forms.Textarea(attrs={'rows': 3, 'placeholder': 'Type your message…'}),
		label='Message',
	)

	def __init__(self, *args, user=None, **kwargs):
		super().__init__(*args, **kwargs)
		if user:
			self.fields['recipient'].queryset = User.objects.exclude(pk=user.pk)
