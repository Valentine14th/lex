"""
GDPR views: data-subject rights dashboard, consent, requests, notifications.
Admin/Controller panel views.
"""
import uuid

from django.contrib.auth.decorators import login_required
from django.http import HttpResponse
from django.shortcuts import get_object_or_404
from django.template.response import TemplateResponse
from django.utils.decorators import method_decorator
from django.views import View
from django.views.generic import TemplateView

from twitt.models import (
    User, GDPRRequest, DataRestriction,
    AdminClaim, GDPRNotification, ConsentRecord, ActivityLog,
)
from twitt.forms import (
    SpecialConsentForm, RectificationForm, ContestAccuracyForm,
    ObjectionForm, ErasureForm, PortabilityForm,
    RecipientInfoForm, AdminClaimForm, AdminLiftRestrictionForm,
    AdminSendDataForm,
)
from instrlib.django.custom_http import redirect, render


# =========================================================================
#  Mixins (local copies – also exported from social.py)
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


def _new_gdpr_request_id() -> str:
    return str(uuid.uuid4())[:8]


# =========================================================================
#  USER-FACING  GDPR VIEWS
# =========================================================================

class GDPRDashboardView(LoginRequiredMixin, TemplateView):
    """Central page for data-subject rights."""
    template_name = 'gdpr/dashboard.html'

    def get_context_data(self, **kwargs):
        user = self.request.user
        return {
            'pending_requests': GDPRRequest.objects.filter(user=user, status='pending').count(),
            'unread_notifications': GDPRNotification.objects.filter(user=user, is_read=False).count(),
            'active_consents': ConsentRecord.objects.filter(user=user, is_active=True),
        }


class ConsentManagementView(LoginRequiredMixin, View):
    """Give or revoke consent for specific purposes."""
    template_name = 'gdpr/consent_management.html'

    def get(self, request, *args, **kwargs):
        records = ConsentRecord.objects.filter(user=request.user)
        return TemplateResponse(request, self.template_name, {
            'consent_records': records,
            'purposes': ['personalized_ad', 'statistics'],
        })

    def post(self, request, *args, **kwargs):
        purpose = ''
        if 'give_consent' in request.POST:
            purpose = request.POST['give_consent']
            ConsentRecord.objects.update_or_create(
                user=request.user, purpose=purpose, special_category='',
                defaults={'is_active': True})
        elif 'revoke_consent' in request.POST:
            purpose = request.POST['revoke_consent']
            ConsentRecord.objects.filter(
                user=request.user, purpose=purpose, special_category='').update(is_active=False)
        return redirect('gdpr_consent')


class SpecialConsentView(LoginRequiredMixin, View):
    """Give or revoke consent for special data categories."""
    template_name = 'gdpr/special_consent.html'

    def get(self, request, *args, **kwargs):
        existing = ConsentRecord.objects.filter(
            user=request.user).exclude(special_category='')
        return TemplateResponse(request, self.template_name, {
            'form': SpecialConsentForm(),
            'existing_consents': existing,
        })

    def post(self, request, *args, **kwargs):
        if 'revoke' in request.POST:
            pk = request.POST['revoke']
            ConsentRecord.objects.filter(pk=pk, user=request.user).delete()
            return redirect('gdpr_special_consent')
        form = SpecialConsentForm(request.POST)
        if form.is_valid():
            ConsentRecord.objects.get_or_create(
                user=request.user,
                purpose=form.cleaned_data['purpose'],
                special_category=form.cleaned_data['special_category'],
                defaults={'is_active': True})
        return redirect('gdpr_special_consent')


class RequestAccessView(LoginRequiredMixin, View):
    """Request access to all personal data (Art. 15) and optionally
    data portability to another controller (Art. 20)."""
    template_name = 'gdpr/request_access.html'

    def get(self, request, *args, **kwargs):
        rq_id = _new_gdpr_request_id()
        GDPRRequest.objects.create(id=rq_id, user=request.user, request_type='access')
        return TemplateResponse(request, self.template_name, {
            'gdpr_request_id': rq_id})

    def post(self, request, *args, **kwargs):
        nc = request.POST.get('new_controller', '').strip()
        rq_id = request.POST.get('gdpr_request_id', '')
        if nc:
            GDPRRequest.objects.filter(pk=rq_id).update(
                request_type='portability', new_controller=nc)
        return redirect('gdpr_my_requests')


class RequestRectificationView(LoginRequiredMixin, View):
    """Request rectification of personal data (Art. 16)."""
    template_name = 'gdpr/request_rectification.html'

    def get(self, request, *args, **kwargs):
        rq_id = _new_gdpr_request_id()
        GDPRRequest.objects.create(id=rq_id, user=request.user, request_type='rectification')
        return TemplateResponse(request, self.template_name, {
            'form': RectificationForm(),
            'gdpr_request_id': rq_id})

    def post(self, request, *args, **kwargs):
        form = RectificationForm(request.POST)
        if form.is_valid():
            rq_id = request.POST.get('gdpr_request_id', '')
            data_id = form.get_data_id(request.user)
            GDPRRequest.objects.filter(pk=rq_id).update(
                data_id=data_id,
                new_data=form.cleaned_data['new_data'])
        return redirect('gdpr_my_requests')


class ContestAccuracyView(LoginRequiredMixin, View):
    """Contest accuracy & request restriction of processing (Art. 16 + 18)."""
    template_name = 'gdpr/contest_accuracy.html'

    def get(self, request, *args, **kwargs):
        rq_id = _new_gdpr_request_id()
        GDPRRequest.objects.create(id=rq_id, user=request.user, request_type='restriction')
        return TemplateResponse(request, self.template_name, {
            'form': ContestAccuracyForm(),
            'gdpr_request_id': rq_id})

    def post(self, request, *args, **kwargs):
        form = ContestAccuracyForm(request.POST)
        if form.is_valid():
            rq_id = request.POST.get('gdpr_request_id', '')
            data_id = form.cleaned_data['data_id']
            purpose = form.cleaned_data['purpose']
            GDPRRequest.objects.filter(pk=rq_id).update(
                data_id=data_id,
                new_data=form.cleaned_data['new_data'],
                purpose=purpose)
            try:
                rq = GDPRRequest.objects.get(pk=rq_id)
                DataRestriction.objects.create(
                    request=rq, data_id=data_id, purpose=purpose)
            except GDPRRequest.DoesNotExist:
                pass
        return redirect('gdpr_my_requests')


class RequestObjectionView(LoginRequiredMixin, View):
    """Object to processing for a specific purpose (Art. 21)."""
    template_name = 'gdpr/request_objection.html'

    def get(self, request, *args, **kwargs):
        rq_id = _new_gdpr_request_id()
        GDPRRequest.objects.create(id=rq_id, user=request.user, request_type='objection')
        return TemplateResponse(request, self.template_name, {
            'form': ObjectionForm(),
            'gdpr_request_id': rq_id})

    def post(self, request, *args, **kwargs):
        form = ObjectionForm(request.POST)
        if form.is_valid():
            rq_id = request.POST.get('gdpr_request_id', '')
            GDPRRequest.objects.filter(pk=rq_id).update(
                purpose=form.cleaned_data['purpose'],
                declaration_text=form.cleaned_data['reason'])
        return redirect('gdpr_my_requests')


class RequestErasureView(LoginRequiredMixin, View):
    """Request erasure of personal data (Art. 17)."""
    template_name = 'gdpr/request_erasure.html'

    def get(self, request, *args, **kwargs):
        rq_id = _new_gdpr_request_id()
        GDPRRequest.objects.create(id=rq_id, user=request.user, request_type='erasure')
        return TemplateResponse(request, self.template_name, {
            'form': ErasureForm(),
            'gdpr_request_id': rq_id})

    def post(self, request, *args, **kwargs):
        form = ErasureForm(request.POST)
        if form.is_valid():
            rq_id = request.POST.get('gdpr_request_id', '')
            data_id = form.get_data_id(request.user)
            GDPRRequest.objects.filter(pk=rq_id).update(data_id=data_id)
        return redirect('gdpr_my_requests')


class RequestPortabilityView(LoginRequiredMixin, View):
    """Redirects to the unified access/portability view."""

    def get(self, request, *args, **kwargs):
        return redirect('gdpr_request_access')

    def post(self, request, *args, **kwargs):
        return redirect('gdpr_request_access')


class RequestRestrictionView(LoginRequiredMixin, View):
    """Redirect to contest accuracy (restriction is part of that flow)."""
    def get(self, request, *args, **kwargs):
        return redirect('gdpr_contest_accuracy')

    def post(self, request, *args, **kwargs):
        return redirect('gdpr_contest_accuracy')


class RequestRecipientInfoView(LoginRequiredMixin, View):
    """Request info about recipients of personal data (Art. 15(1)(c))."""
    template_name = 'gdpr/request_recipient_info.html'

    def get(self, request, *args, **kwargs):
        rq_id = _new_gdpr_request_id()
        GDPRRequest.objects.create(id=rq_id, user=request.user, request_type='recipient')
        return TemplateResponse(request, self.template_name, {
            'form': RecipientInfoForm(),
            'gdpr_request_id': rq_id})

    def post(self, request, *args, **kwargs):
        form = RecipientInfoForm(request.POST)
        return redirect('gdpr_my_requests')


class MyRequestsView(LoginRequiredMixin, TemplateView):
    """List the logged-in user's GDPR requests."""
    template_name = 'gdpr/my_requests.html'

    def get_context_data(self, **kwargs):
        return {'requests': GDPRRequest.objects.filter(user=self.request.user).order_by('-created_at')}


class NotificationsView(LoginRequiredMixin, TemplateView):
    """List enforcement notifications for the logged-in user."""
    template_name = 'gdpr/notifications.html'

    def get_context_data(self, **kwargs):
        notes = GDPRNotification.objects.filter(user=self.request.user).order_by('-created_at')
        notes.filter(is_read=False).update(is_read=True)
        return {'notifications': notes}


# =========================================================================
#  ADMIN / CONTROLLER PANEL VIEWS
# =========================================================================

class AdminDashboardView(StaffRequiredMixin, TemplateView):
    """Controller's GDPR admin dashboard."""
    template_name = 'admin_panel/dashboard.html'

    def get_context_data(self, **kwargs):
        return {
            'pending_requests': GDPRRequest.objects.filter(status='pending').order_by('-created_at')[:20],
            'recent_claims': AdminClaim.objects.order_by('-created_at')[:20],
            'active_restrictions': DataRestriction.objects.filter(is_active=True),
            'recent_activity_logs': ActivityLog.objects.order_by('-created_at')[:20],
        }


class AdminClaimView(StaffRequiredMixin, View):
    """Create a controller claim (judicial, legal, etc.)."""
    template_name = 'admin_panel/claim_form.html'

    def get(self, request, *args, **kwargs):
        return TemplateResponse(request, self.template_name, {'form': AdminClaimForm()})

    def post(self, request, *args, **kwargs):
        form = AdminClaimForm(request.POST)
        if form.is_valid():
            AdminClaim.objects.create(
                claim_type=form.cleaned_data['claim_type'],
                activity=form.cleaned_data.get('activity', ''),
                data_id=form.cleaned_data.get('data_id', ''),
                entity=form.cleaned_data.get('entity', ''),
                purpose=form.cleaned_data.get('purpose', ''),
                detail=form.cleaned_data.get('detail', ''),
                detail2=form.cleaned_data.get('detail2', ''),
                created_by=request.user)
        return redirect('admin_dashboard')


class AdminLiftRestrictionView(StaffRequiredMixin, View):
    """Lift a data-processing restriction."""
    template_name = 'admin_panel/lift_restriction.html'

    def get(self, request, *args, **kwargs):
        return TemplateResponse(request, self.template_name, {
            'form': AdminLiftRestrictionForm(),
            'active_restrictions': DataRestriction.objects.filter(is_active=True),
        })

    def post(self, request, *args, **kwargs):
        form = AdminLiftRestrictionForm(request.POST)
        if form.is_valid():
            DataRestriction.objects.filter(
                data_id=form.cleaned_data['data_id'],
                request_id=form.cleaned_data['request_id'],
                is_active=True).update(is_active=False)
        return redirect('admin_dashboard')


class AdminSendDataView(StaffRequiredMixin, View):
    """Send personal data to a third-party entity."""
    template_name = 'admin_panel/send_data.html'

    def get(self, request, *args, **kwargs):
        return TemplateResponse(request, self.template_name, {'form': AdminSendDataForm()})

    def post(self, request, *args, **kwargs):
        form = AdminSendDataForm(request.POST)
        if form.is_valid():
            pass  # Event is emitted through InstrumentURL → input_mapping
        return redirect('admin_dashboard')


class AdminRequestsView(StaffRequiredMixin, TemplateView):
    """View all user GDPR requests."""
    template_name = 'admin_panel/requests.html'

    def get_context_data(self, **kwargs):
        return {'requests': GDPRRequest.objects.all().order_by('-created_at')}
