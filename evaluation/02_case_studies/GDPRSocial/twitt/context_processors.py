def cookie_consent(request):
    """Template context: GDPR notification badge count.
    Cookie-consent is managed solely through the GDPR Consent Management page."""
    ctx = {}

    if request.user.is_authenticated:
        from twitt.models import GDPRNotification, ConsentRecord
        ctx['unread_gdpr_notifications'] = (
            GDPRNotification.objects.filter(user=request.user, is_read=False).count()
        )
        ctx['has_ad_consent'] = ConsentRecord.objects.filter(
            user=request.user, purpose='personalized_ad'
        ).exists()
        ctx['has_stats_consent'] = ConsentRecord.objects.filter(
            user=request.user, purpose='statistics'
        ).exists()
    else:
        ctx['unread_gdpr_notifications'] = 0
        ctx['has_ad_consent'] = False
        ctx['has_stats_consent'] = False

    return ctx