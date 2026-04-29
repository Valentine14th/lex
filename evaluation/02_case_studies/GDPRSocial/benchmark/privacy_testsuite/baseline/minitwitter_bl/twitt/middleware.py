"""
Analytics middleware: records PageVisit for every request (if the user has
given statistics consent, or for anonymous aggregate tracking).
"""
import hashlib
import time
import uuid

from django.utils.deprecation import MiddlewareMixin



class PageVisitMiddleware(MiddlewareMixin):
    """Record a PageVisit row for each request/response cycle."""

    # Paths to skip (static files, media, admin, favicon)
    SKIP_PREFIXES = ('/static/', '/media/', '/admin/', '/favicon.ico')

    def process_request(self, request):
        request._pv_start = time.monotonic()

    def process_response(self, request, response):
        path = request.path
        if any(path.startswith(p) for p in self.SKIP_PREFIXES):
            return response
        try:
            self.record_page_visit(request, response)
        except Exception:
            pass  # Never break the request pipeline for analytics
        return response
    def record_page_visit(self, request, response):
        # Always record the page visit for aggregate platform stats.
        # Only associate the user when they have given statistics consent.
        user = getattr(request, 'user', None)
        track_user = None
        if user and getattr(user, 'is_authenticated', False):
            from twitt.models import ConsentRecord
            has_stats_consent = ConsentRecord.objects.filter(
                user=user, purpose='statistics'
            ).exists()
            if has_stats_consent:
                track_user = user

        print('Track user', track_user)

        elapsed_ms = 0
        start = getattr(request, '_pv_start', None)
        if start:
            elapsed_ms = int((time.monotonic() - start) * 1000)

        ip = request.META.get('REMOTE_ADDR', '')
        ip_hash = hashlib.sha256(ip.encode()).hexdigest()[:16] if ip else ''

        session_key = ''
        if hasattr(request, 'session') and request.session.session_key:
            session_key = request.session.session_key

        from twitt.models import PageVisit
        try:
            pk = str(uuid.uuid4())[:8]
            PageVisit.objects.create(
                id=pk,
                user=track_user,
                path=request.path,
                method=request.method,
                status_code=response.status_code,
                referrer=(request.META.get('HTTP_REFERER', '') or '')[:1000],
                user_agent=(request.META.get('HTTP_USER_AGENT', '') or '')[:500],
                session_key=session_key,
                ip_hash=ip_hash,
                response_time_ms=elapsed_ms,
            )
        except Exception:
            pass  # Never break the request pipeline for analytics

        return response
