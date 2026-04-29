"""Twitter URL Configuration

The `urlpatterns` list routes URLs to views. For more information please see:
    https://docs.djangoproject.com/en/1.9/topics/http/urls/
Examples:
Function views
    1. Add an import:  from my_app import views
    2. Add a URL to urlpatterns:  url(r'^$', views.home, name='home')
Class-based views
    1. Add an import:  from other_app.views import Home
    2. Add a URL to urlpatterns:  url(r'^$', Home.as_view(), name='home')
Including another URLconf
    1. Import the include() function: from django.conf.urls import url, include
    2. Add a URL to urlpatterns:  url(r'^blog/', include('blog.urls'))
"""
from django.urls import path, include # type: ignore
from django.contrib import admin # type: ignore
from django.conf import settings # type: ignore
from django.conf.urls.static import static # type: ignore

from instrlib.django.url import InstrumentURL
from twitt.enforcer import logger

urlpatterns = [ 
    path('admin/', admin.site.urls),
    path('', include('twitt.urls')),
]

to_instrument = {
    # GDPR user views
    "twitt.views.gdpr.ConsentManagementView",
    "twitt.views.gdpr.SpecialConsentView",
    "twitt.views.gdpr.RequestAccessView",
    "twitt.views.gdpr.RequestRectificationView",
    "twitt.views.gdpr.ContestAccuracyView",
    "twitt.views.gdpr.RequestObjectionView",
    "twitt.views.gdpr.RequestErasureView",
    "twitt.views.gdpr.RequestPortabilityView",
    "twitt.views.gdpr.RequestRestrictionView",
    "twitt.views.gdpr.RequestRecipientInfoView",
    # Data collection views
    "twitt.views.social.SignUpView",
    "twitt.views.social.PostTwitView",
    "twitt.views.social.FollowUserView",
    # Admin views
    "twitt.views.admin.AdminClaimView",
    "twitt.views.admin.AdminLiftRestrictionView",
    "twitt.views.admin.AdminSendDataView",
}

urlpatterns = InstrumentURL(logger, to_instrument, events = {'input'})(urlpatterns)

if settings.DEBUG:
    urlpatterns += static(settings.MEDIA_URL, document_root=settings.MEDIA_ROOT)
