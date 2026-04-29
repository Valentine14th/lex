#!/usr/bin/env python
import os
import sys

if __name__ == "__main__":
    os.environ.setdefault("DJANGO_SETTINGS_MODULE", "Twitter.settings")

    if "--clean" in sys.argv:
        sys.argv.remove("--clean")
        import django
        django.setup()
        from twitt.models import (Follow, Twit, ActivityLog, AdminClaim,
                                  ConsentRecord, DataRestriction,
                                  GDPRNotification, GDPRRequest, AdImpression, 
                                  AdClick, PageVisit)
        Follow.objects.all().delete()
        Twit.objects.all().delete()
        ActivityLog.objects.all().delete()
        AdminClaim.objects.all().delete()
        ConsentRecord.objects.all().delete()
        DataRestriction.objects.all().delete()
        GDPRNotification.objects.all().delete()
        GDPRRequest.objects.all().delete()
        AdImpression.objects.all().delete()
        AdClick.objects.all().delete()
        PageVisit.objects.all().delete()
        print("Cleaned all application tables.")

    if "runserver" in sys.argv:
        from twitt.enforcer import pdp
        pdp.start_threads()

    from django.core.management import execute_from_command_line  # type: ignore
    execute_from_command_line(sys.argv)

   