from django.apps import AppConfig

from Twitter.settings import WITH_REVIEW_THREAD


class TwittConfig(AppConfig):
    default_auto_field = 'django.db.models.BigAutoField'
    name = 'twitt'

    def ready(self):
        from twitt.daily_review import start_daily_review_thread
        if WITH_REVIEW_THREAD:
            start_daily_review_thread()