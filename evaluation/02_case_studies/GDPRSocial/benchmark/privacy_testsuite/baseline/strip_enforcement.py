#!/usr/bin/env python3
"""
Strip all enforcement-related code from the baseline copy.
Run from the baseline/ directory.
"""
import re
from pathlib import Path

BL = Path(__file__).resolve().parent / "minitwitter_bl"

def patch(filepath, replacements):
    """Apply (old, new) string replacements to a file."""
    p = BL / filepath
    text = p.read_text()
    for old, new in replacements:
        if old not in text:
            print(f"  WARNING: pattern not found in {filepath}:\n    {old[:80]}")
        text = text.replace(old, new)
    p.write_text(text)
    print(f"  Patched {filepath}")

def regex_patch(filepath, pattern, replacement):
    p = BL / filepath
    text = p.read_text()
    text = re.sub(pattern, replacement, text)
    p.write_text(text)
    print(f"  Regex-patched {filepath}")


# ── 1. Twitter/settings.py ──────────────────────────────────────────────
print("1. settings.py")
patch("Twitter/settings.py", [
    ("    'instrlib.middleware.RequestMiddleware',\n", ""),
    # Remove INSTRLIB block
])
# Remove all INSTRLIB_* lines
regex_patch("Twitter/settings.py", r"^# Enforcement\n", "")
regex_patch("Twitter/settings.py", r"^INSTRLIB_\w+ = .*\n", "")


# ── 2. Twitter/urls.py ─────────────────────────────────────────────────
print("2. urls.py")
p = BL / "Twitter/urls.py"
text = p.read_text()
# Remove instrlib imports and enforcer import
text = text.replace("from instrlib.django.url import InstrumentURL\n", "")
text = text.replace("from twitt.enforcer import logger\n", "")
# Remove the to_instrument block and the InstrumentURL call
text = re.sub(r'\nto_instrument = \{.*?\}\n', '\n', text, flags=re.DOTALL)
text = re.sub(r'\nurlpatterns = InstrumentURL\(.*?\)\(urlpatterns\)\n', '\n', text)
p.write_text(text)
print("  Patched Twitter/urls.py")


# ── 3. twitt/models/social.py ──────────────────────────────────────────
print("3. models/social.py")
p = BL / "twitt/models/social.py"
text = p.read_text()
text = text.replace("from instrlib.django.orm import InstrumentORM\n", "")
text = text.replace("from twitt.enforcer import logger\n", "")
# Remove all @InstrumentORM(...) decorators (multi-line)
text = re.sub(r'@InstrumentORM\([^)]*\)\n', '', text)
p.write_text(text)
print("  Patched twitt/models/social.py")


# ── 4. twitt/models/ads.py ─────────────────────────────────────────────
print("4. models/ads.py")
p = BL / "twitt/models/ads.py"
text = p.read_text()
text = text.replace("from instrlib.django.orm import InstrumentORM\n", "")
text = text.replace("from twitt.enforcer import logger\n", "")
text = re.sub(r'@InstrumentORM\([^)]*\)\n', '', text)
p.write_text(text)
print("  Patched twitt/models/ads.py")


# ── 5. twitt/models/statistics.py ──────────────────────────────────────
print("5. models/statistics.py")
p = BL / "twitt/models/statistics.py"
text = p.read_text()
text = text.replace("from instrlib.django.orm import InstrumentORM\n", "")
text = text.replace("from twitt.enforcer import logger\n", "")
text = re.sub(r'@InstrumentORM\([^)]*\)\n', '', text)
p.write_text(text)
print("  Patched twitt/models/statistics.py")


# ── 6. twitt/views/gdpr.py ─────────────────────────────────────────────
print("6. views/gdpr.py")
patch("twitt/views/gdpr.py", [
    ("from instrlib.django.custom_http import redirect, render\n",
     "from django.shortcuts import redirect\nfrom django.shortcuts import render\n"),
])


# ── 7. twitt/views/social.py ───────────────────────────────────────────
print("7. views/social.py")
p = BL / "twitt/views/social.py"
text = p.read_text()
text = text.replace("from instrlib.django.purposes import with_purpose\n", "")
text = text.replace("from instrlib.django.custom_http import redirect, render\n",
                     "from django.shortcuts import redirect\nfrom django.shortcuts import render\n")
# Replace @with_purpose('...') decorator with nothing
text = re.sub(r'\s*@with_purpose\([\'"][^\'"]+[\'"]\)\n', '\n', text)
p.write_text(text)
print("  Patched twitt/views/social.py")


# ── 8. twitt/views/ads.py ──────────────────────────────────────────────
print("8. views/ads.py")
p = BL / "twitt/views/ads.py"
text = p.read_text()
text = text.replace("from instrlib.django.custom_http import redirect\n",
                     "from django.shortcuts import redirect\n")
text = text.replace("from instrlib.django.purposes import with_purpose\n", "")
text = re.sub(r'\s*@with_purpose\([\'"][^\'"]+[\'"]\)\n', '\n', text)
p.write_text(text)
print("  Patched twitt/views/ads.py")


# ── 9. twitt/views/statistics.py ────────────────────────────────────────
print("9. views/statistics.py")
p = BL / "twitt/views/statistics.py"
text = p.read_text()
text = text.replace("from instrlib.django.purposes import with_purpose\n", "")
text = re.sub(r'\s*@with_purpose\([\'"][^\'"]+[\'"]\)\n', '\n', text)
p.write_text(text)
print("  Patched twitt/views/statistics.py")


# ── 10. twitt/middleware.py ─────────────────────────────────────────────
print("10. middleware.py")
p = BL / "twitt/middleware.py"
text = p.read_text()
text = text.replace("from instrlib.django.purposes import with_purpose\n", "")
text = re.sub(r'\s*@with_purpose\([\'"][^\'"]+[\'"]\)\n', '\n', text)
p.write_text(text)
print("  Patched twitt/middleware.py")


# ── 11. twitt/apps.py ──────────────────────────────────────────────────
print("11. apps.py – disable daily_review thread")
p = BL / "twitt/apps.py"
p.write_text("""from django.apps import AppConfig


class TwittConfig(AppConfig):
    default_auto_field = 'django.db.models.BigAutoField'
    name = 'twitt'
""")
print("  Patched twitt/apps.py")


# ── 12. Remove enforcer.py, daily_review.py, instrlib symlink ──────────
print("12. Remove enforcer.py, daily_review.py, instrlib")
for f in ["twitt/enforcer.py", "twitt/daily_review.py", "instrlib", "enfguard",
          "policies/gdpr.py"]:
    target = BL / f
    if target.is_symlink() or target.is_file():
        target.unlink()
        print(f"  Removed {f}")
    elif target.is_dir():
        import shutil
        shutil.rmtree(target)
        print(f"  Removed {f}/")
    else:
        print(f"  {f} not found (ok)")


# ── 13. twitt/context_processors.py ────────────────────────────────────
print("13. context_processors.py")
p = BL / "twitt/context_processors.py"
if p.exists():
    text = p.read_text()
    if "instrlib" in text or "enforcer" in text:
        text = re.sub(r'.*instrlib.*\n', '', text)
        text = re.sub(r'.*enforcer.*\n', '', text)
        p.write_text(text)
        print("  Patched")
    else:
        print("  No instrlib refs")


print("\nDone! Baseline app is ready.")
