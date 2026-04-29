"""
Special-category data classifier (Article 9 GDPR).

Uses simple keyword / phrase matching to flag free-text content that may
reveal information belonging to one of the special categories of personal
data listed in Art. 9(1).  The classifier is intentionally conservative
(high recall, possibly lower precision) because enforcement errs on the
side of protection.

Categories (matching the ``special_data_category`` type in the .rex policy):
    racial_ethnic   – racial or ethnic origin
    political       – political opinions
    religious       – religious or philosophical beliefs
    trade_union     – trade union membership
    genetic         – genetic data
    biometric       – biometric data (for unique identification)
    health          – data concerning health
    sexual          – data concerning sex life or sexual orientation
"""

from __future__ import annotations

import re
from typing import List

# ── Keyword dictionaries ────────────────────────────────────────────────
# Each value is a set of lowercased keywords / short phrases.  A match is
# triggered when any keyword appears as a whole word (\\b boundary) in the
# input text.

_KEYWORDS: dict[str, list[str]] = {
    'racial_ethnic': [
        'race', 'racial', 'ethnicity', 'ethnic', 'african', 'caucasian',
        'hispanic', 'latino', 'latina', 'asian', 'indigenous', 'aboriginal',
        'romani', 'slavic', 'mixed race', 'skin color', 'skin colour',
    ],
    'political': [
        'political', 'politics', 'democrat', 'republican', 'liberal',
        'conservative', 'socialist', 'communist', 'fascist', 'anarchist',
        'left-wing', 'right-wing', 'political party', 'election',
        'referendum', 'vote', 'ballot', 'parliament', 'senate', 'congress',
        'ideology', 'partisan',
    ],
    'religious': [
        'religion', 'religious', 'christian', 'muslim', 'jewish', 'hindu',
        'buddhist', 'sikh', 'atheist', 'agnostic', 'catholic', 'protestant',
        'orthodox', 'evangelical', 'church', 'mosque', 'synagogue', 'temple',
        'quran', 'bible', 'torah', 'prayer', 'philosophical belief',
    ],
    'trade_union': [
        'trade union', 'labor union', 'labour union', 'union member',
        'union membership', 'collective bargaining', 'strike action',
        'workers union', 'syndicate',
    ],
    'genetic': [
        'genetic', 'genome', 'dna', 'chromosom', 'gene mutation',
        'hereditary', 'genotype', 'allele', 'crispr', 'genetic test',
        'gene therapy',
    ],
    'biometric': [
        'biometric', 'fingerprint', 'face recognition', 'facial recognition',
        'retina scan', 'iris scan', 'voice recognition', 'palm print',
        'biometric data',
    ],
    'health': [
        'health', 'medical', 'diagnosis', 'disease', 'illness', 'symptom',
        'prescription', 'medication', 'therapy', 'surgery', 'hospital',
        'doctor', 'patient', 'mental health', 'disability', 'chronic',
        'cancer', 'diabetes', 'hiv', 'aids', 'covid', 'vaccine',
        'psychiatric', 'disorder', 'treatment', 'clinical',
    ],
    'sexual': [
        'sexual orientation', 'sex life', 'homosexual', 'heterosexual',
        'bisexual', 'gay', 'lesbian', 'transgender', 'queer', 'lgbtq',
        'non-binary', 'nonbinary', 'pansexual', 'asexual', 'intersex',
        'gender identity', 'sexual preference',
    ],
}

# Pre-compile one regex per category for performance.
_PATTERNS: dict[str, re.Pattern] = {}

for _cat, _words in _KEYWORDS.items():
    # Sort longest-first so multi-word phrases match before sub-words.
    _sorted = sorted(_words, key=len, reverse=True)
    _alt = '|'.join(re.escape(w) for w in _sorted)
    _PATTERNS[_cat] = re.compile(rf'\b(?:{_alt})\b', re.IGNORECASE)


# ── Public API ──────────────────────────────────────────────────────────

def classify_text(text: str) -> List[str]:
    """Return a sorted list of special-category labels found in *text*.

    >>> classify_text("I went to the mosque for prayer")
    ['religious']
    >>> classify_text("nothing special here")
    []
    """
    if not text:
        return []
    return sorted(cat for cat, pat in _PATTERNS.items() if pat.search(text))


# Convenience constant: all known category keys (same order as SPECIAL_CATEGORY_CHOICES in forms).
SPECIAL_CATEGORIES = sorted(_KEYWORDS.keys())
