#!/usr/bin/env python3
"""
classify_coverage.py – Classify GDPR articles/paragraphs/points by formalization
and assumption status.

Usage:
    python classify_coverage.py [--ascii] <total_articles> <lex_file> <rex_file> [annotations_file]

Examples:
    python classify_coverage.py 99 gdpr.lex minitwit_gdpr.rex
    python classify_coverage.py 99 gdpr.lex minitwit_gdpr.rex my_annotations.tsv
    python classify_coverage.py --ascii 99 gdpr.lex minitwit_gdpr.rex

Default output is a LaTeX longtable (stdout).  Use --ascii for the plain-text table.

Annotation convention in the .rex file
---------------------------------------
By default every `assume` statement is treated as a *functional* assumption
(an assumption about the system's design, e.g. "no transfers are performed").

To mark an assumption as *legal* (an assumption that relies on a non-obvious
legal interpretation, e.g. "the processing is fair"), add `# legal` either:
  • on the same line:      assume true IsFair  # legal
  • on the preceding line: # legal
                           assume true IsFair
Similarly, `# functional` can be used explicitly (it is the default).

Annotations file (optional, tab-separated)
-------------------------------------------
Each non-comment line has the form::

    section_path<TAB>relevant<TAB>enforcement

where:
  • section_path   full hierarchical label, e.g. "Art. 5 Para. 1 Point (a)"
                   (for articles use just "Art. 5", omit the parenthetical title)
  • relevant       Y or N  (default: unspecified → shown as ? in LaTeX output)
  • enforcement    enforced, assumed, or partial  (default: auto-detected)

Lines starting with # are ignored.

LaTeX column legend
-------------------
  F  Formalized   ● = yes  ○ = no
  R  Relevant     ● = yes  ○ = no  ? = unspecified
  E  Enforcement  ● = enforced  ○ = assumed  ◐ = partial  --- = N/A
Required LaTeX packages: booktabs, longtable, wasysym
"""

import re
import sys
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple


# ─── Data model ───────────────────────────────────────────────────────────────

class AsmKind(Enum):
    FUNCTIONAL = "functional"
    LEGAL      = "legal"


@dataclass
class AsmInfo:
    """Holds the kind and assumed boolean value of a single ``assume`` statement."""
    kind:  AsmKind
    value: bool    # True = assumed true, False = assumed false


class Status(Enum):
    NOT_FORMALIZED = 0   # no rules at all in this section
    FORMALIZED     = 1   # rules present, no assumed events
    FUNCTIONAL_ASM = 2   # rules present, some events are functional assumptions
    LEGAL_ASM      = 3   # rules present, some events are legal assumptions

    def combine(self, other: "Status") -> "Status":
        return Status(max(self.value, other.value))

    def label(self) -> str:
        return {
            Status.NOT_FORMALIZED: "not formalized",
            Status.FORMALIZED:     "formalized",
            Status.FUNCTIONAL_ASM: "functional assumption",
            Status.LEGAL_ASM:      "legal assumption",
        }[self]

    def icon(self) -> str:
        return {
            Status.NOT_FORMALIZED: "✗",
            Status.FORMALIZED:     "✓",
            Status.FUNCTIONAL_ASM: "◎",
            Status.LEGAL_ASM:      "⚠",
        }[self]


@dataclass
class Rule:
    name: Optional[str]
    events: Set[str]


@dataclass
class Section:
    kind: str                         # 'article' | 'paragraph' | 'point'
    sid: str                          # "5", "1", "a", …
    title: Optional[str]
    rules: List[Rule] = field(default_factory=list)
    children: List["Section"] = field(default_factory=list)

    # ── helpers ──────────────────────────────────────────────────────────────

    def direct_events(self) -> Set[str]:
        s: Set[str] = set()
        for r in self.rules:
            s |= r.events
        return s

    def all_events(self) -> Set[str]:
        s = self.direct_events()
        for c in self.children:
            s |= c.all_events()
        return s

    def has_any_rules(self) -> bool:
        if self.rules:
            return True
        return any(c.has_any_rules() for c in self.children)

    def classify(self, assumptions: Dict[str, AsmInfo]) -> Tuple[
            "Status", Dict[str, bool], Dict[str, bool], bool, bool, bool]:
        """
        Returns::

            (status,
             legal_evts_direct,   # direct rules only: event → assumed_value
             func_evts_direct,    # direct rules only: event → assumed_value
             subtree_has_legal,   # any legal-assumed event anywhere in subtree
             subtree_has_func,    # any functional-assumed event anywhere in subtree
             subtree_has_pure)    # any event NOT in assumptions anywhere in subtree

        ``status`` is aggregated over the whole subtree.
        The returned event dicts contain only events from this section's OWN
        direct rules (not children), so parent rows don't duplicate child detail.
        """
        if not self.has_any_rules():
            return Status.NOT_FORMALIZED, {}, {}, False, False, False

        subtree_has_legal = False
        subtree_has_func  = False
        subtree_has_pure  = False
        for ev in self.all_events():
            if ev in assumptions:
                if assumptions[ev].kind == AsmKind.LEGAL:
                    subtree_has_legal = True
                else:
                    subtree_has_func = True
            else:
                subtree_has_pure = True

        if subtree_has_legal:
            st = Status.LEGAL_ASM
        elif subtree_has_func:
            st = Status.FUNCTIONAL_ASM
        else:
            st = Status.FORMALIZED

        legal_evts: Dict[str, bool] = {}
        func_evts:  Dict[str, bool] = {}
        for ev in self.direct_events():
            if ev in assumptions:
                info = assumptions[ev]
                if info.kind == AsmKind.LEGAL:
                    legal_evts[ev] = info.value
                else:
                    func_evts[ev] = info.value

        return st, legal_evts, func_evts, subtree_has_legal, subtree_has_func, subtree_has_pure


# ─── REX parsing ──────────────────────────────────────────────────────────────

def parse_assumptions(rex_path: str) -> Dict[str, AsmInfo]:
    """Return ``{event_name: AsmInfo}`` from ``assume`` statements in the rex file."""
    result: Dict[str, AsmInfo] = {}
    with open(rex_path, encoding="utf-8") as fh:
        lines = fh.readlines()

    pending: Optional[AsmKind] = None
    for line in lines:
        stripped = line.strip()

        # Standalone annotation comments
        if stripped == "# legal":
            pending = AsmKind.LEGAL
            continue
        if stripped == "# functional":
            pending = AsmKind.FUNCTIONAL
            continue

        m = re.match(r"assume\s+(true|false)\s+(\w+)", stripped)
        if m:
            val   = (m.group(1) == "true")
            event = m.group(2)
            if "# legal" in line:
                kind = AsmKind.LEGAL
            elif "# functional" in line:
                kind = AsmKind.FUNCTIONAL
            elif pending is not None:
                kind = pending
            else:
                kind = AsmKind.FUNCTIONAL  # default
            result[event] = AsmInfo(kind=kind, value=val)
            pending = None
        else:
            # Any non-blank, non-comment line resets the pending annotation
            if stripped and not stripped.startswith("#") and not stripped.startswith('"""'):
                pending = None

    return result


# ─── Annotation file ──────────────────────────────────────────────────────────

@dataclass
class Annotation:
    """Per-section user-supplied annotations read from a TSV file."""
    relevant:    Optional[bool] = None   # True = Y, False = N, None = unspecified
    enforcement: Optional[str]  = None   # "enforced" | "assumed" | "partial" | None = auto


def parse_annotations(path: str) -> Dict[str, "Annotation"]:
    """
    Read a tab-separated annotation file.  Each data line::

        section_path<TAB>relevant<TAB>enforcement

    Lines starting with ``#`` are ignored.
    """
    result: Dict[str, Annotation] = {}
    with open(path, encoding="utf-8") as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            if not line or line.startswith("#"):
                continue
            parts = line.split("\t")
            sec     = parts[0].strip()
            rel_raw = parts[1].strip().upper() if len(parts) > 1 else ""
            enf_raw = parts[2].strip().lower() if len(parts) > 2 else ""

            rel: Optional[bool] = None
            if   rel_raw == "Y": rel = True
            elif rel_raw == "N": rel = False

            enf: Optional[str] = None
            if enf_raw in ("enforced", "assumed", "partial"):
                enf = enf_raw

            result[sec] = Annotation(relevant=rel, enforcement=enf)
    return result


# ─── LEX parsing ──────────────────────────────────────────────────────────────

# PascalCase regex: starts with capital, contains ≥1 lower-case char,
# so all-caps keywords (EXISTS, ONCE, AND, …) are excluded.
_PASCAL = re.compile(r"\b([A-Z][a-zA-Z0-9]*[a-z][a-zA-Z0-9]*)\b")

# Keywords that terminate a rule block when seen at the start of a stripped line
_TERMINATORS = re.compile(
    r"^(?:article|paragraph|point|rule\b|note\b|observable\b|suppressable\b|"
    r"causable\b|internal\b|function\b|type\b|import\b|law\b|replace\b|refine\b)"
)

_ARTICLE_RE   = re.compile(r'^article\s+"([^"]+)"(?:\s+"([^"]*)")?')
_PARA_RE      = re.compile(r'^paragraph(\[\d+\])?\s+"([^"]+)"')
_POINT_RE     = re.compile(r'^point\s+"([^"]+)"')
_RULE_RE      = re.compile(r'^rule(?:\s+"([^"]*)")?(?:\s|$)')


def _extract_events(text: str) -> Set[str]:
    return set(_PASCAL.findall(text))


def parse_lex(lex_path: str) -> List[Section]:
    """Parse a .lex file and return a flat list of top-level Article sections."""
    with open(lex_path, encoding="utf-8") as fh:
        lines = fh.readlines()

    articles: List[Section] = []
    art:        Optional[Section] = None
    outer_para: Optional[Section] = None   # most recent bare paragraph "N"
    para:       Optional[Section] = None   # most recent paragraph or subparagraph
    point:      Optional[Section] = None

    in_rule = False
    rule_name: Optional[str] = None
    rule_lines: List[str] = []

    def finish_rule() -> None:
        nonlocal in_rule, rule_name, rule_lines
        if not in_rule:
            return
        events = _extract_events("\n".join(rule_lines))
        r = Rule(name=rule_name, events=events)
        target = point or para or art
        if target is not None:
            target.rules.append(r)
        in_rule = False
        rule_name = None
        rule_lines = []

    for raw_line in lines:
        stripped = raw_line.strip()
        # Only treat a line as a structural declaration when it starts at
        # column 0 (no leading whitespace). Indented occurrences of
        # 'article', 'paragraph', etc. inside rule bodies (e.g. scope
        # clauses) must not be mistaken for new section declarations.
        is_toplevel = bool(raw_line) and not raw_line[0].isspace()

        if is_toplevel:
            # ── article ──────────────────────────────────────────────────────
            m = _ARTICLE_RE.match(stripped)
            if m:
                finish_rule()
                art_id, art_title = m.group(1), m.group(2)
                art        = Section("article", art_id, art_title)
                outer_para = None
                para       = None
                point      = None
                articles.append(art)
                continue

            # ── paragraph / subparagraph ─────────────────────────────────────
            m = _PARA_RE.match(stripped)
            if m and art is not None:
                finish_rule()
                qualifier = m.group(1)   # "[1]" or None
                pid       = m.group(2)   # number string, e.g. "1", "2"
                point     = None
                if qualifier:
                    # subparagraph: nest under the enclosing paragraph (or art)
                    parent  = outer_para or art
                    new_sec = Section("subparagraph", pid, None)
                    parent.children.append(new_sec)
                    para = new_sec
                    # outer_para is NOT updated — subparas don't become new anchors
                else:
                    # ordinary paragraph: direct child of article
                    new_sec    = Section("paragraph", pid, None)
                    art.children.append(new_sec)
                    outer_para = new_sec
                    para       = new_sec
                continue

            # ── point ─────────────────────────────────────────────────────────
            m = _POINT_RE.match(stripped)
            if m and art is not None:
                finish_rule()
                pt_id = m.group(1)
                point = Section("point", pt_id, None)
                (para or art).children.append(point)
                continue

            # ── rule ─────────────────────────────────────────────────────────
            m = _RULE_RE.match(stripped)
            if m and art is not None:
                finish_rule()
                in_rule   = True
                rule_name = m.group(1)
                rule_lines = []
                continue

            # ── any other terminator (at column 0) ───────────────────────────
            if _TERMINATORS.match(stripped):
                finish_rule()
                continue

        # ── accumulate rule body (indented lines, or non-structural content) ─
        if in_rule:
            rule_lines.append(raw_line)

    finish_rule()
    return articles


# ─── Shared rendering helpers ────────────────────────────────────────────────

def _sort_key(s: str) -> Tuple:
    """Sort section ids numerically where possible."""
    base = re.sub(r"\[.*\]", "", s)
    try:
        return (0, int(base))
    except ValueError:
        return (1, base)


def _truncate(s: str, max_len: int) -> str:
    if len(s) <= max_len:
        return s
    return s[:max_len - 1] + "…"


def _para_base_num(sid: str) -> int:
    """Numeric base of a paragraph id, ignoring [n] qualifiers."""
    base = re.sub(r"\[.*\]", "", sid)
    try:
        return int(base)
    except ValueError:
        return -1


def _gap_fill_by_num(children: List[Section], kind: str) -> List[Section]:
    """Insert placeholder sections for numeric gaps within a list."""
    present = [c for c in children if c.kind == kind]
    nums = sorted(set(_para_base_num(c.sid) for c in present
                      if _para_base_num(c.sid) > 0))
    if len(nums) < 2:
        return children
    existing = set(nums)
    extras: List[Section] = [
        Section(kind, str(n), None)
        for n in range(min(nums), max(nums) + 1)
        if n not in existing
    ]
    if not extras:
        return children
    combined = list(children) + extras
    combined.sort(key=lambda c: (_para_base_num(c.sid)
                                 if _para_base_num(c.sid) > 0 else 9999,
                                 c.sid))
    return combined


def _children_with_point_gaps(children: List[Section]) -> List[Section]:
    """Insert placeholder NOT_FORMALIZED points for alphabetic gaps."""
    points  = [c for c in children if c.kind == "point"]
    letters = [c.sid for c in points if len(c.sid) == 1 and c.sid.isalpha()]
    if len(letters) < 2:
        return children
    lo = min(letters)
    hi = max(letters)
    existing = set(letters)
    extras: List[Section] = []
    for ch in (chr(o) for o in range(ord(lo), ord(hi) + 1)):
        if ch not in existing:
            extras.append(Section("point", ch, None))
    if not extras:
        return children
    combined = list(children) + extras
    combined.sort(key=lambda c: (c.sid if len(c.sid) == 1 and c.sid.isalpha()
                                 else chr(ord('z') + 1) + c.sid))
    return combined


def _bare_section_id(label: str) -> str:
    """Extract just the id/letter from a bare label for range display."""
    m = re.match(r"(?:Article|Subparagraph|Paragraph|Point)\s+(\S+)", label)
    if m:
        return m.group(1).strip("()")
    return label


def _section_prefix(label: str) -> str:
    """Return the keyword prefix of a label."""
    for p in ("Article", "Subparagraph", "Paragraph", "Point"):
        if label.startswith(p):
            return p
    return ""


def _merge_labels(first: str, last: str, count: int) -> str:
    """Build a merged label from the first and last bare labels."""
    if count == 1:
        return first
    prefix = _section_prefix(first)
    fid    = _bare_section_id(first)
    lid    = _bare_section_id(last)
    if prefix == "Point":
        return f"Point ({fid})–({lid})"
    return f"{prefix} {fid}–{lid}"


def _bare_label(sec: Section, include_title: bool = True) -> str:
    """Bare display label (no indent) for a section."""
    if sec.kind == "article":
        title = f" ({sec.title})" if (include_title and sec.title) else ""
        return f"Article {sec.sid}{title}"
    if sec.kind == "paragraph":
        return f"Paragraph {sec.sid}"
    if sec.kind == "subparagraph":
        return f"Subparagraph {sec.sid}"
    return f"Point ({sec.sid})"


def _annotation_key(sec: Section, parent_key: str = "") -> str:
    """Canonical lookup key for the annotations dict (fully qualified, no title)."""
    if sec.kind == "article":
        part = f"Article {sec.sid}"
    elif sec.kind == "paragraph":
        part = f"Paragraph {sec.sid}"
    elif sec.kind == "subparagraph":
        part = f"Subparagraph {sec.sid}"
    else:
        part = f"Point ({sec.sid})"
    return (parent_key + " " + part).strip()


def _ordered_children(sec: Section) -> List[Section]:
    """Return sec's children in display order with gap-filling."""
    para_ch    = _gap_fill_by_num([c for c in sec.children if c.kind == "paragraph"],    "paragraph")
    subpara_ch = _gap_fill_by_num([c for c in sec.children if c.kind == "subparagraph"], "subparagraph")
    point_ch   = _children_with_point_gaps([c for c in sec.children if c.kind == "point"])
    other_ch   = [c for c in sec.children if c.kind not in ("paragraph", "subparagraph", "point")]
    return para_ch + subpara_ch + point_ch + other_ch


# ─── ASCII table rendering ────────────────────────────────────────────────────

def _wrap_events(leg: Dict[str, bool], func: Dict[str, bool], width: int) -> List[str]:
    """
    Format assumed events into lines of at most *width* chars.
    Legal events are shown first (``⚠ ``), functional with ``◎ ``.
    Each event is shown as ``Name(T)`` or ``Name(F)``.
    """
    import textwrap
    out: List[str] = []
    for prefix, evts in [("⚠ legal: ", leg), ("◎ func: ", func)]:
        if not evts:
            continue
        joined = prefix + ", ".join(
            f"{k}({'T' if v else 'F'})" for k, v in sorted(evts.items()))
        indent = " " * len(prefix)
        wrapped = textwrap.wrap(joined, width=width, subsequent_indent=indent)
        out.extend(wrapped)
    return out or [""]


def _render_table(articles: List[Section],
                  assumptions: Dict[str, AsmInfo],
                  total_articles: int,
                  section_col_width: int = 48,
                  events_col_width: int = 60) -> None:
    """Print the full classification ASCII table to stdout."""

    COL_SECTION = section_col_width
    COL_STATUS  = 22

    raw: List[Tuple[int, str, Status, List[str]]] = []
    art_map: Dict[str, Section] = {a.sid: a for a in articles}

    def process_section(sec: Section, indent: int) -> None:
        st, leg, func, *_ = sec.classify(assumptions)
        ev_lines = _wrap_events(leg, func, events_col_width)
        raw.append((indent, _bare_label(sec), st, ev_lines))
        for child in _ordered_children(sec):
            process_section(child, indent + 1)

    for art_num in range(1, total_articles + 1):
        art_id = str(art_num)
        if art_id in art_map:
            process_section(art_map[art_id], 0)
        else:
            raw.append((0, f"Article {art_num}", Status.NOT_FORMALIZED, [""]))

    CLEAN = {Status.NOT_FORMALIZED, Status.FORMALIZED}

    def _has_children(i: int) -> bool:
        return i + 1 < len(raw) and raw[i + 1][0] > raw[i][0]

    merged: List[Tuple[str, Status, List[str]]] = []
    i = 0
    while i < len(raw):
        indent, label, st, ev_lines = raw[i]
        if st in CLEAN and not _has_children(i):
            run_labels = [label]
            j = i + 1
            while j < len(raw):
                jind, jlabel, jst, _ = raw[j]
                if jind == indent and jst == st and not _has_children(j):
                    run_labels.append(jlabel)
                    j += 1
                else:
                    break
            merged_label = "  " * indent + _merge_labels(
                run_labels[0], run_labels[-1], len(run_labels))
            merged.append((_truncate(merged_label, COL_SECTION), st, ev_lines))
            i = j
        else:
            full_label = "  " * indent + label
            merged.append((_truncate(full_label, COL_SECTION), st, ev_lines))
            i += 1

    w0 = COL_SECTION
    w1 = COL_STATUS
    w2 = events_col_width
    sep  = f"+-{'-'*w0}-+-{'-'*w1}-+-{'-'*w2}-+"
    hdr  = f"| {'Section':<{w0}} | {'Status':<{w1}} | {'Assumed events':<{w2}} |"
    fmtl = lambda a, b, c: f"| {a:<{w0}} | {b:<{w1}} | {c:<{w2}} |"

    print()
    print(sep)
    print(hdr)
    print(sep)
    for (sec_str, st, ev_lines) in merged:
        st_str = f"{st.icon()} {st.label()}"
        print(fmtl(sec_str, st_str, ev_lines[0]))
        for ev_line in ev_lines[1:]:
            print(fmtl("", "", ev_line))
    print(sep)
    print()

    counts: Dict[Status, int] = {s: 0 for s in Status}
    for (_, _, st, _) in raw:
        counts[st] += 1

    print("Summary (all section levels)")
    print("-----------------------------")
    for st in Status:
        print(f"  {st.icon()} {st.label():<22}: {counts[st]}")
    print()


# ─── LaTeX table rendering ────────────────────────────────────────────────────

def render_latex(articles: List[Section],
                 assumptions: Dict[str, AsmInfo],
                 total_articles: int,
                 annotations: Optional[Dict[str, "Annotation"]] = None) -> None:
    """Print a LaTeX ``longtable`` classifying all sections to stdout."""
    if annotations is None:
        annotations = {}

    art_map: Dict[str, Section] = {a.sid: a for a in articles}

    # raw row: (indent, bare_label, ann_key, st, leg, func, hl, hf, hp)
    raw: List[Tuple[int, str, str, Status,
                    Dict[str, bool], Dict[str, bool],
                    bool, bool, bool]] = []

    def process_section(sec: Section, indent: int, parent_key: str = "") -> None:
        st, leg, func, hl, hf, hp = sec.classify(assumptions)
        key = _annotation_key(sec, parent_key)
        raw.append((indent, _bare_label(sec, include_title=False), key, st, leg, func, hl, hf, hp))
        for child in _ordered_children(sec):
            process_section(child, indent + 1, key)

    for art_num in range(1, total_articles + 1):
        art_id = str(art_num)
        if art_id in art_map:
            process_section(art_map[art_id], 0)
        else:
            bare = f"Article {art_num}"
            raw.append((0, bare, bare, Status.NOT_FORMALIZED, {}, {}, False, False, False))

    # ── merge consecutive clean, childless rows ───────────────────────────────
    CLEAN = {Status.NOT_FORMALIZED, Status.FORMALIZED}

    def _has_children(i: int) -> bool:
        return i + 1 < len(raw) and raw[i + 1][0] > raw[i][0]

    merged = []
    i = 0
    while i < len(raw):
        indent, bare, key, st, leg, func, hl, hf, hp = raw[i]
        if st in CLEAN and not _has_children(i):
            run = [(bare, key)]
            j = i + 1
            while j < len(raw):
                jind, jbare, jkey, jst, *_ = raw[j]
                if jind == indent and jst == st and not _has_children(j):
                    run.append((jbare, jkey))
                    j += 1
                else:
                    break
            merged_bare = _merge_labels(run[0][0], run[-1][0], len(run))
            merged.append((indent, merged_bare, run[0][1], st, leg, func, hl, hf, hp))
            i = j
        else:
            merged.append((indent, bare, key, st, leg, func, hl, hf, hp))
            i += 1

    # ── latex helpers ─────────────────────────────────────────────────────────

    def _latex_escape(s: str) -> str:
        s = s.replace("\\", r"\textbackslash{}")
        for ch, esc in [("&", r"\&"), ("%", r"\%"), ("$", r"\$"),
                        ("#", r"\#"), ("_", r"\_"), ("{", r"\{"),
                        ("}", r"\}"), ("~", r"\textasciitilde{}"),
                        ("^", r"\textasciicircum{}")]:
            s = s.replace(ch, esc)
        return s

    def _fmt_all_asms(leg: Dict[str, bool], func: Dict[str, bool]) -> str:
        """List all assumed predicates (legal + functional) without distinction."""
        all_evts = sorted(set(leg) | set(func))
        if not all_evts:
            return ""
        items = ", ".join(r"\texttt{" + _latex_escape(k) + "}" for k in all_evts)
        return r"{\small " + items + "}"

    # F: formalized  ● = yes  ○ = no
    def _sym_f(st: Status) -> str:
        return r"\CIRCLE" if st != Status.NOT_FORMALIZED else r"\Circle"

    # C: conservatively (functionally) assumed  ● = has func asms  ○ = none
    def _sym_c(st: Status, has_func: bool) -> str:
        if st == Status.NOT_FORMALIZED:
            return r"\Circle"
        return r"\CIRCLE" if has_func else r"\Circle"

    # E: enforced  ● = fully enforced (no assumptions)  ○ = not enforced  ◐ = partial
    def _sym_e(ann_enf: Optional[str], st: Status,
               has_legal: bool, has_func: bool) -> str:
        if st == Status.NOT_FORMALIZED:
            return r"\Circle"
        if ann_enf == "enforced": return r"\CIRCLE"
        if ann_enf == "assumed":  return r"\Circle"
        if ann_enf == "partial":  return r"\LEFTcircle"
        # auto-detect: enforced iff no assumptions at all
        if not has_legal and not has_func:
            return r"\CIRCLE"
        if has_legal and has_func:
            return r"\LEFTcircle"
        return r"\Circle"

    # I: informally (legally) assumed  ● = has legal asms  ○ = none
    def _sym_i(st: Status, has_legal: bool) -> str:
        if st == Status.NOT_FORMALIZED:
            return r"\Circle"
        return r"\CIRCLE" if has_legal else r"\Circle"

    # ── emit LaTeX ────────────────────────────────────────────────────────────
    print("% " + "─" * 67)
    print("% Generated by classify_coverage.py")
    print("% Required packages: booktabs, longtable, wasysym")
    print("%")
    print("% Column legend:")
    print("%   F  Formalized              \\CIRCLE = yes   \\Circle = no")
    print("%   C  Conservatively assumed  \\CIRCLE = has functional assumptions   \\Circle = none")
    print("%   E  Enforced                \\CIRCLE = fully enforced   \\Circle = not enforced   \\LEFTcircle = partial")
    print("%   I  Informally assumed      \\CIRCLE = has legal assumptions   \\Circle = none")
    print("% " + "─" * 67)
    print()
    print(r"\begin{longtable}{@{}lccccl@{}}")
    print(r"\toprule")
    hdr_row = (r"\textbf{Section} &"
               r" \textbf{F} & \textbf{C} & \textbf{E} & \textbf{I} &"
               r" \textbf{Assumed predicates} \\")
    print(hdr_row)
    print(r"\midrule")
    print(r"\endfirsthead")
    print(r"\toprule")
    print(hdr_row)
    print(r"\midrule")
    print(r"\endhead")
    print(r"\bottomrule")
    print(r"\endfoot")
    print()

    prev_indent = 0
    for (indent, bare, key, st, leg, func, hl, hf, hp) in merged:
        if indent == 0 and prev_indent > 0:
            print(r"\addlinespace[4pt]")
        prev_indent = indent

        ann   = annotations.get(key, Annotation())
        f_sym = _sym_f(st)
        c_sym = _sym_c(st, hl or hf)
        e_sym = _sym_e(ann.enforcement, st, hl, hf or hp)
        i_sym = _sym_i(st, hl)

        asm_str = _fmt_all_asms(leg, func)

        hspace = (r"\hspace{" + str(indent) + r".2em}") if indent > 0 else ""
        label_latex = hspace + r"{\small " + _latex_escape(bare) + "}"

        print(f"{label_latex} & {f_sym} & {c_sym} & {e_sym} & {i_sym} & "
              f"{asm_str} \\\\")

    print()
    print(r"\end{longtable}")
    print()



# ─── Entry point ──────────────────────────────────────────────────────────────

def main() -> None:
    args = sys.argv[1:]

    ascii_mode = False
    if args and args[0] == "--ascii":
        ascii_mode = True
        args = args[1:]

    if len(args) not in (3, 4):
        print(__doc__)
        sys.exit(1)

    total_articles = int(args[0])
    lex_path       = args[1]
    rex_path       = args[2]
    ann_path       = args[3] if len(args) == 4 else None

    print(f"Parsing {lex_path} …", file=sys.stderr)
    articles = parse_lex(lex_path)
    print(f"  Found {len(articles)} article(s) in the lex file.", file=sys.stderr)

    print(f"Parsing {rex_path} …", file=sys.stderr)
    assumptions = parse_assumptions(rex_path)
    legal_count = sum(1 for v in assumptions.values() if v.kind == AsmKind.LEGAL)
    func_count  = sum(1 for v in assumptions.values() if v.kind == AsmKind.FUNCTIONAL)
    print(f"  Found {len(assumptions)} assume statement(s): "
          f"{legal_count} legal, {func_count} functional.", file=sys.stderr)

    annotations: Dict[str, Annotation] = {}
    if ann_path:
        print(f"Parsing annotations {ann_path} …", file=sys.stderr)
        annotations = parse_annotations(ann_path)
        print(f"  Found {len(annotations)} annotation(s).", file=sys.stderr)

    print(f"\nGenerating coverage table for {total_articles} articles …\n",
          file=sys.stderr)

    if ascii_mode:
        _render_table(articles, assumptions, total_articles,
                      section_col_width=48, events_col_width=55)
    else:
        render_latex(articles, assumptions, total_articles, annotations)


if __name__ == "__main__":
    main()
