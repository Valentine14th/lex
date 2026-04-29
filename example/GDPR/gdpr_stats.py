#!/usr/bin/env python3
"""
Compute the % of the GDPR covered by F, C, E, I, weighted by word count.

Usage: python3 gdpr_stats.py coverage GDPR.xml
"""

import re
import sys
import xml.etree.ElementTree as ET

# ── Symbol → score ───────────────────────────────────────────────────────────
# F: \LEFTcircle = 0.5 (partial formalization)
# C/E/I: \LEFTcircle = 1.0 (any coverage counts as fully covered)
SYM_F   = {r'\CIRCLE': 1.0, r'\LEFTcircle': 0.5, r'\Circle': 0.0}
SYM_CEI = {r'\CIRCLE': 1.0, r'\LEFTcircle': 1.0, r'\Circle': 0.0}

def parse_sym(s, sym=SYM_F):
    for k, v in sym.items():
        if k in s:
            return v
    return None

# ── Coverage table parsing ────────────────────────────────────────────────────

def parse_coverage(path):
    """
    Returns list of (depth, label, f, c, e, i).
    depth: 0=article, 1=paragraph, 2=subparagraph/point, 3=point under subparagraph
    """
    rows = []
    with open(path) as fh:
        for line in fh:
            if '&' not in line:
                continue
            parts = line.split('&')
            if len(parts) < 5:
                continue
            label_col = parts[0]
            # Depth from \hspace{X.Xem}
            m = re.match(r'\s*\\hspace\{(\d+\.\d+)em\}', label_col)
            em = float(m.group(1)) if m else 0.0
            # 1.2→1, 2.2→2, 3.2→3; 0→0
            depth = round(em - 0.2) if em > 0.1 else 0
            # Label: first {\small ...} in label_col
            m_lbl = re.search(r'\{\\small ([^}]+)\}', label_col)
            if not m_lbl:
                continue
            label = m_lbl.group(1).strip()
            # Skip if label contains LaTeX commands (it's a predicate cell, not a section)
            if '\\' in label:
                continue
            f = parse_sym(parts[1], SYM_F)
            c = parse_sym(parts[2], SYM_CEI)
            e = parse_sym(parts[3], SYM_CEI)
            i = parse_sym(parts[4], SYM_CEI)
            if f is None:
                continue
            rows.append((depth, label, f, c, e, i))
    return rows

# ── GDPR XML parsing ──────────────────────────────────────────────────────────

def word_count(el):
    """Count all words in element and descendants."""
    return len(ET.tostring(el, encoding='unicode', method='text').split())

def parse_xml(path):
    """
    Returns articles dict:
      articles[n] = {
        'words': int,
        'paras': {
          p: {
            'words': int,
            'subparas': [ {'words': int, 'points': [int, ...]}, ... ],  # indexed 0-based
            'allpoints': [int, ...]  # flat word-count list for all ITEMs
          }
        }
      }
    """
    root = ET.parse(path).getroot()
    articles = {}
    for art in root.findall('.//ARTICLE'):
        n = int(art.attrib['IDENTIFIER'])
        paras = {}
        for parag in art.findall('PARAG'):
            idf = parag.attrib.get('IDENTIFIER', '0.0')
            pn = int(idf.split('.')[1])
            alineas = parag.findall('ALINEA')
            subparas = []
            allpoints = []
            for al in alineas:
                pts = [word_count(item) for item in al.findall('.//ITEM')]
                allpoints.extend(pts)
                subparas.append({'words': word_count(al), 'points': pts})
            paras[pn] = {
                'words': word_count(parag),
                'subparas': subparas,
                'allpoints': allpoints,
            }
        articles[n] = {'words': word_count(art), 'paras': paras}
    return articles

# ── Label parsing ─────────────────────────────────────────────────────────────

# Normalise en-dash / em-dash / double-hyphen to a single ASCII hyphen
_NORM = re.compile(r'[–—]|--+')

def parse_label(label):
    """
    Returns (kind, start, end) or None.
    kind  : 'article' | 'paragraph' | 'subparagraph' | 'point' | 'point_num'
    start, end: int (numeric) or str (letter)
    """
    label = _NORM.sub('-', label).strip()
    m = re.match(r'(Article|Paragraph|Subparagraph)\s+(\d+)(?:-(\d+))?$', label)
    if m:
        s = int(m.group(2))
        e = int(m.group(3)) if m.group(3) else s
        return (m.group(1).lower(), s, e)
    m = re.match(r'Point\s+\(([a-z])\)(?:-\(([a-z])\))?$', label)
    if m:
        return ('point', m.group(1), m.group(2) if m.group(2) else m.group(1))
    m = re.match(r'Point\s+\((\d+)\)(?:-\((\d+)\))?$', label)
    if m:
        s = int(m.group(1))
        e = int(m.group(2)) if m.group(2) else s
        return ('point_num', s, e)
    return None

def point_indices(start, end):
    """0-based indices for a point range (letter or numeric)."""
    if isinstance(start, str):
        return list(range(ord(start) - ord('a'), ord(end) - ord('a') + 1))
    else:
        return list(range(start - 1, end))   # numeric: 1-based → 0-based

# ── Word-count lookup for a leaf row ─────────────────────────────────────────

def lookup_words(depth, label, ctx, articles):
    """
    ctx[d] = (label, parsed) for the ancestor row at each depth d.
    Returns word count of the XML section(s) covered by this row.
    """
    parsed = parse_label(label)
    if not parsed:
        return 0
    kind, start, end = parsed

    if depth == 0:
        # Article or article-range
        return sum(articles[n]['words'] for n in range(start, end + 1) if n in articles)

    if depth == 1:
        # Paragraph range inside a single article (depth-0 ranges are always leaves)
        if ctx[0] is None:
            return 0
        _, (_, a, _) = ctx[0]
        if a not in articles:
            return 0
        paras = articles[a]['paras']
        return sum(paras[p]['words'] for p in range(start, end + 1) if p in paras)

    if depth == 2:
        if ctx[0] is None or ctx[1] is None:
            return 0
        _, (_, a, _) = ctx[0]
        _, (_, p_start, _) = ctx[1]
        p = p_start
        if a not in articles or p not in articles[a]['paras']:
            return 0
        parag = articles[a]['paras'][p]
        if kind == 'subparagraph':
            total = 0
            for sn in range(start, end + 1):
                idx = sn - 1
                if 0 <= idx < len(parag['subparas']):
                    total += parag['subparas'][idx]['words']
            return total
        else:  # point or point_num
            pts = parag['allpoints']
            return sum(pts[idx] for idx in point_indices(start, end) if idx < len(pts))

    if depth == 3:
        if ctx[0] is None or ctx[1] is None or ctx[2] is None:
            return 0
        _, (_, a, _) = ctx[0]
        _, (_, p_start, _) = ctx[1]
        p = p_start
        _, sp_parsed = ctx[2]
        if sp_parsed is None:
            return 0
        _, sp, _ = sp_parsed
        if a not in articles or p not in articles[a]['paras']:
            return 0
        parag = articles[a]['paras'][p]
        sp_idx = sp - 1
        if sp_idx >= len(parag['subparas']):
            return 0
        subpara = parag['subparas'][sp_idx]
        pts = subpara['points']
        return sum(pts[idx] for idx in point_indices(start, end) if idx < len(pts))

    return 0

# ── Main ──────────────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <coverage.tex> <GDPR.xml>")
        sys.exit(1)

    coverage_path, xml_path = sys.argv[1], sys.argv[2]
    rows = parse_coverage(coverage_path)
    articles = parse_xml(xml_path)

    total_xml_words = sum(a['words'] for a in articles.values())

    # ── Pass 1: collect all leaf rows with a frozen context snapshot ──────────
    leaf_rows = []   # (depth, label, f, c, e, i, ctx_snapshot)
    ctx = [None, None, None, None]
    for idx, (depth, label, f, c, e, i) in enumerate(rows):
        ctx[depth] = (label, parse_label(label))
        for d in range(depth + 1, 4):
            ctx[d] = None
        is_leaf = (idx + 1 >= len(rows)) or (rows[idx + 1][0] <= depth)
        if is_leaf:
            leaf_rows.append((depth, label, f, c, e, i, list(ctx)))

    # ── Pass 2: resolve word counts; fix 0-word leaves by distributing parent ─
    leaf_words = [lookup_words(depth, label, cs, articles)
                  for depth, label, f, c, e, i, cs in leaf_rows]

    def _n_indices(label):
        """Number of sub-clause indices covered by a point/numeric label."""
        p = parse_label(label)
        if p is None:
            return 1
        _, start, end = p
        return (ord(end) - ord(start) + 1) if isinstance(start, str) else (end - start + 1)

    # Group 0-word leaves by their (article_start, para_start) parent key
    from collections import defaultdict
    zero_groups: dict = defaultdict(list)   # (a, p) -> [leaf index]
    for li, (depth, label, f, c, e, i, cs) in enumerate(leaf_rows):
        if leaf_words[li] == 0:
            a_ctx, p_ctx = cs[0], cs[1]
            if a_ctx and a_ctx[1] and p_ctx and p_ctx[1]:
                _, (_, a, _) = a_ctx
                _, (_, p, _) = p_ctx
                zero_groups[(a, p)].append(li)

    for (a, p), indices in zero_groups.items():
        if a not in articles or p not in articles[a]['paras']:
            continue
        para_words = articles[a]['paras'][p]['words']
        total_idx = sum(_n_indices(leaf_rows[li][1]) for li in indices)
        if total_idx == 0:
            continue
        for li in indices:
            leaf_words[li] = round(para_words * _n_indices(leaf_rows[li][1]) / total_idx)

    # Warn if any leaves still have 0 words after the fix
    still_zero = [
        (depth, label, cs)
        for (depth, label, f, c, e, i, cs), w in zip(leaf_rows, leaf_words) if w == 0
    ]
    if still_zero:
        print("Warnings (unmapped provisions):", file=sys.stderr)
        for depth, label, cs in still_zero:
            path = ' > '.join(cs[d][0] for d in range(depth + 1) if cs[d])
            print(f"  0 words: {path}", file=sys.stderr)

    # ── Pass 3: accumulate stats ──────────────────────────────────────────────
    total_words = 0
    weighted = {'f': 0.0, 'c': 0.0, 'e': 0.0, 'i': 0.0}
    weighted_f_for = {'c': 0.0, 'e': 0.0, 'i': 0.0}
    article_f: dict = {}
    article_words: dict = {}
    article_w: dict = {}

    for (depth, label, f, c, e, i, cs), words in zip(leaf_rows, leaf_words):
        total_words += words
        weighted['f'] += f * words
        weighted['c'] += c * words
        weighted['e'] += e * words
        weighted['i'] += i * words
        for _col, _val in [('c', c), ('e', e), ('i', i)]:
            weighted_f_for[_col] += f * _val * words
        if cs[0] is not None and cs[0][1] is not None:
            _, (_, a_start, a_end) = cs[0]
            for _a in range(a_start, a_end + 1):
                article_f[_a] = article_f.get(_a, 0.0) + f * words
                article_words[_a] = article_words.get(_a, 0) + words
                aw = article_w.setdefault(_a, {'f': 0.0, 'c': 0.0, 'e': 0.0, 'i': 0.0})
                aw['f'] += f * words
                aw['c'] += c * words
                aw['e'] += e * words
                aw['i'] += i * words

    total_articles = len(articles)
    targeted = sum(1 for v in article_f.values() if v > 0)
    pct_targeted = 100.0 * targeted / total_articles if total_articles else 0.0

    # Word counts and weighted scores restricted to targeted articles
    targeted_arts = {a for a, v in article_f.items() if v > 0}
    targeted_words = sum(article_words.get(a, 0) for a in targeted_arts)
    targeted_weighted = {col: sum(article_w[a][col] for a in targeted_arts if a in article_w)
                         for col in ('f', 'c', 'e', 'i')}

    f_score   = weighted['f']
    t_f_score = targeted_weighted['f']

    def pct(num, den):
        return 100.0 * num / den if den else 0.0

    rows_data = [
        # (name, pct_law, pct_targeted, pct_f_or_None)
        ('Formalized (F)',
         pct(f_score, total_words),
         pct(t_f_score, targeted_words),
         None),
        ('Conservatively assumed (C)',
         pct(weighted['c'], total_words),
         pct(targeted_weighted['c'], targeted_words),
         pct(weighted_f_for['c'], f_score)),
        ('Enforced at runtime (E)',
         pct(weighted['e'], total_words),
         pct(targeted_weighted['e'], targeted_words),
         pct(weighted_f_for['e'], f_score)),
        ('Informally assumed (I)',
         pct(weighted['i'], total_words),
         pct(targeted_weighted['i'], targeted_words),
         pct(weighted_f_for['i'], f_score)),
    ]

    latex = sys.argv[3] == '--latex' if len(sys.argv) > 3 else False

    if latex:
        print(r'\begin{table}[t]')
        print(r'\centering')
        print(r'\begin{tabular}{@{}lrrr@{}}')
        print(r'\toprule')
        print(r'\textbf{Status} & \textbf{\% of law} & \textbf{\% of targeted arts} & \textbf{\% of F} \\')
        print(r'\midrule')
        print(rf'\multicolumn{{4}}{{@{{}}l}}{{\emph{{Targeted articles: '
              rf'{targeted}/{total_articles} ({pct_targeted:.1f}\%)}}}} \\')
        print(r'\addlinespace[3pt]')
        for name, pl, pt, pf in rows_data:
            pf_str = rf'{pf:.1f}\%' if pf is not None else ''
            print(rf'\small {name} & {pl:.1f}\% & {pt:.1f}\% & {pf_str} \\')
        print(r'\bottomrule')
        print(r'\end{tabular}')
        print(r'\caption{GDPR coverage statistics (weighted by word count). '
              r'F scoring: \textbackslash CIRCLE=1.0, \textbackslash LEFTcircle=0.5, \textbackslash Circle=0.0. '
              r'C/E/I scoring: \textbackslash LEFTcircle counts as 1.0. '
              r'\% of F = fraction of formalized text also covered by C/E/I.}')
        print(r'\label{tab:gdpr-stats}')
        print(r'\end{table}')
    else:
        print(f"\nGDPR Coverage Statistics (weighted by word count)")
        print(f"{'=' * 62}")
        print(f"  Total words in XML (enacting articles): {total_xml_words:,}")
        print(f"  Words attributed to coverage leaves:    {total_words:,}")
        print()
        print(f"  Articles targeted (≥1 formalized provision): {targeted} / {total_articles}  ({pct_targeted:.1f}%)")
        print()
        print(f"  {'Status':<35}  {'% of law':>8}  {'% targeted':>10}  {'% of F':>8}")
        print(f"  {'-'*35}  {'-'*8}  {'-'*10}  {'-'*8}")
        for name, pl, pt, pf in rows_data:
            pf_str = f'{pf:7.1f}%' if pf is not None else ' ' * 8
            print(f"  {name:<35}  {pl:7.1f}%  {pt:9.1f}%  {pf_str}")
        print()
        print("Notes:")
        print("  • % of law      = weighted sum(symbol × words) / total leaf words")
        print("  • % targeted    = same numerator / words in targeted articles only")
        print("  • % of F        = among formalized provisions, fraction also covered by C/E/I")
        print("                    = sum(f_score × cei_score × words) / sum(f_score × words)")
        print("  • F scoring: \\CIRCLE=1.0, \\LEFTcircle=0.5, \\Circle=0.0")
        print("  • C/E/I scoring: \\CIRCLE=1.0, \\LEFTcircle=1.0, \\Circle=0.0")
        print("  • Word count from GDPR.xml (ARTICLE / PARAG / ALINEA / ITEM level).")

if __name__ == '__main__':
    main()
