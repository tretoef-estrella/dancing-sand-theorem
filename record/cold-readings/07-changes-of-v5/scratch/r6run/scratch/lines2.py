#!/usr/bin/env python3
"""lines2.py — Grepy el lector frío del cubo 6, 2026-10-05. Own structure checks on the bbox of the pdf.
1. Word-space baseline: mean gap between consecutive plain words on full-measure lines (same selection as
   gaps_text_words.py), median and percentiles, and lines whose mean gap exceeds 1.5× the median.
2. Page breaks: last line of each page and first line of the next; flag
   (a) two display-like lines (indented on both sides) on either side of the break;
   (b) a heading of the md as the last line of a page.
"""
import re, sys, html, unicodedata
exec(open('scratch/pdfcheck.py').read().split('def main():')[0])
s = open(sys.argv[1], encoding='utf-8').read()
md = open(sys.argv[2], encoding='utf-8').read().split('\n')
P = parse(s)
W = re.compile(r"^[A-Za-z][A-Za-z'’\-‐]*[.,;:)]*$")
rows = []
for pi, ws in enumerate(P, 1):
    lines = {}
    for w in ws:
        lines.setdefault(round((w[1] + w[3]) / 2 / 2.0), []).append(w)
    for k, L in lines.items():
        L.sort()
        if len(L) < 5 or L[0][0] > 80 or L[-1][2] < 538:
            continue
        gaps = [L[i + 1][0] - L[i][2] for i in range(len(L) - 1)]
        if max(gaps) > 45:
            continue
        tg = [gaps[i] for i in range(len(L) - 1) if W.match(L[i][4]) and W.match(L[i + 1][4])]
        if len(tg) < 2:
            continue
        rows.append((sum(tg) / len(tg), pi, ' '.join(w[4] for w in L)[:90]))
g = sorted(r[0] for r in rows)
med = g[len(g) // 2]
print('lines measured %d; mean word gap: median %.2f pt, p90 %.2f, p99 %.2f, max %.2f' % (
    len(g), med, g[int(.9 * len(g))], g[int(.99 * len(g))], g[-1]))
loose = sorted([r for r in rows if r[0] > 1.5 * med], reverse=True)
print('lines with mean gap > 1.5 × median (%.2f pt): %d' % (1.5 * med, len(loose)))
for r in loose:
    print('  %.1f p%d  %s' % r)
# 2. page breaks
def norm(t):
    return re.sub(r'[^a-z0-9]', '', unicodedata.normalize('NFKC', t).lower())
heads = [norm(re.sub(r'^#+ ', '', l)) for l in md if re.match(r'^#{2,3} ', l)]
for i in range(len(P) - 1):
    a, b = lines_of(P[i]), lines_of(P[i + 1])
    if not a or not b:
        continue
    la, fb = a[-1], b[0]
    def disp(ln):
        return ln[1] > 90 and ln[2] < 505
    if disp(la) and disp(fb):
        print('DISPLAYS across p%d/p%d: «%s» / «%s»' % (i + 1, i + 2, ' '.join(la[5])[:50], ' '.join(fb[5])[:50]))
    t = norm(' '.join(la[5]))
    if len(t) > 3 and any(t == h or (h.startswith(t) and len(t) > 8) for h in heads):
        print('HEADING at the foot of p%d: %s' % (i + 1, ' '.join(la[5])))
    print('break p%d/p%d: last «%s» | first «%s»' % (i + 1, i + 2, ' '.join(la[5])[-45:], ' '.join(fb[5])[:45]))
print('FIN-OK')
