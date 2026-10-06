#!/usr/bin/env python3
"""loose.py (v2: text-size boxes >= 14 pt form the lines; gaps >= 15 pt and the gap before ∎ excluded) — Grepy cold reader 7. The stretched word space of every justified line of the pdf.
Input: pdftotext -bbox html (word boxes). Per page, words of normal size (box height >= 8 pt) are banded
into visual lines (centres within 3 pt); every word of any size whose centre lies inside the band's
vertical extent is attached (scripts). A line counts if its last word reaches the right margin (xMax >= 536; a final ≅ ends at 538.9)
and it has >= 4 words. Its stretched space s = the largest gap between two consecutive TEXT words
(alphabetic tokens, trailing punctuation allowed), because a justified line stretches all its word spaces
equally; lines with no text pair use the largest gap below 40 pt (a matrix or a quad is excluded).
Prints the global median of s, and every line with s >= FACTOR * median, sorted by s."""
import re, sys, html, statistics
s = open(sys.argv[1]).read(); FACTOR = float(sys.argv[2]) if len(sys.argv) > 2 else 1.6
pages = s.split('<page ')[1:]
TXT = re.compile(r"^[«(]?[A-Za-z][A-Za-z'’\-]*[.,;:)»]*$")
rows = []; wide = []
for pi, p in enumerate(pages, 1):
    ws = [(float(a), float(b), float(c), float(d), html.unescape(w)) for a, b, c, d, w in
          re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p)]
    ws = [w for w in ws if w[4].strip('⁠​ ') != '']
    tall = sorted([w for w in ws if w[3] - w[1] >= 14.0], key=lambda w: (w[1] + w[3]) / 2)  # text-size boxes only (16.7 body, 14.5/15.1 tables); scripts (11.7) are attached below
    bands = []
    for w in tall:
        mid = (w[1] + w[3]) / 2
        if bands and abs(bands[-1]['mid'] - mid) < 3.0:
            b = bands[-1]; b['w'].append(w); b['y0'] = min(b['y0'], w[1]); b['y1'] = max(b['y1'], w[3])
        else:
            bands.append({'mid': mid, 'w': [w], 'y0': w[1], 'y1': w[3]})
    used = set(id(w) for b in bands for w in b['w'])
    for w in ws:
        if id(w) in used: continue
        c = (w[1] + w[3]) / 2
        for b in bands:
            if b['y0'] <= c <= b['y1']:
                b['w'].append(w); break
    for b in bands:
        L = sorted(b['w'])
        if len(L) < 4 or max(w[2] for w in L) < 536: continue
        gaps = [(L[i + 1][0] - L[i][2], i) for i in range(len(L) - 1)]
        if any(g >= 15 and TXT.match(L[i][4]) and TXT.match(L[i + 1][4]) for g, i in gaps):
            wide.append((pi, round(b['mid']), ' '.join(w[4] for w in L)[:110]))
        tg = [g for g, i in gaps if g < 15 and TXT.match(L[i][4]) and TXT.match(L[i + 1][4])]
        if tg: sv = max(tg); kind = 'text'
        else:
            og = [g for g, i in gaps if g < 15 and '∎' not in L[i + 1][4]]
            if not og: continue
            sv = max(og); kind = 'formula'
        rows.append((sv, pi, round(b['mid']), kind, ' '.join(w[4] for w in L)))
med = statistics.median(r[0] for r in rows)
print('justified lines: %d   median stretched space: %.2f pt' % (len(rows), med))
for f in (1.4, 1.6, 1.8, 2.0, 2.5):
    print('  lines with s >= %.1f x median (%.2f pt): %d' % (f, f * med, sum(r[0] >= f * med for r in rows)))
print('text pairs with a gap >= 15 pt (an object between two words, e.g. a matrix):', len(wide))
for x in wide: print('   p%d y=%d %s' % x)
print('-----')
for r in sorted(rows, reverse=True):
    if r[0] < FACTOR * med: break
    print('%5.2f pt (%.2fx) p%-2d y=%-4d %-7s %s' % (r[0], r[0] / med, r[1], r[2], r[3], r[4][:110]))
