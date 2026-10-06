#!/usr/bin/env python3
"""pdfcheck.py — Grepy el lector frío del cubo 6, 2026-10-05. Own checks on `pdftotext -bbox` output.

1. Text block: left/right/top/bottom edges measured from the body words (modes), largest xMax overall.
2. Page fill: lowest text line of each page against the bottom of the text block.
3. Folios: words outside the text block vertically (page numbers / running heads).
4. Hyphenation at line ends: every line whose last word ends with a hyphen (-, U+2010, U+2011);
   flags: remainder (first word of the next line, letters only) < 3 letters; first part < 2 letters;
   the broken word already contains a hyphen (compound); the fragment starts with «[» (citation key);
   the word is code (contains «_» or «.py»).
Control: a synthetic page with a known hyphenated compound and a 2-letter remainder must be flagged.
"""
import re, sys, html
from collections import Counter

WRE = re.compile(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>')
HY = ('-', '‐', '‑')

def parse(s):
    pages = s.split('<page ')[1:]
    out = []
    for p in pages:
        ws = [(float(a), float(b), float(c), float(d), html.unescape(w)) for a, b, c, d, w in WRE.findall(p)]
        out.append([w for w in ws if w[4].strip('⁠​') != ''])
    return out

def lines_of(ws):
    tall = [w for w in ws if (w[3] - w[1]) >= 8.0]
    bands = []
    for w in sorted(tall, key=lambda w: (w[1] + w[3]) / 2):
        mid = (w[1] + w[3]) / 2
        if bands and abs(bands[-1][0] - mid) < 3.0:
            bands[-1][1].append(w)
        else:
            bands.append([mid, [w]])
    res = []
    for mid, L in bands:
        L.sort()
        res.append((mid, min(w[0] for w in L), max(w[2] for w in L), min(w[1] for w in L), max(w[3] for w in L), [w[4] for w in L]))
    return res

def hyph_scan(P, label=''):
    flags = []
    total = 0
    for pi, ws in enumerate(P, 1):
        L = lines_of(ws)
        for k in range(len(L)):
            toks = L[k][5]
            last = toks[-1]
            if not last.endswith(HY) or len(last) < 2:
                continue
            # next line: same page, or first line of the next page
            nk = next((j for j in range(k + 1, len(L)) if L[j][0] > L[k][0] + 8), None)
            if nk is not None:
                nxt = L[nk][5]
            elif pi < len(P):
                LL = lines_of(P[pi])
                nxt = LL[0][5] if LL else ['']
            else:
                nxt = ['']
            total += 1
            first = re.sub(r'[^A-Za-z]', '', last[:-1].split('‐')[-1].split('-')[-1])
            rem_tok = nxt[0]
            rem = re.match(r"[A-Za-z]*", rem_tok).group(0)
            why = []
            if 0 < len(rem) < 3 and not re.match(r"[A-Za-z]+[\-‐‑]", rem_tok):
                why.append('remainder<3:%r' % rem_tok)
            if 0 < len(first) < 2:
                why.append('first<2')
            body = last[:-1]
            if re.search(r'[A-Za-z][\-‐‑][A-Za-z]', body) or re.match(r"[A-Za-z]+[\-‐‑]", rem_tok):
                why.append('inside-compound')
            if body.startswith('['):
                why.append('citation-key')
            if '_' in body or '.py' in body:
                why.append('code')
            if why:
                flags.append('%sp%d  «%s» / «%s»  %s' % (label, pi, last, rem_tok, ', '.join(why)))
    return total, flags

def main():
    s = open(sys.argv[1], encoding='utf-8').read()
    P = parse(s)
    # 1. text block
    rights = Counter(); lefts = Counter(); tops = []; bottoms = []
    allx = []
    for pi, ws in enumerate(P, 1):
        L = lines_of(ws)
        for ln in L:
            rights[round(ln[2] * 2) / 2] += 1
            lefts[round(ln[1] * 2) / 2] += 1
        if L:
            tops.append((round(L[0][3], 1), pi)); bottoms.append((round(L[-1][4], 1), pi))
        for w in ws:
            allx.append((w[2], pi, w[4]))
    print('right edges (mode):', rights.most_common(3))
    print('left edges (mode):', lefts.most_common(3))
    mx = max(allx)
    print('largest xMax: %.2f p%d %r' % mx)
    R = rights.most_common(1)[0][0]
    over = sorted([a for a in allx if a[0] > R + 0.5], reverse=True)
    print('words beyond the right edge %.1f + 0.5 pt: %d' % (R, len(over)), over[:5])
    tc = Counter(t for t, _ in tops); bc = Counter(b for b, _ in bottoms)
    print('top of first line (mode):', tc.most_common(3))
    print('bottom of last line (mode):', bc.most_common(3))
    top = tc.most_common(1)[0][0]
    bot = max(b for b, _ in bottoms)
    print('text block: top %.1f, lowest line bottom over all pages %.1f' % (top, bot))
    # 2. page fill
    print('page fill (lowest line bottom − top) / (block bottom − top):')
    under = []
    for b, pi in bottoms:
        f = (b - top) / (bot - top)
        if f < 0.90:
            under.append((pi, round(100 * f)))
    print('  pages under 90 %:', under)
    print('  all pages:', [(pi, round(100 * (b - top) / (bot - top))) for b, pi in bottoms])
    # 3. folios
    outside = []
    for pi, ws in enumerate(P, 1):
        for w in ws:
            if w[1] > bot + 5 or w[3] < top - 5:
                outside.append((pi, w[4], round(w[1])))
    print('words outside the text block vertically:', len(outside), outside[:10])
    # 4. hyphenation
    total, flags = hyph_scan(P)
    print('line-end hyphens:', total, ' flagged:', len(flags))
    for f in flags:
        print('  ' + f)
    # control
    ctrl = [[(54, 100, 300, 110, 'foo'), (310, 100, 540, 110, 'non-in-'), (54, 115, 200, 125, 'creasing'),
             (54, 130, 300, 140, 'reducibili-'), (54, 145, 200, 155, 'ty,'), (54, 160, 300, 170, '[ABER-'),
             (54, 175, 200, 185, 'S55]')]]
    ct, cf = hyph_scan(ctrl, 'CONTROL ')
    print('control: %d hyphens, %d flagged' % (ct, len(cf)))
    for f in cf:
        print('  ' + f)
    print('FIN-OK')

main()
