# widows.py — cold reader 5. Single lines of a paragraph alone at the top (widow) or the foot (orphan) of a page.
import re, sys, html
s = open(sys.argv[1]).read()
pages = s.split('<page ')[1:]
def lines_of(p):
    ws = [(float(a), float(b), float(c), float(d), html.unescape(w)) for a, b, c, d, w in
          re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p)]
    tall = [w for w in ws if (w[3] - w[1]) >= 8.0 and w[4].strip('⁠') != '']
    bands = []
    for w in sorted(tall, key=lambda w: (w[1] + w[3]) / 2):
        mid = (w[1] + w[3]) / 2
        if bands and abs(bands[-1][0] - mid) < 3.0:
            bands[-1][1].append(w)
        else:
            bands.append([mid, [w]])
    out = []
    for mid, L in bands:
        L.sort()
        out.append((mid, L[0][0], max(w[2] for w in L), ' '.join(w[4] for w in L)))
    return out
P = [lines_of(p) for p in pages]
for i in range(len(P) - 1):
    a, b = P[i], P[i + 1]
    if not a or not b: continue
    # orphan: last line of page i is the first line of a paragraph that continues
    if len(a) >= 2:
        gap_before = a[-1][0] - a[-2][0]
        full = a[-1][2] > 535
        if full and gap_before > 17 and b[0][1] < 60:
            print('ORPHAN? p%d foot: %s  [gap %.1f]' % (i + 1, a[-1][3][:80], gap_before))
    # widow: first line of page i+1 is the last line of a paragraph started on page i
    if len(b) >= 2:
        short = b[0][2] < 500
        gap_after = b[1][0] - b[0][0]
        if short and gap_after > 17 and a[-1][2] > 535:
            print('WIDOW?  p%d top:  %s  [gap after %.1f]' % (i + 2, b[0][3][:80], gap_after))
print('FIN-OK')
