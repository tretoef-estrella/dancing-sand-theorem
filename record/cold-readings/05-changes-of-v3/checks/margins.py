# margins.py — cold reader 5. Right text margin of the v3 pdf, from `pdftotext -bbox`.
import re, sys, html
from collections import Counter
s = open(sys.argv[1]).read()
pages = s.split('<page ')[1:]
allw = []
for pi, p in enumerate(pages, 1):
    for a, b, c, d, w in re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p):
        allw.append((float(c), pi, float(a), float(b), html.unescape(w)))
# the body right edge: mode of xMax rounded to 0.5 pt among the rightmost word of each line
lines = {}
for xM, pi, xm, y, w in allw:
    lines.setdefault((pi, round(y)), []).append(xM)
right = Counter(round(max(v) * 2) / 2 for v in lines.values())
print('most common right edges of lines (pt):', right.most_common(6))
mx = max(allw)
print('largest xMax: %.2f on p%d word %r (xMin %.2f)' % (mx[0], mx[1], mx[4], mx[2]))
over = sorted([w for w in allw if w[0] > 542.5], reverse=True)
print('words with xMax > 542.5:', len(over))
for w in over[:20]:
    print('  %.2f p%d %r' % (w[0], w[1], w[4]))
left = Counter(round(min(w[2] for w in allw if w[1] == pi) * 2) / 2 for pi in range(1, len(pages) + 1))
print('leftmost xMin per page (mode):', left.most_common(3))
lm = min(allw, key=lambda w: w[2])
print('smallest xMin: %.2f on p%d word %r' % (lm[2], lm[1], lm[4]))
print('page sizes:', set(re.findall(r'width="([\d.]+)" height="([\d.]+)"', s)))
print('FIN-OK')
