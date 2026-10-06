#!/usr/bin/env python3
"""fill.py — Grepy cold reader 7. Fill of each page: (bottom of the last text word above the folio − top of the
text block) / (text block height). The folio is the lone number centred in the bottom margin (y > 780 pt).
The text block top and bottom are the medians of the first-word top and last-word bottom over all pages."""
import re, sys, html, statistics
s = open(sys.argv[1]).read()
pages = s.split('<page ')[1:]
tops, bots, data = [], [], []
for pi, p in enumerate(pages, 1):
    ws = [(float(a), float(b), float(c), float(d), html.unescape(w)) for a, b, c, d, w in
          re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p)]
    body = [w for w in ws if not (w[1] > 780 and re.fullmatch(r'\d+', w[4]))]
    folio = [w for w in ws if w[1] > 780 and re.fullmatch(r'\d+', w[4])]
    top = min(w[1] for w in body); bot = max(w[3] for w in body)
    tops.append(top); bots.append(bot); data.append((pi, top, bot, folio[0][4] if folio else '-'))
T = statistics.median(tops); B = max(bots)
print('text block: top %.1f pt (median), bottom %.1f pt (max over pages); height %.1f pt' % (T, B, B - T))
for pi, top, bot, f in data:
    fill = (bot - T) / (B - T)
    flag = '  <-- under 90 %' if fill < 0.90 else ''
    print('p%-2d folio %-3s last text bottom %.1f  fill %5.1f %%%s' % (pi, f, bot, 100 * fill, flag))
