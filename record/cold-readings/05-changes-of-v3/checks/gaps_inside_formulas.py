# gaps_inside_formulas.py — cold reader 5. Does the stretch of a justified line go inside formulas?
# Reads the html of `pdftotext -bbox`. Groups words into lines by overlap of their vertical extent with the
# line's main band (so sub- and superscripts stay on their line, unlike a 2-pt bucket), and reports, for every
# full justified body line, the largest space between two consecutive glyph runs where at least one side is a
# mathematical token (digits, operators, Greek, brackets, sub/superscripts), next to the mean text-word gap.
import re, sys, html
s = open(sys.argv[1]).read()
TOP = int(sys.argv[2]) if len(sys.argv) > 2 else 25
pages = s.split('<page ')[1:]
W = re.compile(r"^[A-Za-z][A-Za-z'’\-]*[.,;:)]*$")
rows = []
for pi, p in enumerate(pages, 1):
    ws = [(float(a), float(b), float(c), float(d), html.unescape(w)) for a, b, c, d, w in
          re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p)]
    ws = [w for w in ws if w[4].strip('⁠​') != '']
    # main bands: words that look like text words of normal height
    tall = [w for w in ws if (w[3] - w[1]) >= 8.0]
    bands = []
    for w in sorted(tall, key=lambda w: (w[1] + w[3]) / 2):
        mid = (w[1] + w[3]) / 2
        if bands and abs(bands[-1][0] - mid) < 3.0:
            bands[-1][1].append(w)
        else:
            bands.append([mid, [w]])
    for mid, L in bands:
        # attach small words (sub/superscripts) whose vertical extent overlaps [mid-6, mid+6]
        ids = set(id(x) for x in L)
        full = L + [w for w in ws if id(w) not in ids and (w[3] - w[1]) < 8.0 and w[1] < mid + 6 and w[3] > mid - 6]
        full.sort()
        if len(full) < 6 or full[0][0] > 80 or max(w[2] for w in full) < 538:
            continue
        gaps = []
        for i in range(len(full) - 1):
            g = full[i + 1][0] - full[i][2]
            if g > 0.5:
                gaps.append((g, full[i][4], full[i + 1][4]))
        if not gaps or max(g for g, _, _ in gaps) > 45:
            continue  # table rows, displays
        tw = [g for g, a, b in gaps if W.match(a) and W.match(b)]
        if len(tw) < 2:
            continue
        mtw = sum(tw) / len(tw)
        mg = [(g, a, b) for g, a, b in gaps if not (W.match(a) and W.match(b))]
        if not mg:
            continue
        gmax = max(mg)
        rows.append((gmax[0], mtw, pi, gmax[1], gmax[2], ' '.join(w[4] for w in full)[:90]))
rows.sort(reverse=True)
for r in rows[:TOP]:
    print('math-gap %.1f  text-mean %.1f  p%d  [%s | %s]  %s' % r)
print('lines', len(rows), 'math-gap>8:', sum(r[0] > 8 for r in rows), '>10:', sum(r[0] > 10 for r in rows),
      '>12:', sum(r[0] > 12 for r in rows))
print('FIN-OK')
