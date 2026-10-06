# structure.py — cold reader 5. (1) Headings near the foot of a page; (2) numbered statements (Lemma, Theorem,
# Proposition, Corollary) whose statement runs across a page break. Uses the md (statement boundaries) and the
# bbox html of the pdf (positions).
import re, sys, html, unicodedata
md = open(sys.argv[1]).read().split('\n')
s = open(sys.argv[2]).read()
pages = s.split('<page ')[1:]
def norm(t):
    t = unicodedata.normalize('NFKC', t)
    return re.sub(r'[^A-Za-z]', '', t).lower()
pw = []  # per page: list of (y, normalized word)
for p in pages:
    ws = [(float(b), html.unescape(w)) for a, b, c, d, w in
          re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p)]
    pw.append(ws)
pagetext = [norm(' '.join(w for _, w in ws)) for ws in pw]
# (1) headings
print('== headings in the lowest 12% of the page (y > 740 pt) ==')
for i, line in enumerate(md):
    m = re.match(r'^(#{2,3}) (.*)$', line)
    if not m: continue
    key = norm(m.group(2))[:25]
    if len(key) < 6: continue
    for pi, t in enumerate(pagetext, 1):
        if key in t:
            # find y of the first word of the heading on that page
            words = [w for _, w in pw[pi - 1]]
            first = norm(m.group(2).split()[0] if m.group(2).split() else '')
            ys = [y for y, w in pw[pi - 1] if norm(w) and norm(w) == first]
            y = max(ys) if ys else None
            below = [yy for yy, w in pw[pi - 1] if y is not None and yy > y + 5]
            if y is not None and y > 740:
                print('p%d y=%.0f  %s  (text lines below on the page: %d words)' % (pi, y, m.group(2)[:60], len(below)))
            break
# (2) statements
print('== numbered statements running across a page break ==')
i = 0
cnt = 0
while i < len(md):
    m = re.match(r'^\*\*(Lemma|Theorem|Proposition|Corollary) ([0-9.]+[a-z]?)', md[i])
    if not m:
        i += 1; continue
    label = m.group(1) + ' ' + m.group(2)
    # statement = from this line until the line starting with *Proof or a blank line followed by a non-indented para that starts a new block
    j = i
    block = []
    while j < len(md) and not md[j].startswith('*Proof') and not (j > i and re.match(r'^\*\*(Lemma|Theorem|Proposition|Corollary|Remark|Example|Definition)', md[j])) and not md[j].startswith('#'):
        block.append(md[j]); j += 1
    text = ' '.join(block)
    head = norm(text)[:40]
    tail = norm(text)[-40:]
    p_head = next((pi for pi, t in enumerate(pagetext, 1) if head[:30] in t), None)
    p_tail = None
    if p_head:
        for pi in range(p_head, min(p_head + 3, len(pagetext) + 1)):
            if tail[-25:] in pagetext[pi - 1]:
                p_tail = pi; break
    cnt += 1
    if p_head is None or p_tail is None:
        print('  ?? %s: head page %s, tail page %s (not located)' % (label, p_head, p_tail))
    elif p_tail != p_head:
        print('  SPLIT %s: starts p%d, ends p%d' % (label, p_head, p_tail))
    i = j if j > i else i + 1
print('statements examined:', cnt)
print('FIN-OK')
