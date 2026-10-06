# formula_lines.py — cold reader 5. Lines of the pdf (bbox, grouped by line with sub/superscripts attached)
# that start with a binary operator or relation, that consist of a relation or «= 0» or the proof mark alone,
# or that end with a word that should not end a line (min, max, mod, Lemma, Theorem, step, §, Proposition ...).
import re, sys, html
s = open(sys.argv[1]).read()
pages = s.split('<page ')[1:]
OPS_START = ('+', '−', '-', '=', '≤', '≥', '<', '>', '≅', '⊆', '⊂', '·', '∘', '⊗', '⊕', '→', '↦', '≡', '∈', '×', ':=', '∣', '|')
BAD_END = {'min', 'max', 'mod', 'Lemma', 'Lemmas', 'Theorem', 'Theorems', 'step', '§', 'Proposition', 'Corollary',
           'Remark', 'Section', 'case', 'Case', 'Step', 'and', 'of', 'the', 'a', 'v', 'Syl', 'rank', 'dim', 'coker', 'ker', 'gcd', 'lcm', 'log', 'deg'}
out = []
for pi, p in enumerate(pages, 1):
    ws = [(float(a), float(b), float(c), float(d), html.unescape(w)) for a, b, c, d, w in
          re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', p)]
    ws = [w for w in ws if w[4].strip('⁠​') != '']
    tall = [w for w in ws if (w[3] - w[1]) >= 8.0]
    bands = []
    for w in sorted(tall, key=lambda w: (w[1] + w[3]) / 2):
        mid = (w[1] + w[3]) / 2
        if bands and abs(bands[-1][0] - mid) < 3.0:
            bands[-1][1].append(w)
        else:
            bands.append([mid, [w]])
    for mid, L in bands:
        L.sort()
        toks = [w[4] for w in L]
        text = ' '.join(toks)
        first, last = toks[0], toks[-1]
        if first in OPS_START or (first.startswith(('=', '≤', '≥', '≅', '⊆', '→', '+', '−')) and len(first) <= 3):
            out.append('p%d START-OP  [%s]' % (pi, text[:100]))
        core = text.strip()
        if core in ('∎', '■', '= 0.', '= 0', '=', '≤', '≅') or re.fullmatch(r'[=≤≥≅] ?[0-9A-Za-z()]{0,6}[.,]?', core):
            out.append('p%d ALONE     [%s]' % (pi, text[:100]))
        lastw = last.rstrip('.,;:')
        if last in BAD_END or lastw in {'min', 'max', 'mod', 'Lemma', 'Theorem', 'Proposition', 'Corollary', 'step', '§'}:
            # a sentence-final word with a period is fine
            if not last.endswith('.'):
                out.append('p%d END-BAD   [...%s]' % (pi, text[-80:]))
for o in out:
    print(o)
print('count', len(out))
print('FIN-OK')
