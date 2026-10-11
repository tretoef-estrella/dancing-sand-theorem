# Grepy Cotejo: which v9 pages (40 dpi) are pixel-identical to some v8 page; word diff of pdftotext without page numbers
import os, hashlib, re, sys, difflib
def h(p): return hashlib.md5(open(p, 'rb').read()).hexdigest()
d8 = sorted(os.listdir('scratch/r40/v8')); d9 = sorted(os.listdir('scratch/r40/v9'))
H8 = {h('scratch/r40/v8/' + f): i + 1 for i, f in enumerate(d8)}
same = []; diff = []
for i, f in enumerate(d9):
    k = h('scratch/r40/v9/' + f)
    if k in H8: same.append((i + 1, H8[k]))
    else: diff.append(i + 1)
print('v9 pages identical to a v8 page:', len(same))
print('  pairs (v9->v8):', same)
print('v9 pages that differ:', diff)
# word comparison
def words(path):
    t = open(path, encoding='utf-8').read()
    pages = t.split('\f')
    out = []
    for pg in pages:
        lines = [l for l in pg.split('\n')]
        # drop a page-number line: a line that is only digits (the footer)
        lines = [l for l in lines if not re.fullmatch(r'\s*\d+\s*', l)]
        out += ' '.join(lines).split()
    return out
w8 = words('scratch/v8.txt'); w9 = words('scratch/v9.txt')
sm = difflib.SequenceMatcher(None, w8, w9, autojunk=False)
ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
print('word ops:', len(ops), 'words v8', len(w8), 'v9', len(w9))
for tag, a, b, c, d in ops:
    print(f'{tag}: -[{" ".join(w8[a:b])[:300]}] +[{" ".join(w9[c:d])[:300]}]')
