# md_vs_pdf.py — cold reader 5. Does the pdf say what the md says?
# (a) every number in the tables of §1 and §12 of the md appears in the pdf, in the same order (as a subsequence
#     of the numbers of the pdf text of the same section);
# (b) for every numbered statement (bold label), the prose words outside formulas appear in the pdf in order.
import re, sys, unicodedata
md = open(sys.argv[1]).read()
pdf = open(sys.argv[2]).read()
def nums(t):
    t = t.replace(' ', ' ').replace(' ', ' ')
    t = re.sub(r'(?<=\d) (?=\d{3}\b)', '', t)   # 109 200 -> 109200
    return re.findall(r'[0-9]+', t)
def subseq(a, b):
    it = iter(b)
    return all(x in it for x in a)
def section(t, start, end):
    i = t.find(start); j = t.find(end, i + 1)
    return t[i:j] if i >= 0 else ''
# (a) tables
ok = True
for name, (s1, s2), (p1, p2) in [
        ('§1.0 summary table', ('### 1.0', '### 1.1'), ('1.0', '1.1 The problem')),
        ('§1.6 notation table', ('### 1.6', '### 1.7'), ('1.6 Notation', '1.7 Vocabulary')),
        ('§1.7 vocabulary table', ('### 1.7', '### 1.8'), ('1.7 Vocabulary', '1.8')),
        ('§12.1 table', ('### 12.1', '### 12.2'), ('12.1 The checks', '12.2 Independent')),
        ('§12.2 table', ('### 12.2', '## 13'), ('12.2 Independent', '13. Exact status'))]:
    mds = section(md, s1, s2)
    rows = [l for l in mds.split('\n') if l.startswith('|') and not set(l) <= set('|-: ')]
    mn = [n for r in rows for n in nums(r)]
    pds = section(pdf, p1, p2)
    pn = nums(pds)
    from collections import Counter
    cm, cp = Counter(mn), Counter(pn)
    short = {x: cm[x] - cp[x] for x in cm if cm[x] > cp[x]}
    res = subseq(mn, pn)
    print('   multiset check %-24s: %s' % (name, 'OK' if not short else 'numbers missing in pdf: %s' % short))
    if not res:
        # find first failure
        it = 0; bad = None
        for k, x in enumerate(mn):
            try:
                it = pn.index(x, it) + 1
            except ValueError:
                bad = (k, x, mn[max(0, k - 5):k + 5]); break
        print('TABLE %-24s md numbers %4d, pdf numbers %4d: NOT a subsequence; first miss %s' % (name, len(mn), len(pn), bad))
        ok = False
    else:
        print('TABLE %-24s md numbers %4d, pdf numbers %4d: subsequence OK' % (name, len(mn), len(pn)))
# (b) statements
def prose_words(t):
    t = re.sub(r'`[^`]*`', ' ', t)
    t = re.sub(r'[*_#>|]', ' ', t)
    t = unicodedata.normalize('NFKC', t)
    return [w.lower() for w in re.findall(r"[A-Za-z]{3,}", t)]
pdfw = [w.lower() for w in re.findall(r"[A-Za-z]{3,}", unicodedata.normalize('NFKC', pdf.replace('-\n', '').replace('‐\n', '')))]
lines = md.split('\n')
bad = 0; n = 0
for i, l in enumerate(lines):
    m = re.match(r'^\*\*(Lemma|Theorem|Proposition|Corollary|Main Theorem)( [0-9.]+)?', l)
    if not m: continue
    block = []
    j = i
    while j < len(lines) and lines[j].strip() != '' and not lines[j].startswith('*Proof'):
        block.append(lines[j]); j += 1
    w = prose_words(' '.join(block))
    if len(w) < 3: continue
    n += 1
    # locate the first 3 words, then check subsequence in a window
    found = False
    for k in range(len(pdfw) - 2):
        if pdfw[k:k + 3] == w[:3]:
            if subseq(w, pdfw[k:k + 6 * len(w) + 40]):
                found = True; break
    if not found:
        bad += 1
        print('STATEMENT not matched in order:', l[:70])
print('statements checked:', n, 'not matched:', bad)
print('FIN-OK')
