# md_vs_pdf9.py — cold reader 9. For every line added in v6->v7 (the '+' lines of the diff), check that its words
# appear, in order and contiguously, in the text of a pdf; for table rows, cell by cell. Words: alphabetic runs of
# length >= 3 after NFKC, lower case. Numbers: every digit run of the line must occur in the pdf text.
# Usage: python3 md_vs_pdf9.py DIFF PDFTEXT [mutate]
import sys, re, unicodedata
diff, pdft = sys.argv[1], sys.argv[2]; mutate = len(sys.argv) > 3
def norm(s):
    s = unicodedata.normalize('NFKC', s)
    return s
def words(s): return [w.lower() for w in re.findall(r'[^\W\d_]{3,}', norm(s))]
def nums(s): return re.findall(r'\d+', norm(s))
pt = open(pdft, encoding='utf-8').read()
pt = re.sub(r'-\n(?=[a-z])', '', pt)          # end-of-line hyphenation
PW = words(pt); PWs = ' ' + ' '.join(PW) + ' '
PN = set(nums(pt))
added = [l[1:] for l in open(diff, encoding='utf-8') if l.startswith('+') and not l.startswith('+++')]
added = [l for l in added if l.strip()]
bad = 0; checks = 0
for n, line in enumerate(added):
    if mutate:   # damage: replace the longest word of the line by a word that is not in the paper
        ws = re.findall(r'[A-Za-z]{5,}', line)
        if ws: line = line.replace(max(ws, key=len), 'Zzyqxw', 1)
    parts = [c for c in line.split('|') if c.strip()] if line.lstrip().startswith('|') else [line]
    for c in parts:
        w = words(c.replace('`', ' ').replace('*', ' '))
        if len(w) < 1: continue
        checks += 1
        seq = ' ' + ' '.join(w) + ' '
        if seq not in PWs:
            # locate the longest prefix found, to show where it breaks
            k = 0
            while k < len(w) and (' ' + ' '.join(w[:k+1]) + ' ') in PWs: k += 1
            bad += 1; print(f'MISS line{n} words {k}/{len(w)} breaks at: {w[k:k+6]}')
    missing = [x for x in nums(line.replace('`', ' ')) if x not in PN]
    checks += 1
    if missing: bad += 1; print(f'MISS line{n} numbers not in pdf: {missing}')
print(f'RESULT added_lines={len(added)} checks={checks} misses={bad}')
