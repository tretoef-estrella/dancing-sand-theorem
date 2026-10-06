#!/usr/bin/env python3
"""stmt_cmp.py — Grepy el lector frío del cubo 6, 2026-10-05.
Does every numbered statement of the md print in the pdf with the same characters (boxed ones included)?
md block: from the label line («**Lemma 2.1.**», «> **Corollary 1.4 …**») to the line before «*Proof», a blank
line, or the next label; boxed blocks are the consecutive «>» lines.
Normalization (both sides): NFKC (math italic → ASCII, 𝒦 → K, 𝟙 → 1), drop md markup (` * > _ ^ { }),
drop all whitespace and every hyphen-like character (-, U+2010, U+2011, soft hyphen), map ′→', ″→'', ∑→Σ,
⨁→⊕, ∏ stays; then compare the MULTISETS of characters (pdftotext reads stacked scripts out of order).
pdf window: from the label to the first «Proof.» after it, or to the next label, whichever comes first.
Reports characters of the md missing from the pdf window (should be none) and, when the window ends at
«Proof.», characters of the pdf window absent from the md.
Control: a copy of the md with one «≤» changed into «<» inside Lemma 9.7 must be reported.
"""
import re, sys, unicodedata
from collections import Counter

def norm(t):
    t = unicodedata.normalize('NFKC', t)
    t = t.replace('′', "'").replace('″', "''").replace('∑', 'Σ').replace('⨁', '⊕')
    t = re.sub(r'[`*>_^{}\s\-‐‑­⁠​]', '', t)
    return t

md = open(sys.argv[1], encoding='utf-8').read()
if '--control' in sys.argv:
    i = md.find('**Lemma 9.7')
    j = md.find('≥ 4`', i)
    md = md[:j] + '> 4`' + md[j + 3:]
    print('CONTROL: changed «≥ 4» to «> 4» in Lemma 9.7')
pdf = open(sys.argv[2], encoding='utf-8').read()
lines = md.split('\n')
LAB = re.compile(r'^(> )?\*\*((Main Theorem|Theorem|Lemma|Proposition|Corollary)( [0-9.]+[0-9]|( [A-Z]{1,2}\b))?)')
stmts = []
for i, l in enumerate(lines):
    m = LAB.match(l)
    if not m:
        continue
    boxed = bool(m.group(1))
    block = [l]
    j = i + 1
    while j < len(lines):
        x = lines[j]
        if boxed:
            if not x.startswith('>'):
                break
        else:
            if x.strip() == '' or x.startswith('*Proof') or LAB.match(x) or x.startswith('#'):
                break
        block.append(x); j += 1
    label = m.group(2).strip()
    stmts.append((label, '\n'.join(block)))
print('statements found in the md:', len(stmts))
prev = 0
bad = 0
for k, (label, block) in enumerate(stmts):
    a = pdf.find(label + ' ') if label != 'Main Theorem' else pdf.find('Main Theorem (the Dancing Sand Theorem).')
    if label == 'Main Theorem' or a < 0:
        a = pdf.find(label + '.') if a < 0 else a
    if a < 0:
        a = pdf.find(label)
    # use the bold-label occurrence: the one followed within 3 chars by '.' or ' ('
    a = -1
    for mm in re.finditer(re.escape(label), pdf[prev:]):
        tail = pdf[prev + mm.end():prev + mm.end() + 3]
        if tail.startswith('.') or tail.startswith(' ('):
            a = prev + mm.start(); break
    if label == 'Main Theorem':
        a = pdf.find('Main Theorem (the Dancing Sand Theorem). For every')
    if a < 0:
        print('NOT FOUND', label); bad += 1; continue
    ends = []
    pr = pdf.find('Proof.', a + 5)
    if pr > 0: ends.append((pr, 'proof'))
    if k + 1 < len(stmts):
        nl = stmts[k + 1][0]
        for mm in re.finditer(re.escape(nl), pdf[a + 5:]):
            tail = pdf[a + 5 + mm.end():a + 5 + mm.end() + 3]
            if tail.startswith('.') or tail.startswith(' ('):
                ends.append((a + 5 + mm.start(), 'next')); break
    e, why = min(ends) if ends else (a + 3 * len(block), 'len')
    prev = a + 5
    win = pdf[a:e]
    cm, cp = Counter(norm(block)), Counter(norm(win))
    miss = cm - cp
    extra = cp - cm if why == 'proof' else Counter()
    if miss or extra:
        bad += 1
        print('%-28s missing in pdf: %s | extra in pdf: %s' % (label, dict(miss), dict(extra)))
print('statements with a difference:', bad, 'of', len(stmts))
print('FIN-OK')
