#!/usr/bin/env python3
"""xref2.py — Grepy el lector frío del cubo 6, 2026-10-05. Own cross-reference check of the md.
Defined: every bold label (boxed «> **…» included), their names (Theorem D/O/F/U/DW, Lemma W/K, Main Theorem),
their parts (a), (b), … found in the statement block, sections and subsections, Appendix A, the numbered
Remarks (n) of each section. Referenced: every «Lemma/Theorem/Proposition/Corollary x.y[(p)]» (lists with
«and», «,», «·», «–» included), «§x[.y]», «Remark (n)». References inside a citation bracket «[Key, …]» or
preceded by «their»/«Gao et al.'s» are external and skipped. Every unresolved reference is printed with
context; ranges «x.y–x.z» are expanded. Control: «Lemma 7.11» and «§10.9» appended to the body must be reported.
"""
import re, sys
md = open(sys.argv[1], encoding='utf-8').read()
body, _, refs = md.partition('\n## References')
if '--control' in sys.argv:
    body += '\nControl: by Lemma 7.11 and §10.9.\n'
lines = body.split('\n')
defined = {}           # (kind, label) -> set of parts
LAB = re.compile(r'^(?:> )?\*\*(Main Theorem|Theorem|Lemma|Proposition|Corollary) ?([0-9]+\.[0-9]+|[A-Z]{1,2}\b)?([^*]*)\*\*')
for i, l in enumerate(lines):
    m = LAB.match(l)
    if not m:
        continue
    kind, lab, rest = m.group(1), m.group(2) or '', m.group(3)
    if kind == 'Main Theorem':
        kind, lab = 'Theorem', 'Main'
    # block to collect parts
    blk = [l]
    for x in lines[i + 1:i + 12]:
        if x.startswith('*Proof') or LAB.match(x) or x.startswith('#'):
            break
        blk.append(x)
    parts = set(re.findall(r'(?:^|\s|>\s?)\(([a-d])\)', '\n'.join(blk)))
    defined[(kind, lab)] = parts
    nm = re.search(r'\((Theorem|Lemma) ([A-Z]{1,2})\b', rest)
    if nm:
        defined[(nm.group(1), nm.group(2))] = parts
for nmk in ['D', 'DW']:
    pass
secs = set(re.findall(r'^#{2,3} ([0-9]+(?:\.[0-9]+)?)[. ]', body, re.M))
remarks = {}
cur = None
for l in lines:
    h = re.match(r'^#{2,3} ([0-9]+(?:\.[0-9]+)?)', l)
    if h:
        cur = h.group(1)
    if l.startswith('**Remarks.**') or l.startswith('**Remark'):
        for n in re.findall(r'\((\d)\)', l):
            remarks.setdefault(cur, set()).add(n)
print('statements defined:', len(defined), ' sections:', len(secs), ' remarks:', remarks)
# strip citations and external
def strip_ext(t):
    t = re.sub(r'\[[A-Za-z]+[0-9]{2}[^\]]*\]', ' ', t)
    t = re.sub(r"(their|Gao et al\.'s|Bai's|in \[?[A-Z][A-Za-z]+[0-9]{2})\s+((?:Theorem|Proposition|Conjecture|Remark|Table|Corollary|Lemma)s?\s+[0-9.]+(?:\s*(?:and|,)\s*[0-9.]+)*)", ' ', t)
    return t
B = strip_ext(body)
bad = []
REF = re.compile(r'\b(Lemma|Theorem|Proposition|Corollary)s?\s+((?:[0-9]+\.[0-9]+[a-z]?(?:\([a-d]\))?|[A-Z]{1,2}\b)(?:\s*(?:,|and|·|–|or)\s*(?:[0-9]+\.[0-9]+(?:\([a-d]\))?|[A-Z]{1,2}\b))*)')
n = 0
for m in REF.finditer(B):
    kind = m.group(1)
    labs = re.findall(r'([0-9]+)\.([0-9]+)(?:\(([a-d])\))?|\b([A-Z]{1,2})\b', m.group(2))
    rng = '–' in m.group(2)
    nums = []
    for a, b, p, nm in labs:
        if nm:
            if nm in ('A', 'I', 'U', 'O', 'F', 'D', 'DW', 'W', 'K'):
                nums.append((nm, ''))
            continue
        nums.append(('%s.%s' % (a, b), p))
    if rng and len(nums) == 2 and '.' in nums[0][0]:
        a0, b0 = map(int, nums[0][0].split('.')); a1, b1 = map(int, nums[1][0].split('.'))
        if a0 == a1:
            nums = [('%d.%d' % (a0, x), '') for x in range(b0, b1 + 1)]
    for lab, p in nums:
        n += 1
        if lab in ('A', 'I'):
            continue
        key = (kind, lab)
        if key not in defined:
            bad.append('MISSING %s %s  …%s…' % (kind, lab, B[max(0, m.start() - 50):m.end() + 10].replace('\n', ' ')))
        elif p and p not in defined[key]:
            bad.append('NO PART %s %s(%s) (parts: %s)  …%s…' % (kind, lab, p, sorted(defined[key]), B[max(0, m.start() - 40):m.end() + 5].replace('\n', ' ')))
for m in re.finditer(r'§\s?([0-9]+(?:\.[0-9]+)?)', B):
    n += 1
    if m.group(1) not in secs:
        bad.append('MISSING § %s  …%s…' % (m.group(1), B[max(0, m.start() - 50):m.end() + 10].replace('\n', ' ')))
for m in re.finditer(r'Remarks? \((\d)\)(?: (?:of|after) (§[0-9.]+|Theorem [0-9.]+))?', B):
    n += 1
    where = m.group(2) or ''
    ok = any(m.group(1) in v for v in remarks.values())
    if not ok:
        bad.append('MISSING Remark (%s) %s' % (m.group(1), where))
print('references checked:', n, ' unresolved:', len(bad))
for b in bad:
    print('  ' + b)
print('FIN-OK')
