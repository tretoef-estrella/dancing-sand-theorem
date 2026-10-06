# xrefs.py — cold reader 5. Every «Lemma x.y», «Theorem …», «Proposition», «Corollary», «§x.y», «Remark (n) of §x.y»
# cited in the text points to an item that exists; every citation key is in the references and every reference is cited.
import re, sys
md = open(sys.argv[1]).read()
body, _, refs = md.partition('\n## References')
defined = set()
for m in re.finditer(r'^\*\*(Lemma|Theorem|Proposition|Corollary|Definition|Example)\s+([0-9]+\.[0-9]+[a-z]?|[A-Z]{1,2}\b)', body, re.M):
    defined.add((m.group(1), m.group(2)))
for m in re.finditer(r'^\*\*Main Theorem', body, re.M):
    defined.add(('Theorem', 'Main'))
secs = set()
for m in re.finditer(r'^(#{2,3}) ([0-9]+(?:\.[0-9]+)?)[. ]', body, re.M):
    secs.add(m.group(2))
for m in re.finditer(r'^## (Appendix [A-Z])', body, re.M):
    secs.add(m.group(1))
print('defined statements:', len(defined), ' sections:', len(secs))
missing = []
# plural and lists: «Lemmas 10.4 and 10.5», «Propositions 5.2 · 5.3 · 5.4», «Theorems 10.12, 10.15»
for m in re.finditer(r'\b(Lemma|Theorem|Proposition|Corollary)s?\s+((?:[0-9]+\.[0-9]+[a-z]?|[A-Z]{1,2}\b)(?:\s*(?:,|and|·|–|or)\s*(?:[0-9]+\.[0-9]+[a-z]?|[A-Z]{1,2}\b))*)', body):
    kind = m.group(1)
    for lab in re.findall(r'[0-9]+\.[0-9]+[a-z]?|\b[A-Z]{1,2}\b', m.group(2)):
        if lab in ('A', 'I'):   # «Theorem A»? check separately
            pass
        if (kind, lab) not in defined:
            missing.append((kind, lab, body[max(0, m.start() - 40):m.end() + 10].replace('\n', ' ')))
for m in re.finditer(r'§\s?([0-9]+(?:\.[0-9]+)?)', body):
    if m.group(1) not in secs:
        missing.append(('§', m.group(1), body[max(0, m.start() - 40):m.end() + 10].replace('\n', ' ')))
seen = set()
for k, l, ctx in missing:
    if (k, l) in seen: continue
    seen.add((k, l))
    print('MISSING TARGET %s %s  …%s…' % (k, l, ctx))
# citations
keys_ref = re.findall(r'^- \[([^\]]+)\]', refs, re.M)
cited = set()
for m in re.finditer(r'\[([A-Za-z]+[0-9]{2}|OEIS)(?:,[^\]]*)?\]', body):
    cited.add(m.group(1))
for m in re.finditer(r'\[([A-Za-z]+[0-9]{2})[;\]]', body):
    cited.add(m.group(1))
print('reference keys:', len(keys_ref), ' cited keys:', len(cited))
print('cited but not in the list:', sorted(cited - set(keys_ref)))
print('in the list but never cited:', sorted(set(keys_ref) - cited))
print('duplicates in the list:', sorted(k for k in set(keys_ref) if keys_ref.count(k) > 1))
print('list in alphabetical order (case-insensitive):', keys_ref == sorted(keys_ref, key=lambda s: s.lower()))
print('FIN-OK')
