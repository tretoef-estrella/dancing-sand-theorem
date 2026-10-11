# fill_v2.py (version 2: CertCubo2.log, data_v2) — Grepy Escribano, 11 Oct 2026.
# Fills LEAN_CERTIFICATE_DANCING_SAND_v2.src.md -> LEAN_CERTIFICATE_DANCING_SAND_v2.md:
#   a line «<<<Name1 Name2 …>>>» becomes a fenced block with Lean's own output for those declarations,
#   taken verbatim from logs/CertCubo2.log (#check / #print); «<<<TABLES>>>» becomes data_v2/tables.md.
# Nothing is typed by hand: every quoted statement and definition is cut out of the log.
import os, re, sys
H = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(H, '..', '..', 'logs', 'CertCubo2.log')
lines = open(LOG).read().splitlines()
assert lines[-1].startswith('VIGIA-FIN-OK exit=0'), lines[-1]
lines = lines[:-1]
start = re.compile(r"^(@\[[a-z]+\] )?(def|theorem|abbrev|class|structure) |^[A-Za-z][A-Za-z0-9_.']* : |^'[^']*' depends on axioms")
blocks, cur = [], []
for l in lines:
    if start.match(l) and cur:
        blocks.append(cur); cur = []
    cur.append(l)
blocks.append(cur)
byname = {}
for b in blocks:
    m = re.match(r"^(?:@\[[a-z]+\] )?(?:def|theorem|abbrev) ([^ ]+?)(?:\.\{[^}]*\})? :|^([A-Za-z][A-Za-z0-9_.']*) :", b[0])
    if m:
        name = m.group(1) or m.group(2)
        assert name not in byname, name
        byname[name] = '\n'.join(b)
src = open(os.path.join(H, 'LEAN_CERTIFICATE_DANCING_SAND_v2.src.md')).read()
used = set()
def sub(m):
    names = m.group(1).split()
    if names == ['TABLES']:
        return open(os.path.join(H, 'data_v2', 'tables.md')).read().rstrip('\n')
    out = []
    for n in names:
        if n not in byname:
            sys.exit('MISSING in log: ' + n)
        out.append(byname[n]); used.add(n)
    return '```\n' + '\n'.join(out) + '\n```'
res = re.sub(r'^<<<([^>]+)>>>$', sub, src, flags=re.M)
assert '<<<' not in res
open(os.path.join(H, 'LEAN_CERTIFICATE_DANCING_SAND_v2.md'), 'w').write(res)
print('blocks in log', len(byname), 'quoted', len(used), 'not quoted', sorted(set(byname) - used))
