# M4: §4 axiom lines over the 68 final per-piece check logs; §3.3 cone counts and union; §1.4/§8 log identity.
import os, re, collections
M = 'material'; PP = f'{M}/logs/per_piece'
pieces = sorted({f.split('_')[0] for f in os.listdir(f'{M}/pieces') if f.endswith('.md')})
files = os.listdir(PP)
final = {}
for p in pieces:
    cands = [f for f in files if f.lower() == f'check{p.lower()}.log']
    if p == 'C31': cands = ['checkC31b.log']
    final[p] = cands
print('pieces', len(pieces), 'with exactly one final check log:', sum(1 for v in final.values() if len(v) == 1),
      [ (p, v) for p, v in final.items() if len(v) != 1])
kinds = collections.Counter(); lines_total = 0; per = {}; other = []
for p, v in final.items():
    t = open(os.path.join(PP, v[0]), encoding='utf-8').read()
    ax = re.findall(r"depends on axioms: \[([^\]]*)\]", t)
    no = re.findall(r"does not depend on any axioms", t)
    per[p] = len(ax) + len(no); lines_total += len(ax) + len(no)
    for a in ax: kinds[a] += 1
    kinds['(none)'] += len(no)
    last = t.rstrip().splitlines()[-1]
    if 'exit=0' not in last: other.append((p, last))
    if 'sorryAx' in t or 'error' in t.lower(): other.append((p, 'sorryAx/error present'))
print('axiom lines over the 68 final logs:', lines_total); print('  by content:', dict(kinds))
print('  final logs not ending with exit=0 or containing sorryAx/error:', other)
print('  pieces with 0 axiom lines:', [p for p, c in per.items() if c == 0])
# which theorems give fewer axioms
for p, v in final.items():
    t = open(os.path.join(PP, v[0]), encoding='utf-8').read()
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", t):
        if m.group(2) != 'propext, Classical.choice, Quot.sound': print('   ', p, m.group(1), '[' + m.group(2) + ']')
# per_piece copies of CheckCubo logs vs final_checks
for f in ('CheckCubo.log', 'CheckCubo_postclean.log', 'CheckCubo_run1.log'):
    print(f, 'per_piece copy identical to final_checks:', open(f'{PP}/{f}', 'rb').read() == open(f'{M}/logs/final_checks/{f}', 'rb').read())
# identity of the logs before/after the rebuild, except the watchdog's last line
for a, b in (('CheckCubo.log', 'CheckCubo_postclean.log'), ('DepsCubo.log', 'DepsCubo_postclean.log')):
    A = open(f'{M}/logs/final_checks/{a}').read().splitlines(); B = open(f'{M}/logs/final_checks/{b}').read().splitlines()
    print(a, 'vs', b, ': lines', len(A), len(B), '; identical except the last (watchdog) line:', A[:-1] == B[:-1], '; last lines:', A[-1], '|', B[-1])
# §3.3 cones
t = open(f'{M}/logs/final_checks/DepsCubo_postclean.log').read()
heads = re.findall(r'^(\S+): project decls in cone: (\d+); modules: (\d+)', t, re.M)
for h in heads: print('cone', h)
sec = t.split('UNION: ')[1]
union_mods = re.findall(r'^RequestProject\.(\S+) \d+$', sec, re.M)
print('union modules listed', len(union_mods))
RP = f'{M}/project/RequestProject'
mods = sorted(os.path.relpath(os.path.join(d, x), RP)[:-5].replace('/', '.') for d, _, xs in os.walk(RP) for x in xs if x.endswith('.lean'))
out = [m for m in mods if m not in set(union_mods)]
alls = [m for m in out if m.endswith('.All')]; rest = [m for m in out if not m.endswith('.All')]
print('modules outside the union:', len(out), '; .All:', len(alls), '; others:', rest)
print('number of .All modules in the project:', sum(1 for m in mods if m.endswith('.All')), '; folders without .All:', sorted({m.split(".")[0] for m in mods if m != "Main"} - {m.split(".")[0] for m in mods if m.endswith(".All")}))
# do the .All modules only import (and document)?
nonimport = []
for m in [m for m in mods if m.endswith('.All')]:
    src = open(f'{RP}/' + m.replace('.', '/') + '.lean').read()
    code = re.sub(r'/-.*?-/', '', src, flags=re.S); code = re.sub(r'--.*', '', code)
    rest_lines = [l for l in code.splitlines() if l.strip() and not re.match(r'\s*(public\s+)?import\s|\s*module\s*$', l)]
    if rest_lines: nonimport.append((m, rest_lines[:3]))
print('.All modules with something other than imports:', nonimport)
