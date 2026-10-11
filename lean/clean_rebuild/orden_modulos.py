# orden_modulos.py — Grepy Mandalay, 3 Oct 2026; adapted for the cube by Grepy Escribano, 10 Oct 2026.
# Topological order of every module of the Lean project (from its import lines), for the clean rebuild.
# Prints one module name per line; modules listed in EXCLUDE (and every module importing one of them)
# are printed at the end with a leading '#', so that the rebuild script skips them and the
# certificate can declare them.
import os, re, sys

ROOT = os.path.expanduser('~/Desktop/ARBOLYAML/HYPERCUBE/lean/proyecto_cubo')
EXCLUDE = set(sys.argv[1:])
IMP = re.compile(r'^(?:public\s+)?import\s+(RequestProject[\w.]*)', re.M)

mods = {}
for d, _, fs in os.walk(os.path.join(ROOT, 'RequestProject')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(d, f)
            name = os.path.relpath(p, ROOT)[:-5].replace('/', '.')
            mods[name] = sorted(set(IMP.findall(open(p).read())))
main = os.path.join(ROOT, 'RequestProject.lean')
if os.path.exists(main):
    mods['RequestProject'] = sorted(set(IMP.findall(open(main).read())))

order, seen, temp = [], set(), set()
def visit(m):
    if m in seen: return
    if m in temp: raise SystemExit(f'cycle at {m}')
    temp.add(m)
    for d in mods.get(m, []):
        if d not in mods: raise SystemExit(f'missing import {d} in {m}')
        visit(d)
    temp.discard(m); seen.add(m); order.append(m)
for m in sorted(mods): visit(m)

bad = set(EXCLUDE)
changed = True
while changed:
    changed = False
    for m in order:
        if m not in bad and any(d in bad for d in mods[m]):
            bad.add(m); changed = True
for m in order:
    if m not in bad: print(m)
for m in order:
    if m in bad: print('#' + m)
