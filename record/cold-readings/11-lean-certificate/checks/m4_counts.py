# M4: recount §7 and Table 6b of the certificate from the files, and the clean rebuild of §8.
import os, re, datetime
M = 'material'; RP = f'{M}/project/RequestProject'
cert = open(f'{M}/certificate/LEAN_CERTIFICATE_DANCING_SAND_v1.md').read().replace('\u2009', ' ').replace('\u202f', ' ').replace('\u00a0', ' ')  # thin spaces in numbers
num = lambda s: int(s.replace(' ', '').replace(' ', ''))
# Table 6b
t6b = {}
sec = cert.split('**Table 6b.')[1].split('\n---\n')[0]
for line in sec.splitlines():
    m = re.match(r'\| (C\w+|—) \| `([^`]+)` \| (\d+) \| ([\d ]+) \| (\d+) \| (\d+) \| (\d+) \| (\d+) \| ([\d.]+) \|', line)
    if m: t6b[m.group(2)] = dict(piece=m.group(1), files=int(m.group(3)), lines=num(m.group(4)), thms=int(m.group(5)), defs=int(m.group(6)), mods=int(m.group(7)), secs=num(m.group(8)), peak=float(m.group(9)))
print('Table 6b rows parsed:', len(t6b))
# rebuild log
cr = {}
for line in open(f'{M}/logs/clean_rebuild/clean_rebuild_2026-10-10.log'):
    m = re.match(r'RequestProject\.(\S+) VIGIA-FIN-OK exit=(\d+) pico_kb=(\d+) t=(\d+)s wall=(\d+)s', line)
    if m: cr[m.group(1)] = dict(exit=int(m.group(2)), kb=int(m.group(3)), t=int(m.group(4)), wall=int(m.group(5)))
def counts(path, rule):
    src = open(path, encoding='utf-8').read(); L = src.split('\n')
    nl = src.count('\n')
    if rule == 'col0':
        th = sum(1 for l in L if l.startswith('theorem ') or l.startswith('lemma '))
        de = sum(1 for l in L if re.match(r'(noncomputable )?(def|abbrev)\b', l))
    else:  # any indentation, any modifiers/attributes before
        th = sum(1 for l in L if re.match(r'\s*(@\[[^\]]*\]\s*)?((private|protected|nonrec|noncomputable)\s+)*(theorem|lemma)\s', l))
        de = sum(1 for l in L if re.match(r'\s*(@\[[^\]]*\]\s*)?((private|protected|nonrec|noncomputable|partial|unsafe)\s+)*(def|abbrev)\s', l))
    return nl, th, de
folders = sorted(d for d in os.listdir(RP) if os.path.isdir(os.path.join(RP, d)))
print('folders on disk:', len(folders), 'in Table 6b:', len([f for f in t6b if f != 'Main.lean']), 'same set:', set(folders) == set(t6b) - {'Main.lean'})
tot = dict(files=0, lines=0, thms=0, defs=0, thms_any=0, defs_any=0, mods=0, secs=0)
mism = []
for f in folders:
    fl = sorted(x for x in os.listdir(os.path.join(RP, f)) if x.endswith('.lean'))
    lines = th = de = tha = dea = 0
    for x in fl:
        a, b, c = counts(os.path.join(RP, f, x), 'col0'); lines += a; th += b; de += c
        _, b2, c2 = counts(os.path.join(RP, f, x), 'any'); tha += b2; dea += c2
    mods = [k for k in cr if k.split('.')[0] == f]
    secs = sum(cr[k]['t'] for k in mods); peak = max(cr[k]['kb'] for k in mods) / 1048576
    row = dict(files=len(fl), lines=lines, thms=th, defs=de, mods=len(mods), secs=secs, peak=round(peak, 2))
    for k in ('files', 'lines', 'thms', 'defs', 'mods', 'secs', 'peak'):
        if row[k] != t6b[f][k]: mism.append((f, k, 'certificate', t6b[f][k], 'mine', row[k]))
    if (tha, dea) != (th, de): print(f'  {f}: counting with any indentation/modifiers gives thms {tha} defs {dea} (col0: {th}, {de})')
    for k in ('files', 'lines', 'thms', 'defs', 'mods', 'secs'): tot[k] += row[k]
    tot['thms_any'] += tha; tot['defs_any'] += dea
mainp = f'{RP}/Main.lean'; a, b, c = counts(mainp, 'col0')
print('Main.lean: lines', a, 'thms', b, 'defs', c, 'rebuild', cr.get('Main'))
print('68 folders totals (mine):', tot)
print('certificate §7: 415 files, 60 940 lines, 3 237 theorems, 876 definitions')
print('Table 6b mismatches:', mism if mism else 'none')
# rebuild
print('rebuild entries', len(cr), 'all exit 0:', all(v['exit'] == 0 for v in cr.values()))
print('sum t', sum(v['t'] for v in cr.values()), 'sum wall', sum(v['wall'] for v in cr.values()))
lng = max(cr, key=lambda k: cr[k]['t']); pk = max(cr, key=lambda k: cr[k]['kb'])
print('longest', lng, cr[lng]['t'], 's; peak', pk, cr[pk]['kb'], 'kB =', round(cr[pk]['kb'] / 1048576, 3), 'GiB')
log = open(f'{M}/logs/clean_rebuild/clean_rebuild_2026-10-10.log').read()
print('START/END lines:', [l for l in log.splitlines() if l.startswith(('START', 'END', 'RESUME', 'SKIPPED', 'STOP', 'FIN'))])
s = datetime.datetime(2026, 10, 10, 22, 16, 14); e = datetime.datetime(2026, 10, 11, 5, 20, 33); print('duration', e - s)
# every module of the project in the rebuild log, and cr_logs
mods_disk = sorted(os.path.relpath(os.path.join(d, x), RP)[:-5].replace('/', '.') for d, _, xs in os.walk(RP) for x in xs if x.endswith('.lean'))
print('modules on disk', len(mods_disk), 'all in rebuild log:', set(mods_disk) == set(cr))
crl = os.listdir(f'{M}/logs/clean_rebuild/cr_logs'); print('cr_logs files', len(crl))
bad = [x for x in crl if not open(f'{M}/logs/clean_rebuild/cr_logs/' + x).read().rstrip().splitlines()[-1].startswith('VIGIA-FIN-OK exit=0')]
print('cr_logs not ending in VIGIA-FIN-OK exit=0:', bad)
# cr_logs vs main log
dif = []
for x in crl:
    last = open(f'{M}/logs/clean_rebuild/cr_logs/' + x).read().rstrip().splitlines()[-1]
    m = re.match(r'VIGIA-FIN-OK exit=(\d+) pico_kb=(\d+) t=(\d+)s', last); k = x[:-4].replace('RequestProject.', '')
    if not m or k not in cr or (int(m.group(2)), int(m.group(3))) != (cr[k]['kb'], cr[k]['t']): dif.append(x)
print('cr_logs disagreeing with the main log:', dif)
# topological order
order = [l.strip() for l in open(f'{M}/logs/clean_rebuild/orden_modulos.txt') if l.strip()]
print('orden_modulos entries', len(order), 'commented', sum(1 for o in order if o.startswith('#')))
pos = {o: i for i, o in enumerate(order)}
viol = []
for mod in mods_disk:
    src = open(os.path.join(RP, mod.replace('.', '/') + '.lean'), encoding='utf-8').read()
    for imp in re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+RequestProject\.(\S+)', src, re.M):
        if pos.get('RequestProject.' + imp, 10**9) > pos.get('RequestProject.' + mod, -1): viol.append((mod, imp))
print('order is topological (every import earlier):', not viol, viol[:5])
print('order of the main log equals orden_modulos:', [l.split()[0] for l in log.splitlines() if l.startswith('RequestProject.')] == order)
# what does a module build log contain: does it build anything other than the module itself?
multi = []
for x in crl:
    t = open(f'{M}/logs/clean_rebuild/cr_logs/' + x).read()
    built = re.findall(r'Built (RequestProject\.\S+)', t)
    if len(set(built)) > 1 or (built and built[0] != x[:-4]): multi.append((x, built[:3]))
print('module logs that built more than their own module:', len(multi), multi[:3])
print('example cr_log:', open(f'{M}/logs/clean_rebuild/cr_logs/RequestProject.MainTheorem.Theorem.log').read()[-600:])
