# M3: verify the source manifests of logs/clean_rebuild against the files in material/project,
# recompute the md5 of MANIFEST_md5_416.txt, and compare .olean timestamps with the sources.
import hashlib, os, sys
R = 'material/project'
CR = 'material/logs/clean_rebuild'
def md5(p):
    return hashlib.md5(open(p,'rb').read()).hexdigest()
for man in ['MANIFEST_md5_416.txt', 'MANIFEST_sources_md5.txt']:
    ok = bad = 0; paths = []
    for line in open(os.path.join(CR, man)):
        h, f = line.split(None, 1); f = f.strip(); paths.append(f)
        p = os.path.join(R, f)
        if not os.path.exists(p): print('MISSING', man, f); bad += 1; continue
        if md5(p) == h: ok += 1
        else: print('DIFF', man, f); bad += 1
    print(man, 'lines', len(paths), 'ok', ok, 'bad', bad, 'sorted bytewise', paths == sorted(paths, key=lambda s: s.encode()))
print('md5 of MANIFEST_md5_416.txt =', md5(os.path.join(CR, 'MANIFEST_md5_416.txt')))
# every .lean in RequestProject in the 416 manifest?
srcs = sorted(os.path.relpath(os.path.join(d, f), R) for d, _, fs in os.walk(os.path.join(R, 'RequestProject')) for f in fs if f.endswith('.lean'))
man416 = [l.split(None,1)[1].strip() for l in open(os.path.join(CR, 'MANIFEST_md5_416.txt'))]
print('lean sources on disk', len(srcs), 'same set as manifest', set(srcs) == set(man416))
# what is in MANIFEST_sources_md5 beyond the 416
extra = [l.split(None,1)[1].strip() for l in open(os.path.join(CR, 'MANIFEST_sources_md5.txt'))]
extra = [e for e in extra if e not in set(man416)]
print('extra entries in sources manifest:', len(extra)); print('  ', extra[:5], '...', extra[-5:])
# check files present in project/checks but not in manifest
chk = sorted('checks/' + f for f in os.listdir(os.path.join(R, 'checks')))
print('project/checks files', len(chk), 'not in sources manifest:', [c for c in chk if c not in extra])
# olean timestamps
B = os.path.join(R, '.lake', 'build', 'lib', 'lean')
missing = []; older = []; tmin = None; tmax = None
for s in srcs:
    o = os.path.join(B, s[:-5] + '.olean')
    if not os.path.exists(o): missing.append(s); continue
    to = os.path.getmtime(o); ts = os.path.getmtime(os.path.join(R, s))
    tmin = to if tmin is None else min(tmin, to); tmax = to if tmax is None else max(tmax, to)
    if to < ts: older.append(s)
import datetime
print('oleans missing', len(missing), missing[:5], 'olean older than source', len(older), older[:5])
print('olean mtimes from', datetime.datetime.fromtimestamp(tmin), 'to', datetime.datetime.fromtimestamp(tmax))
print('other dirs in .lake:', os.listdir(os.path.join(R, '.lake')))
