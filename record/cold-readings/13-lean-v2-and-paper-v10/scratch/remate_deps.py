import re
L=open('material/final_checks/DepsCubo2.log',encoding='utf-8').read().split('\n')
O=open('material/final_checks/DepsCubo_postclean.log',encoding='utf-8').read().split('\n')
print('old log lines',len(O),'old last',O[-2][:60] if O[-1]=='' else O[-1][:60])
print('old[:-2] == new[:len(old)-2]:', O[:-2]==L[:len(O)-2], 'first differing old line idx', next((k for k,(a,b) in enumerate(zip(O,L)) if a!=b),None))
secs={}; cur=None
for l in L:
    m=re.match(r'^(\S+): project decls in cone: (\d+); modules: (\d+)',l)
    if m:
        cur=m.group(1)+('#2' if m.group(1) in secs else ''); secs[cur]=(int(m.group(2)),int(m.group(3)),[]); continue
    if cur and l.startswith('RequestProject.'): secs[cur][2].append(l.split()[0])
for k,(d,m,mods) in secs.items(): print(f'{k:24s} decls={d} modules={m} listed={len(mods)}')
u1=set(secs['UNION'][2]); u2=set(secs['UNION#2'][2])
print('old union subset of new:',u1<=u2,'new minus old:',sorted(u2-u1))
allm=set(l.split()[1].replace('RequestProject/','RequestProject.').replace('.lean','').replace('/','.') for l in open('material/final_checks/MANIFEST_md5_420.txt'))
print('modules in project:',len(allm),'outside new union:',len(allm-u2))
out=sorted(allm-u2); alls=[x for x in out if x.endswith('.All')]
print('outside .All:',len(alls),' non-All:',[x for x in out if not x.endswith('.All')])
print('SmallCases in union:',sorted(x for x in u2 if 'SmallCases' in x))
