# verify each remove-string occurs exactly once; apply all to copies in scratch and check the result
import re,shutil
R=open('REPORT_COLD_13.md',encoding='utf-8').read()
sec0=R.split('## 1. (a)')[0]
pairs=[]
for m in re.finditer(r'Remove: (``?)(.+?)\1(?: — |\n\s*)Print: (``?)(.+?)\3(?:\n|$)',sec0):
    pairs.append((m.group(2),m.group(4)))
print('pairs found',len(pairs))
P='material/paper/THE_DANCING_SAND_THEOREM_v10.md'; S='material/certificate/LEAN_CERTIFICATE_DANCING_SAND_v2.src.md'; M='material/certificate/LEAN_CERTIFICATE_DANCING_SAND_v2.md'
txt={f:open(f,encoding='utf-8').read() for f in (P,S,M)}
new={f:txt[f] for f in txt}
for a,b in pairs:
    c={f.split('/')[-1]:txt[f].count(a) for f in txt}
    print(c,'|',a[:70])
    for f in txt:
        if txt[f].count(a)==1: new[f]=new[f].replace(a,b)
for f in txt:
    out='scratch/applied_'+f.split('/')[-1]; open(out,'w',encoding='utf-8').write(new[f])
    print('wrote',out)
