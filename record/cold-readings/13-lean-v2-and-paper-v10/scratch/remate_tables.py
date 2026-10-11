import os,re
D='material/certificate/data_v2/'
fc=[l.split() for l in open(D+'folders_counts.txt')]
cb={l.split()[0]:l.split()[1:] for l in open(D+'clean_build_by_folder.txt')}
print('folders',len(fc),'files',sum(int(x[2]) for x in fc),'lines',sum(int(x[3]) for x in fc),'thm-lines',sum(int(x[4]) for x in fc),'defs',sum(int(x[5]) for x in fc))
print('build modules',sum(int(v[0]) for v in cb.values()),'seconds',sum(int(v[1]) for v in cb.values()),'peak',max(float(v[2]) for v in cb.values()), 'Main' in cb, cb.get('Main'))
# own recount per folder of the two columns, straight from the sources
root='material/project/RequestProject'; T=re.compile(r'^(theorem|lemma)\b'); Df=re.compile(r'^(def|abbrev|noncomputable def|noncomputable abbrev)\b')
mine={}
for d in sorted(os.listdir(root)):
    p=os.path.join(root,d)
    if not os.path.isdir(p): continue
    nf=nl=nt=nd=0
    for dd,_,fs in os.walk(p):
        for f in fs:
            if f.endswith('.lean'):
                L=open(os.path.join(dd,f),encoding='utf-8').read().split('\n')
                t=open(os.path.join(dd,f),encoding='utf-8').read()
                nf+=1; nl+=t.count('\n'); nt+=sum(1 for l in L if T.match(l)); nd+=sum(1 for l in L if Df.match(l))
    mine[d]=(nf,nl,nt,nd)
bad=[(x[1],x[2:],mine[x[1]]) for x in fc if tuple(map(int,x[2:]))!=mine[x[1]]]
print('folders where data_v2 differs from my recount:',bad)
print('my totals', [sum(v[i] for v in mine.values()) for i in range(4)])
# compare tables.md with certificate v2 md
t=open(D+'tables.md',encoding='utf-8').read(); md=open('material/certificate/LEAN_CERTIFICATE_DANCING_SAND_v2.md',encoding='utf-8').read()
for blk in t.split('\n\n'):
    if blk.strip(): print('tables.md block in v2.md:', blk.strip() in md, blk.strip()[:40].replace('\n',' '))
