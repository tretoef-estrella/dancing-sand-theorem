# md-vs-pdf, numbers of 3 or more digits (with thin/normal space grouping) in §12 and in §1.0–§1.4, in order
import re,difflib
md=open('material/paper/THE_DANCING_SAND_THEOREM_v6.md').read()
pdf=open('scratch/v6_raw.txt').read().split('\f')
N=r'(?<![\d.])\d{1,3}(?:[    ]\d{3})+(?!\d)|(?<![\d.])\d{3,}(?!\d)'
def nums(s): return [re.sub(r'\s','',x) for x in re.findall(N,s)]
def section(s,a,b): return s[s.index(a):s.index(b)]
for name,(ma,mb),(pa,pb) in [('§12',('## 12. Computations','## 13. Exact status'),(44,47)),('§1.0-1.4',('### 1.0 Summary','### 1.5 The idea'),(2,6)),('§13+App A',('## 13. Exact status','## References'),(47,50))]:
    m=nums(section(md,ma,mb)); p=nums(' '.join(pdf[pa-1:pb]))
    if name=='§12': p=p[p.index('2')] if False else p
    sm=difflib.SequenceMatcher(None,m,p,autojunk=False)
    print('==',name,'md numbers',len(m),'pdf numbers',len(p))
    for t,a1,a2,b1,b2 in sm.get_opcodes():
        if t!='equal': print('  ',t,'md',m[a1:a2],'pdf',p[b1:b2],'| md before:',m[max(0,a1-3):a1])
