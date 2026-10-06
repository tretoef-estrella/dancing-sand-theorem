# md-vs-pdf, words, third version: prose words outside code spans, plus code-span words that the pdf sets in ASCII (operator names)
import re,difflib
md=open('material/paper/THE_DANCING_SAND_THEOREM_v6.md').read()
pdf=open('scratch/v6_raw.txt').read()
W=r"[A-Za-z][A-Za-z’]+(?:'[a-z]+)?"
pdfvocab=set(re.findall(r"[A-Za-z]+",pdf))
toks=[]
for i,part in enumerate(re.split(r'(`[^`]*`)',md)):
    if part.startswith('`'):
        for w in re.findall(r"[A-Za-z]+'*",part):
            if "'" in w or len(w)<2: continue
            if w in pdfvocab and w not in ('FE','EF','gf','fg','Fp','Fn','pq','ab','Db','hJ','us','ss'): toks.append(w)
    else:
        part=part.replace('**',' ').replace('*',' ')
        toks+= [w for w in re.findall(W,part)]
wm=[w.replace('’',"'") for w in toks]
vocab=set(w.lower() for w in wm)
def join(m):
    a,b=m.group(1),m.group(2)
    return a+b if (a+b).lower() in vocab else a+'-'+b
p=re.sub(r"([A-Za-z]+)-\n([a-z]+)",join,pdf)
wp=[w.replace('’',"'") for w in re.findall(W,p)]
sm=difflib.SequenceMatcher(None,wm,wp,autojunk=False)
n=0
for t,a1,a2,b1,b2 in sm.get_opcodes():
    if t=='equal': continue
    n+=1
    print(f'W{n} {t}: md<{" ".join(wm[a1:a2])[:150]}> pdf<{" ".join(wp[b1:b2])[:150]}>  | ctx: {" ".join(wm[max(0,a1-7):a1])}')
print('word ops:',n,' md words',len(wm),' pdf words',len(wp))
