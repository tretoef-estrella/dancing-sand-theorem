# md-vs-pdf, words: md words include ASCII words inside code spans; pdf hyphen breaks joined only when the joined word exists in the md
import re,difflib,collections
md=open('material/paper/THE_DANCING_SAND_THEOREM_v6.md').read()
pdf=open('scratch/v6_raw.txt').read()
W=r"[A-Za-z][A-Za-z'’]+"
def mdwords(s):
    s=s.replace('**',' ').replace('*',' ').replace('`',' ')
    s=re.sub(r'\s+',' ',s)
    return re.findall(W,s)
wm=[w.replace('’',"'") for w in mdwords(md)]
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
