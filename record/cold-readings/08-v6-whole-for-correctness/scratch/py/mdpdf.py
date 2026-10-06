# my own md-vs-pdf comparison: (1) sequence of prose words; (2) sequence of numbers in §12 and §1.0/§1.2 tables and statements
import re,difflib,unicodedata
md=open('material/paper/THE_DANCING_SAND_THEOREM_v6.md').read()
pdf=open('scratch/v6_raw.txt').read()
def words_md(s):
    s=re.sub(r'`[^`]*`',' ',s)            # drop code spans (formulas)
    s=s.replace('**',' ').replace('*',' ')
    return re.findall(r"[A-Za-z][A-Za-z'’]+",s)
def words_pdf(s):
    s=re.sub(r'-\n(?=[a-z])','',s)        # join hyphenated breaks
    toks=re.findall(r"[A-Za-z][A-Za-z'’]+",s)
    return toks
wm=[w.replace('’',"'") for w in words_md(md)]
wp=[w.replace('’',"'") for w in words_pdf(pdf)]
sm=difflib.SequenceMatcher(None,wm,wp,autojunk=False)
n=0
for t,a1,a2,b1,b2 in sm.get_opcodes():
    if t=='equal': continue
    n+=1
    print(f'W{n} {t}: md<{" ".join(wm[a1:a2])[:120]}> pdf<{" ".join(wp[b1:b2])[:120]}>  | md ctx: {" ".join(wm[max(0,a1-6):a1])}')
print('word ops:',n,' md words',len(wm),' pdf words',len(wp))
