# word-level diff of v5 vs v6 md, per changed line block; output hunks with line numbers
import difflib,re,sys
a=open('material/paper/THE_DANCING_SAND_THEOREM_v5.md').read().split('\n')
b=open('material/paper/THE_DANCING_SAND_THEOREM_v6.md').read().split('\n')
sm=difflib.SequenceMatcher(None,a,b,autojunk=False)
h=0
for tag,i1,i2,j1,j2 in sm.get_opcodes():
    if tag=='equal': continue
    h+=1
    print(f'### HUNK {h}: {tag} v5 {i1+1}-{i2} v6 {j1+1}-{j2}')
    A=' \n '.join(a[i1:i2]); B=' \n '.join(b[j1:j2])
    ta=re.findall(r'\S+|\n',A); tb=re.findall(r'\S+|\n',B)
    s2=difflib.SequenceMatcher(None,ta,tb,autojunk=False)
    for t,x1,x2,y1,y2 in s2.get_opcodes():
        if t=='equal': continue
        ctx=' '.join(ta[max(0,x1-6):x1])
        print(f'  [{t}] ...{ctx}  -<{" ".join(ta[x1:x2])}>  +<{" ".join(tb[y1:y2])}>')
