#!/usr/bin/env python3
"""hunkmap.py — map every changed line block (v4->v5) to its hunk of DIFF_v4_to_v5.txt, its section,
and whether it lies inside a numbered statement or a proof (v5 side).
Statement: a paragraph starting with **Theorem/Lemma/Proposition/Corollary/Definition x** or '> **'.
Proof: from a line containing '*Proof' up to the line containing '∎' (inclusive)."""
import re, difflib
old=open('material/paper/THE_DANCING_SAND_THEOREM_v4.md',encoding='utf-8').read().split('\n')
new=open('material/paper/THE_DANCING_SAND_THEOREM_v5.md',encoding='utf-8').read().split('\n')
# hunks of the given diff (new-side ranges)
H=[]
for l in open('material/paper/DIFF_v4_to_v5.txt',encoding='utf-8'):
    m=re.match(r'@@ -(\d+),(\d+) \+(\d+),(\d+) @@',l)
    if m: a,b,c,d=map(int,m.groups()); H.append((c,c+d-1))
def hunk_of(j):
    for k,(c,e) in enumerate(H,1):
        if c<=j<=e: return k
    return None
# section and kind for each v5 line
sec=['']*len(new); kind=['text']*len(new)
cur=''; inproof=False; instmt=False
for n,l in enumerate(new):
    if l.startswith('#'): cur=l.strip('# ').strip()[:40]; instmt=False
    sec[n]=cur
    if re.match(r'^(> )?\*\*(Theorem|Lemma|Proposition|Corollary|Definition|Main Theorem)',l): instmt=True
    if l.strip()=='' : instmt=False if not l.startswith('>') else instmt
    if '*Proof' in l: inproof=True
    if inproof: kind[n]='PROOF'
    elif instmt or l.startswith('>'): kind[n]='STATEMENT'
    if inproof and '∎' in l: inproof=False
sm=difflib.SequenceMatcher(None,old,new,autojunk=False); nb=0
for tag,i1,i2,j1,j2 in sm.get_opcodes():
    if tag=='equal': continue
    nb+=1
    js=range(j1,j2) if j2>j1 else [j1]
    kinds=sorted(set(kind[j] for j in js if j<len(new)))
    print(f'block {nb:3d} hunk {hunk_of(j1+1)} v5 {j1+1}-{j2} [{sec[j1]}] {",".join(kinds)} :: {new[j1][:70]!r}')
