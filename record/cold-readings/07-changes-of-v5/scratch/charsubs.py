#!/usr/bin/env python3
"""charsubs.py — for every changed line block v4->v5, char-level diff; tally each (old -> new) substitution.
Prints the tally and, for each block, the substitutions that are NOT in the expected typographic set."""
import sys, difflib, collections
old=open(sys.argv[1],encoding='utf-8').read().split('\n'); new=open(sys.argv[2],encoding='utf-8').read().split('\n')
EXPECTED={('Z','ℤ'),('Q','ℚ'),('F','𝔽'),("'",'’'),('₂','_2')}
tally=collections.Counter(); 
sm=difflib.SequenceMatcher(None,old,new,autojunk=False); nb=0
for tag,i1,i2,j1,j2 in sm.get_opcodes():
    if tag=='equal': continue
    nb+=1
    a='\n'.join(old[i1:i2]); b='\n'.join(new[j1:j2])
    s=difflib.SequenceMatcher(None,a,b,autojunk=False)
    odd=[]
    for t,a1,a2,b1,b2 in s.get_opcodes():
        if t=='equal': continue
        pair=(a[a1:a2],b[b1:b2]); tally[pair]+=1
        if pair not in EXPECTED: odd.append((pair, a[max(0,a1-25):a2+25].replace('\n','⏎')))
    if len(sys.argv)>3:
        print(f'## block {nb} v4 {i1+1}-{i2} v5 {j1+1}-{j2}: {len(odd)} non-typographic char runs')
        for p,c in odd[:40]: print('   ',repr(p[0])[:80],'->',repr(p[1])[:80],' | ctx:',c[:90])
print('TALLY (top 40):')
for p,c in tally.most_common(40): print(f'  {c:4d}  {p[0][:40]!r} -> {p[1][:40]!r}')
