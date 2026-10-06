#!/usr/bin/env python3
"""xrefparts.py — every reference «Lemma/Proposition/Theorem/Corollary x.y(p)» to a PART p: does the statement have part (p)?
Also: code names in the pdf text are whole (every «gate…» token ends with .py or /)."""
import re
md=open('material/paper/THE_DANCING_SAND_THEOREM_v5.md',encoding='utf-8').read()
body=md.split('\n## References')[0]
L=body.split('\n')
# statement text per label (from the label line until *Proof or a blank line)
stm={}
for i,l in enumerate(L):
    m=re.match(r'^(?:> )?\*\*(Lemma|Theorem|Proposition|Corollary) ([0-9]+\.[0-9]+)',l)
    if m:
        j=i; block=[]
        while j<len(L) and not L[j].startswith('*Proof') and (j==i or not re.match(r'^(?:> )?\*\*(Lemma|Theorem|Proposition|Corollary)',L[j])):
            block.append(L[j]); j+=1
            if L[j-1].strip()=='' and j-i>1: break
        stm[(m.group(1),m.group(2))]=' '.join(block)
bad=0; n=0
for m in re.finditer(r'\b(Lemma|Theorem|Proposition|Corollary) ([0-9]+\.[0-9]+)\(([a-z])\)',body):
    k=(m.group(1),m.group(2)); p=m.group(3); n+=1
    s=stm.get(k)
    if s is None: print('NO STATEMENT', k, p); bad+=1; continue
    if f'({p})' not in s: print('PART MISSING', k, p, '…', body[max(0,m.start()-50):m.end()+10].replace('\n',' ')); bad+=1
print('part references checked:', n, 'problems:', bad)
raw=open('scratch/bbox/v5_raw.txt',encoding='utf-8').read()
toks=re.findall(r'gate[\w./]*',raw)
badc=[t for t in toks if not (t.endswith('.py') or t.endswith('/'))]
print('code tokens «gate…» in pdf text:', len(toks), ' not whole:', badc)
print('remark2 tokens:', re.findall(r'remark2\S*',raw))
