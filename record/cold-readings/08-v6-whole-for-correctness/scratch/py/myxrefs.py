# my own cross-reference and citation check on the v6 md
import re,collections
md=open('material/paper/THE_DANCING_SAND_THEOREM_v6.md').read()
body,refs=md.split('\n## References\n')
keys=re.findall(r'^- \[([^\]]+)\]',refs,re.M)
cited=collections.Counter()
for grp in re.findall(r'\[([A-Za-z][A-Za-z0-9]*\d\d)(?:[,\]])',body): cited[grp]+=1
# multi-key brackets like [Jan03, Don93]
for b in re.findall(r'\[([^\]]+)\]',body):
    for part in b.split(','):
        p=part.strip().split(' ')[0]
        if re.fullmatch(r'[A-Za-z]+\d\d',p) or p=='OEIS': cited[p]+=1
print('reference keys:',len(keys)); print('not cited:',[k for k in keys if k not in cited]); print('cited, not in list:',sorted(k for k in cited if k not in keys))
# defined numbered items
defs=set()
for kind,num in re.findall(r'\*\*(Lemma|Theorem|Proposition|Corollary) (\d+\.\d+)',body): defs.add((kind,num))
for kind,num in re.findall(r'> \*\*(Corollary|Theorem) (\d+\.\d+)',body): defs.add((kind,num))
secs=set(re.findall(r'^#{2,3} (\d+(?:\.\d+)?)[ .]',body,re.M))
print('defined items:',len(defs),' sections:',len(secs))
# uses
bad=[]
for m in re.finditer(r'(Lemmas?|Theorems?|Propositions?|Corollar(?:y|ies)) ((?:\d+\.\d+(?:\([a-z]\))?(?:, | and | · |–|, and )?)+)',body):
    kind=m.group(1); k={'Lemma':'Lemma','Lemmas':'Lemma','Theorem':'Theorem','Theorems':'Theorem','Proposition':'Proposition','Propositions':'Proposition','Corollary':'Corollary','Corollaries':'Corollary'}[kind]
    ctx=body[max(0,m.start()-12):m.start()]
    if re.search(r'(GMMY24|Bai03|Bai|IKKY23|Gao et al\.\'s|their) ?,? ?$',ctx) or '[GMMY24, ' in body[max(0,m.start()-10):m.start()] or '[Bai03, ' in body[max(0,m.start()-9):m.start()] or 'their ' in ctx: continue
    nums=re.findall(r'\d+\.\d+',m.group(2))
    if '–' in m.group(2):
        a,b=nums[0],nums[-1]; x,y=a.split('.'),b.split('.')
        nums=[f'{x[0]}.{j}' for j in range(int(x[1]),int(y[1])+1)]
    for n in nums:
        if (k,n) not in defs: bad.append((k,n,body[max(0,m.start()-40):m.end()+10].replace('\n',' ')))
print('unresolved numbered refs:',len(bad))
for b in bad: print('  ',b)
badsec=[]
for s in re.findall(r'§(\d+(?:\.\d+)?)',body):
    if s not in secs: badsec.append(s)
print('unresolved §:',sorted(set(badsec)))
print('defined:',sorted(defs,key=lambda x:(int(x[1].split(".")[0]),int(x[1].split(".")[1]))))
