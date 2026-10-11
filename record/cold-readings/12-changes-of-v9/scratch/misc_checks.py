# Grepy Cotejo: small checks redone under vigia (numbered statements of §2–§10, missing final logs, instances)
import re, os
v9 = open('material/paper/THE_DANCING_SAND_THEOREM_v9.md', encoding='utf-8').read()
a = v9.index('\n## 2. '); b = v9.index('\n## 11. ')
sec = v9[a:b]
names = re.findall(r'^(?:> )?\*\*((?:Lemma|Theorem|Proposition|Corollary) \d+\.\d+)', sec, re.M)
uniq = []
[uniq.append(x) for x in names if x not in uniq]
print('numbered statements in §2–§10 (distinct, in order):', len(uniq), 'first', uniq[0], 'last', uniq[-1])
cert = open('material/evidence/certificate/LEAN_CERTIFICATE_DANCING_SAND_v1.src.md', encoding='utf-8').read()
pieces = re.findall(r'^\| (C\d+[a-h]?) \|', cert, re.M)
fs = set(os.listdir('material/evidence/final_checks'))
print('pieces', len(pieces), 'final check logs missing from material:',
      [p for p in pieces if f'check{p}.log' not in fs and not (p == 'C31' and 'checkC31b.log' in fs)])
def strip(s):
    out=[];i=0;n=len(s);d=0
    while i<n:
        if d==0 and s.startswith('--',i):
            j=s.find('\n',i); i=n if j<0 else j; continue
        if s.startswith('/-',i): d+=1;i+=2;continue
        if d>0 and s.startswith('-/',i): d-=1;i+=2;continue
        if d>0:
            if s[i]=='\n': out.append('\n')
            i+=1;continue
        out.append(s[i]);i+=1
    return ''.join(out)
inst = 0
for dd, _, ff in os.walk('material/evidence/lean/project/RequestProject'):
    for f in ff:
        if f.endswith('.lean'):
            c = strip(open(os.path.join(dd, f), encoding='utf-8').read())
            inst += len(re.findall(r'^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:noncomputable|private|protected|scoped|local)[ \t]+)*instance\b', c, re.M))
print('instance declarations in code:', inst)
