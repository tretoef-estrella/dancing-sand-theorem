# M1: compare the #check output of my run (checks/L1_headline.log) with the author's CertCubo.log
# and with the certificate §1.1 (code blocks), statement by statement, whitespace-normalized.
# Also compare Lean's #eval of FamDec.m with my Python multiplicities.
import re, sys
sys.path.insert(0, 'checks')
def blocks(text):
    # split into top-level entries: a line starting at column 0 with "Name :" begins a new statement
    out = {}; cur = None
    for line in text.splitlines():
        m = re.match(r'^([A-Za-z][\w.\']*) : ', line)
        if m: cur = m.group(1); out[cur] = line[len(cur) + 3:]
        elif cur and line.startswith(' '): out[cur] += ' ' + line.strip()
        else: cur = None
    return {k: ' '.join(v.split()) for k, v in out.items()}
mine = blocks(open('checks/L1_headline.log').read())
cert_log = blocks(open('material/logs/final_checks/CertCubo.log').read())
cmd = open('material/certificate/LEAN_CERTIFICATE_DANCING_SAND_v1.md').read()
code = '\n'.join(re.findall(r'```\n(.*?)```', cmd.split('### 1.2')[0], re.S))
cert_md = blocks(code)
names = ['MainTheorem.M1','MainTheorem.M2','Windows.theorem_D_i','BaiCounts.B1','BaiCounts.B2','PodiumCor.G1','PodiumCor.G2',
 'PodiumCor.G3','Mirror.Y2','FoldLaw.H','FoldLaw.DW',"FoldLaw.DW'",'FoldLaw.L1','FoldLaw.R','OddParts.B1','OddParts.C5',
 'PodiumCor.P1','PodiumCor.P2','PodiumCor.P3']
for n in names:
    a = mine.get(n); b = cert_log.get(n); c = cert_md.get(n)
    print(f'{n:28s} mine==CertCubo.log: {a == b}   mine==certificate §1.1: {a == c}')
    if a != c: print('   mine:', a, '\n   cert:', c)
print('certificate §1.1 statements not in my list:', sorted(set(cert_md) - set(names)))
# multiplicities
import ast, m2_rule as R
log = open('checks/L1_headline.log').read()
i = log.index('[[1], [0, 1]'); j = log.index(']]', i) + 2
lean_m = ast.literal_eval(log[i:j])
py_m = [[R.mult(n).get(lam, 0) for lam in range(n + 1)] for n in range(12)]
print('FamDec.m (Lean #eval) == multiplicities from the paper (Python), n <= 11:', lean_m == py_m)
