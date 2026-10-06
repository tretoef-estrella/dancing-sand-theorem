# control for quotes.py (altered quotes must be MISSING), and context of the cited numbered items
import re,sys
def norm(s):
    s=s.replace('’',"'").replace('ﬁ','fi'); s=re.sub(r'-\s*\n\s*','',s); return re.sub(r'\s+',' ',s)
S='material/sources/'
t=norm(open(S+'Bai_cube_group_LAA2003.txt',errors='ignore').read()).lower()
for q in ['the full structure of the sylow-2 subgroup of the critical group of the n-cube is unknown','the 2-sylow subgroup remains a mystery']:
    print('CONTROL (must be MISSING):', 'FOUND' if q in t else 'MISSING', '|', q)
def ctx(f,pat,w=220,maxn=4):
    t=norm(open(S+f,errors='ignore').read())
    ms=list(re.finditer(pat,t))
    print('##',f,'|',pat,'| hits',len(ms))
    for m in ms[:maxn]: print('   ...',t[max(0,m.start()-60):m.start()+w],'...')
G='GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt'
for p in [r'Theorem 4\.1[ .]',r'Theorem 4\.2[ .]',r'Conjecture 4\.14',r'Conjecture 5\.4',r'Proposition 1\.9',r'Proposition 2\.12',r'Remark 2\.13',r'Remark 4\.4',r'Proposition 2\.5',r'Table 1',r'2\.2 ']:
    ctx(G,p,180,2)
B='Bai_cube_group_LAA2003.txt'
for p in [r'Theorem 1\.1',r'Theorem 1\.2',r'Theorem 1\.3',r'Lemma 2\.2',r'Corollary 2\.3',r'still unknown']:
    ctx(B,p,200,2)
ctx('Adinkras_arXiv2202.02821.txt',r'Proposition 37',200,2)
ctx('Adinkras_arXiv2202.02821.txt',r'rather difficult',10,1)
ctx('ChandlerSinXiang_arXiv1511.00272.txt',r'5\.2',120,3)
ctx('TwoAdicAllOnesSquare_arXiv2609.10625.txt',r'natural place to look',10,1)
ctx('Larsen_arXiv2405.16015.txt',r'^.{0}|2\. ',150,3)
ctx('ReinerTseng_arXiv1301.2977.txt',r'signed graph',200,2)
