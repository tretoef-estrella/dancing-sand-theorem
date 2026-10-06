# check each quotation of the paper against the text extraction of its source (whitespace/hyphenation normalized)
import re
def norm(s):
    s=s.replace('’',"'").replace('ﬁ','fi').replace('ﬀ','ff').replace('ﬂ','fl')
    s=re.sub(r'-\s*\n\s*','',s)  # join hyphenated line breaks
    s=re.sub(r'\s+',' ',s)
    return s.lower()
S='material/sources/'
Q=[('Bai_cube_group_LAA2003.txt','The full structure of the Sylow-2 subgroup of the critical group of the n-cube is still unknown'),
('DuceyJalil_AbelianCayley_arXiv1308.2335.txt','the full structure of the 2-primary component of both the critical group and the Smith group of the n-cube remain unknown'),
('ChandlerSinXiang_arXiv1511.00272.txt','only the 2-Sylow subgroup of the critical group remains to be determined, for both odd and even n. We do not have any conjecture about its exact structure'),
('Adinkras_arXiv2202.02821.txt','the 2-Sylow subgroup of their critical groups, or even the just 2-rank of the Laplacians, has been rather difficult to understand'),
('GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt','determining the complete structure still seems out of reach at this moment'),
('GaoMarxKuoMcDonald_JMMposter2019.txt','the Sylow-2 subgroup remains a mystery'),
('GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt','We are not sure if that is a coincident, or a special case of some deeper connection'),
('TwoAdicAllOnesSquare_arXiv2609.10625.txt','a natural place to look for additional structure under an involution'),
('TwoAdicAllOnesSquare_arXiv2609.10625.txt','Can an analogous integral description with fixed vertices explain both the folded all-ones class and the remaining 2-primary factors?'),
]
for f,q in Q:
    t=norm(open(S+f,errors='ignore').read()); n=norm(q)
    i=t.find(n)
    if i>=0: print('FOUND  ',f,'|',q[:60]); continue
    # longest matching prefix, to locate a difference
    best=0
    for L in range(len(n),10,-1):
        if n[:L] in t: best=L;break
    j=t.find(n[:best]) if best else -1
    print('MISSING',f,'| matched prefix',best,'of',len(n),'| source continues:',repr(t[j:j+len(n)+40]) if j>=0 else '')
