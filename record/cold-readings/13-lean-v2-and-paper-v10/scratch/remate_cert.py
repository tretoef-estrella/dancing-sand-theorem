# Grepy Remate: certificate v2 mechanical checks
import re,sys
FC='material/final_checks/'; C='material/certificate/'
log2=open(FC+'CertCubo2.log',encoding='utf-8').read().split('\n')
i=[k for k,l in enumerate(log2) if l.startswith("SmallCases.DW'_all")][0]
j=[k for k,l in enumerate(log2) if l.startswith("SmallCases.G1_all")][0]
blk="\n".join(log2[i:j+5])
for f in ['LEAN_CERTIFICATE_DANCING_SAND_v2.md','LEAN_CERTIFICATE_DANCING_SAND_v2.src.md']:
    t=open(C+f,encoding='utf-8').read()
    print(f,'block of §1.5 byte-identical to CertCubo2.log lines',i+1,'-',j+4,':',('```\n'+blk+'\n```') in t)
    for name in ["SmallCases.DW'_all","SmallCases.L1_all","SmallCases.R_all","SmallCases.G1_all"]:
        print('   occurrences of',name+' :',t.count(name+' :'))
print('log2 lines after G1_all block:',repr(log2[j+4][:60]))
# CheckCubo2 first 21 lines vs postclean
a=open(FC+'CheckCubo_postclean.log',encoding='utf-8').read().split('\n'); b=open(FC+'CheckCubo2.log',encoding='utf-8').read().split('\n')
print('CheckCubo_postclean lines',len(a),'last',a[-2] if a[-1]=='' else a[-1])
print('CheckCubo2 lines',len(b),'last',b[-2] if b[-1]=='' else b[-1])
ax=lambda L:[l for l in L if 'depends on axioms' in l]
A=ax(a);B=ax(b); print('axiom lines',len(A),len(B),'first21 equal:',B[:21]==A, 'first 21 raw lines equal:', b[:21]==a[:21])
print('all B standard:',all(l.endswith('[propext, Classical.choice, Quot.sound]') for l in B))
for l in B[21:]: print('  ',l)
print('non-axiom non-VIGIA lines in CheckCubo2:',[l for l in b if l and 'depends on axioms' not in l and 'VIGIA' not in l][:5])
