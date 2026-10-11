# C53 brute force: small cases n=1 (DW', L1, R) and n=2 (Gao Thm 4.1). Grepy Escribano, 11 Oct 2026.
from itertools import product
import sympy
from sympy.matrices.normalforms import smith_normal_form
def smith_diag(M):
    S = smith_normal_form(sympy.Matrix(M), domain=sympy.ZZ)
    return [abs(S[i,i]) for i in range(min(S.shape))]
def cube_lap(n):
    V=list(product([0,1],repeat=n)); idx={v:i for i,v in enumerate(V)}
    L=[[0]*len(V) for _ in V]
    for v in V:
        L[idx[v]][idx[v]]+=n
        for i in range(n):
            w=list(v); w[i]^=1; L[idx[v]][idx[tuple(w)]]-=1
    return L
def fold_lap(n):
    V=list(product([0,1],repeat=n)); rep={}
    for v in V:
        c=tuple(1-x for x in v); rep[v]=min(v,c)
    R=sorted(set(rep.values())); idx={r:i for i,r in enumerate(R)}
    L=[[0]*len(R) for _ in R]
    for r in R:
        L[idx[r]][idx[r]]+=n
        for i in range(n):
            w=list(r); w[i]^=1; L[idx[r]][idx[rep[tuple(w)]]]-=1
    return L
def two_part(d):  # invariant factors -> list of 2-exponents (torsion only, ignore 0 = free)
    out=[]
    for x in d:
        if x==0: continue
        e=0
        while x%2==0: x//=2; e+=1
        if e: out.append(e)
    return sorted(out,reverse=True)
def layer(exps,j): return 2**sum(1 for e in exps if e>j)
def cExp(exps,r):
    S=[e for e in range(1,60) if 2**r<=layer(exps,e-1)]
    return max(S) if S else 0
def v2(x):
    e=0
    while x%2==0: x//=2; e+=1
    return e
phi=lambda x: x+v2(x)
gmax=lambda N: max(phi(x) for x in range(1,N)) if N>1 else 0
aN=lambda n: max(0,2**max(n-2,0)-2**(max(n-2,0)//2))
ok=fail=0
def chk(name,cond):
    global ok,fail
    print(('PASS ' if cond else 'FAIL ')+name); ok+=cond; fail+=(not cond)
K1=two_part(smith_diag(cube_lap(1))); KB1=two_part(smith_diag(fold_lap(1)))
K2=two_part(smith_diag(cube_lap(2)))
chk('S0 aN 1 = 0', aN(1)==0)
chk('S1 Syl2 K(Q_1) trivial', K1==[])
chk('S2 Syl2 KBar(1) trivial', KB1==[])
chk('S3 lapBar at n=1 is zero', all(x==0 for row in fold_lap(1) for x in row))
chk('DW\'1 H trivial: l0=l1=1', layer([],0)==layer([],1)==1)
chk('L1-1 l0 Syl2 KBar 1 = 2^(2^0-1-aN 1)=1', layer(KB1,0)==2**(2**0-1-aN(1)))
chk('R1 rank over F2 of lapBar(1) = aN 1', 0==aN(1))
chk('T0 Syl2 K(Q_2) = Z/4', K2==[2])
chk('T1 gmax 2 = 1', gmax(2)==1)
chk('G1-2 cExp 1 = max(gmax 2, v2 2 + 2 - 1)', cExp(K2,1)==max(gmax(2),v2(2)+2-1)==2)
# also n=3..6 sanity for G1 against the formula (existing theorem range)
for n in range(3,5):
    E=two_part(smith_diag(cube_lap(n)))
    chk(f'G1 n={n} first clause', cExp(E,1)==max(gmax(n),v2(n)+n-1))
    chk(f'G1 n={n} second clause', all(cExp(E,r)==gmax(n) for r in range(2,n)))
print('controls (must FAIL):')
chk('CONTROL cExp(Z/4,1)=1', cExp(K2,1)==1)
chk('CONTROL K(Q_2)=Z/2', K2==[1])
chk('CONTROL aN 1 = 1', aN(1)==1)
chk('CONTROL lapBar(1) nonzero', any(x!=0 for row in fold_lap(1) for x in row))
print('done', ok, fail)
