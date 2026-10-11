# Brute force for C11 (Proposition 4.1, the twist move, scaled form):
# coker(c*G_Phi) ~= (B/cB)^{rank} (+) coker(c*2*G'), compared by invariant factors over Z.
import random, sys
from itertools import product
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import invariant_factors
def snf_invariants(M):
    # invariant factors over Z of a square integer matrix (sympy); 0 = free summand; 1s dropped
    n=len(M)
    inv=[abs(int(x)) for x in invariant_factors(Matrix(M),domain=ZZ)]
    inv+=[0]*(n-len(inv))
    return sorted(x for x in inv if x!=1)
def group(inv): return sorted(inv)
cnt={}; fails=[]; ctrl={"no-middle":0,"pu-wrong-floor":0,"no-factor-2":0,"no-B1-summand":0}
def ok(n,c,i):
    cnt[n]=cnt.get(n,0)+1
    if not c: fails.append((n,i))
def build(trial,c,mode="ok"):
    rnd=random.Random(trial)
    r=rnd.randint(1,3); nI=rnd.randint(1,3)
    fl=[rnd.randint(0,3) for _ in range(nI)]; dims=[rnd.randint(1,2) for _ in range(nI)]
    # N index offsets
    off=[];o=0
    for d in dims: off.append(o); o+=d
    dimN=o
    Fm=[[rnd.randint(-3,3) for _ in range(dimN)] for _ in range(dimN)]  # F on total N (any linear map)
    p=[[rnd.randint(-3,3) for _ in range(10)] for _ in range(r)]
    kap=[[[rnd.randint(-3,3) for _ in range(10)] for _ in range(r)] for _ in range(r)]
    # coordinates of N-total: index (i,a) a<dims[i] -> off[i]+a
    def flN(idx):
        for i in range(nI):
            if off[i]<=idx<off[i]+dims[i]: return fl[i]
    # Phi total: slot s, e in {0,1}, idx in N -> s*2*dimN + e*dimN + idx ; floor 2 fl + e
    nP=r*2*dimN
    G=[[0]*nP for _ in range(nP)]   # column = image of basis vector
    def P(s,e,idx): return s*2*dimN+e*dimN+idx
    for s1 in range(r):
        for idx in range(dimN):
            f=flN(idx)
            # b0 idx in slot s1
            col=P(s1,0,idx)
            G[P(s1,1,idx)][col]+=1
            G[col][col]+=2*p[s1][2*f]
            for s in range(s1+1,r): G[P(s,0,idx)][col]+=2*kap[s][s1][2*f]
            col=P(s1,1,idx)
            for jdx in range(dimN): G[P(s1,0,jdx)][col]+=2*Fm[jdx][idx]
            G[col][col]+=2*p[s1][2*f+1]
            for s in range(s1+1,r): G[P(s,1,idx)][col]+=2*kap[s][s1][2*f+1]
    lhs=snf_invariants([[c*x for x in row] for row in G])
    # G' on N^r
    nQ=r*dimN
    def Q(s,idx): return s*dimN+idx
    Gp=[[0]*nQ for _ in range(nQ)]
    for s1 in range(r):
        for idx in range(dimN):
            f=flN(idx); col=Q(s1,idx)
            for jdx in range(dimN): Gp[Q(s1,jdx)][col]+=Fm[jdx][idx]
            pp=-p[s1][2*f]*p[s1][2*f+1]
            Gp[col][col]+=2*pp
            for u in range(s1+1,r):
                mid=sum(kap[s][s1][2*f+1]*kap[u][s][2*f] for s in range(s1+1,u))
                if mode=="no-middle": mid=0
                pu=p[u][2*f+1] if mode=="pu-wrong-floor" else p[u][2*f]
                kp=-(p[s1][2*f+1]*kap[u][s1][2*f]+kap[u][s1][2*f+1]*pu+mid)
                Gp[Q(u,idx)][col]+=2*kp
    fac=1 if mode=="no-factor-2" else 2
    rhs=snf_invariants([[c*fac*x for x in row] for row in Gp])
    b1=[] if mode=="no-B1-summand" else [abs(c)]*(r*dimN)
    rhs=sorted([x for x in rhs+b1 if x!=1])
    return lhs,rhs,(r,fl,dims)
T=int(sys.argv[1]) if len(sys.argv)>1 else 300
for trial in range(T):
    for c in (1,2,4,3,-2):
        lhs,rhs,info=build(trial,c)
        ok("twist",lhs==rhs,(trial,c,info,lhs,rhs))
        for m in ctrl:
            l2,r2,_=build(trial,c,m)
            if l2!=r2: ctrl[m]+=1
print("COUNTS",cnt); print("TOTAL FAILURES",len(fails)); print(fails[:3])
print("CONTROLS",ctrl,"ALL FIRE" if all(v>0 for v in ctrl.values()) else "SOME SILENT")
