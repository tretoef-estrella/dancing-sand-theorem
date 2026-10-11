# Brute force for C12 (Proposition 4.2, the split move, scaled; and the basis change V⊗Φ -> A,B,C,Dd).
import random, sys
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import invariant_factors
def inv(M):
    n=len(M); v=[abs(int(x)) for x in invariant_factors(Matrix(M),domain=ZZ)]; v+=[0]*(n-len(v))
    return sorted(x for x in v if x!=1)
cnt={}; fails=[]; ctrl={"no-CA-coupling-sp":0,"CC-wrong-floors":0,"no-factor-2":0,"one-copy-only":0,"C-from-A-sign":0}
def ok(n,c,i):
    cnt[n]=cnt.get(n,0)+1
    if not c: fails.append((n,i))
def family(trial):
    rnd=random.Random(trial)
    r=rnd.randint(1,2); nI=rnd.randint(1,2)
    fl=[rnd.randint(0,3) for _ in range(nI)]; dims=[rnd.randint(1,2) for _ in range(nI)]
    off=[];o=0
    for d in dims: off.append(o); o+=d
    dimN=o; flN=[None]*dimN
    for i in range(nI):
        for a in range(dims[i]): flN[off[i]+a]=fl[i]
    Fm=[[rnd.randint(-3,3) for _ in range(dimN)] for _ in range(dimN)]
    p=[[rnd.randint(-3,3) for _ in range(12)] for _ in range(r)]
    kap=[[[rnd.randint(-3,3) for _ in range(12)] for _ in range(r)] for _ in range(r)]
    return r,dimN,flN,Fm,p,kap
def paysys(r,dim,flr,Fop,p,kap):
    # generic payment system matrix: basis (s,idx), F given as matrix Fop[jdx][idx] (image coords)
    n=r*dim; G=[[0]*n for _ in range(n)]
    for s1 in range(r):
        for idx in range(dim):
            col=s1*dim+idx; f=flr[idx]
            for j in range(dim): G[s1*dim+j][col]+=Fop[j][idx]
            G[col][col]+=2*p[s1][f]
            for s in range(s1+1,r): G[s*dim+idx][col]+=2*kap[s][s1][f]
    return G
def run(trial,c,mode="ok"):
    r,dimN,flN,Fm,p,kap=family(trial)
    # Psi model: coordinates (j,idx) j in 0..3 (A,B,C,Dd) -> j*dimN+idx
    D=4*dimN; flP=[0]*D; FP=[[0]*D for _ in range(D)]
    for idx in range(dimN):
        f=flN[idx]
        flP[0*dimN+idx]=2*f; flP[1*dimN+idx]=2*f+1; flP[2*dimN+idx]=2*f+1; flP[3*dimN+idx]=2*f+2
        FP[1*dimN+idx][0*dimN+idx]+=1; FP[2*dimN+idx][0*dimN+idx]+=2      # F A = B + 2C
        for j in range(dimN): FP[0*dimN+j][1*dimN+idx]+=2*Fm[j][idx]     # F B = 2 A_{Fn}
        FP[3*dimN+idx][2*dimN+idx]+=1                                     # F C = Dd
        for j in range(dimN): FP[2*dimN+j][3*dimN+idx]+=2*Fm[j][idx]     # F Dd = 2 C_{Fn}
    GP=paysys(r,D,flP,FP,p,kap)
    lhs=inv([[c*x for x in row] for row in GP])
    # V⊗Φ model: coords (e,e',idx) -> (2e+e')*dimN+idx ; floor 2f+e+e'
    flV=[0]*D; FV=[[0]*D for _ in range(D)]
    def V(e,e2,idx): return (2*e+e2)*dimN+idx
    for idx in range(dimN):
        f=flN[idx]
        for e in (0,1):
            for e2 in (0,1): flV[V(e,e2,idx)]=2*f+e+e2
        # F = F_V⊗1 + 1⊗F_Φ
        for e in (0,1):
            for e2 in (0,1):
                col=V(e,e2,idx)
                if e==0: FV[V(1,e2,idx)][col]+=1
                if e2==0: FV[V(e,1,idx)][col]+=1
                else:
                    for j in range(dimN): FV[V(e,0,j)][col]+=2*Fm[j][idx]
    GV=paysys(r,D,flV,FV,p,kap)
    if mode=="ok":
        ok("basis-change",inv([[c*x for x in row] for row in GV])==lhs,(trial,c))
    # G'' on slots (s,X) lex, X in {A=0,C=1}: slot index 2s+X
    r2=2*r; p2=[[0]*12 for _ in range(r2)]; k2=[[[0]*12 for _ in range(r2)] for _ in range(r2)]
    for s in range(r):
        for f in range(4):
            p2[2*s][f]=-p[s][2*f]*p[s][2*f+1]
            p2[2*s+1][f]=-p[s][2*f+1]*p[s][2*f+2]
    for s1 in range(r):
        for f in range(4):
            sign=1 if mode=="C-from-A-sign" else -1
            k2[2*s1+1][2*s1][f]=sign*p[s1][2*f+1]
            for u in range(s1+1,r):
                midA=sum(kap[s][s1][2*f+1]*kap[u][s][2*f] for s in range(s1+1,u))
                k2[2*u][2*s1][f]=-(p[s1][2*f+1]*kap[u][s1][2*f]+kap[u][s1][2*f+1]*p[u][2*f]+midA)
                if mode=="CC-wrong-floors":
                    midC=sum(kap[s][s1][2*f+1]*kap[u][s][2*f] for s in range(s1+1,u))
                    k2[2*u+1][2*s1+1][f]=-(p[s1][2*f+1]*kap[u][s1][2*f]+kap[u][s1][2*f+1]*p[u][2*f]+midC)
                else:
                    midC=sum(kap[s][s1][2*f+2]*kap[u][s][2*f+1] for s in range(s1+1,u))
                    k2[2*u+1][2*s1+1][f]=-(p[s1][2*f+2]*kap[u][s1][2*f+1]+kap[u][s1][2*f+2]*p[u][2*f+1]+midC)
                if mode!="no-CA-coupling-sp":
                    k2[2*u+1][2*s1][f]=-kap[u][s1][2*f+1]
    G2=paysys(r2,dimN,flN,Fm,p2,k2)
    fac=1 if mode=="no-factor-2" else 2
    rhs=inv([[c*fac*x for x in row] for row in G2])
    copies=1 if mode=="one-copy-only" else 2
    rhs=sorted([x for x in rhs+[abs(c)]*(copies*r*dimN) if x!=1])
    return lhs,rhs
T=int(sys.argv[1]) if len(sys.argv)>1 else 200
for trial in range(T):
    for c in (1,2,4,3,-2):
        l,rr=run(trial,c); ok("split",l==rr,(trial,c,l,rr))
        for m in ctrl:
            l2,r2=run(trial,c,m)
            if l2!=r2: ctrl[m]+=1
# basis change is unimodular: matrix theta over Z with det ±1 and theta*F_V = F_P*theta
print("COUNTS",cnt); print("TOTAL FAILURES",len(fails)); print(fails[:3])
print("CONTROLS",ctrl,"ALL FIRE" if all(v>0 for v in ctrl.values()) else "SOME SILENT")
