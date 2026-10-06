# gate_section10.py — gate of §10.1-§10.2 as printed. Grepy Bross, 5 Oct 2026.
# G1 the weights eta_m, eta'_m (Bernoulli formulas, 2-adic units); G2 Lemma 10.1 on V^{(x)n};
# G3 Lemmas 10.4, 10.5 and the family law on the explicit lattices T(lambda) of gate_dance.py.
import sys
from fractions import Fraction as Fr
from math import comb, factorial
src=open(__file__.replace('gate_section10.py','gate_dance.py')).read().split('ok=bad=0')[0]
exec(src)
def dfact(n):  # n!! for odd n>=-1
    r=1
    while n>1: r*=n; n-=2
    return r
# ---------- G1
NB=40
B=[Fr(1)]+[Fr(0)]*(2*NB+1)
for m in range(1,2*NB+2):
    B[m]=-sum(comb(m+1,j)*B[j] for j in range(m))/Fr(m+1)
# series in u: cosh, sinh(u)/u
N=2*NB+2
ch=[Fr(0)]*N; sh=[Fr(0)]*N
for t in range(0,N,2): ch[t]=Fr(1,factorial(t)); sh[t]=Fr(1,factorial(t+1))
def mul(a,b): 
    c=[Fr(0)]*N
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:N-i]): c[i+j]+=x*y
    return c
def inv(a):
    b=[Fr(0)]*N; b[0]=1/a[0]
    for n in range(1,N): b[n]=-sum(a[j]*b[n-j] for j in range(1,n+1))/a[0]
    return b
shi=inv(sh)
tanhser=mul([ch[0]-1]+ch[1:],shi); cothser=mul([ch[0]+1]+ch[1:],shi)
g1bad=0
for m in range(1,NB):
    # coefficient of F^(m): u^(2m) = 2^m m! F^(m)
    e_t=tanhser[2*m]*2**m*factorial(m); e_c=cothser[2*m]*2**m*factorial(m)
    ft=2*(2**(2*m)-1)*B[2*m]/dfact(2*m-1); fc=2*B[2*m]/dfact(2*m-1)
    if e_t!=ft or e_c!=fc or v2(ft)!=0 or v2(fc)!=0: g1bad+=1
assert cothser[0]==2 and tanhser[0]==0
print("G1 weights eta, eta' (m=1..%d): bad"%(NB-1),g1bad, "eta_1",tanhser[2]*2,"eta'_1",cothser[2]*2)
# ---------- G2 Lemma 10.1
g2bad=0
for n in range(1,7):
    S=list(range(1<<n))
    # x_j on basis s_S: x_j = 1 - s_j ; s_j s_S = s_{S+j} or 2 s_S
    def xj(j,vec):
        out={}
        for S_,c in vec.items():
            out[S_]=out.get(S_,0)+c
            if S_>>j&1: out[S_]=out.get(S_,0)-2*c
            else: out[S_|1<<j]=out.get(S_|1<<j,0)-c
        return out
    for S_ in S:
        v={S_:1}
        for j in range(n): v=xj(j,v)
        # (-1)^{floor} exp(F): exp F s_S = sum over supersets T of s_T ; floor = |T|
        w={}
        for T_ in S:
            if T_&S_==S_: w[T_]=(-1)**bin(T_).count('1')
        v={k:c for k,c in v.items() if c}
        if v!=w: g2bad+=1
print("G2 Lemma 10.1 (a = (-1)^floor exp F), n=1..6: bad",g2bad)
# ---------- G3
def Fmat(L):
    n=len(L['fl']); M=[[Fr(0)]*n for _ in range(n)]
    for j in range(n):
        for (jj,c) in L['F'][j]: M[jj][j]+=c
    return M
def mm(A,B_):
    n=len(A); m=len(B_[0]); k=len(B_)
    return [[sum(A[i][t]*B_[t][j] for t in range(k) if A[i][t]) for j in range(m)] for i in range(n)]
def eye(n): return [[Fr(int(i==j)) for j in range(n)] for i in range(n)]
def add(A,B_,s=1): return [[A[i][j]+s*B_[i][j] for j in range(len(A[0]))] for i in range(len(A))]
def scal(c,A): return [[c*x for x in r] for r in A]
def divpows(L):
    F=Fmat(L); n=len(F); P=[eye(n)]; cur=eye(n); m=0
    while True:
        m+=1; cur=mm(cur,F)
        if all(x==0 for r in cur for x in r): break
        P.append(scal(Fr(1,factorial(m)),cur))
    return P   # P[m] = F^(m)
def diagD(L,c): 
    n=len(L['fl']); return [[Fr(L['fl'][i]+c) if i==j else Fr(0) for j in range(n)] for i in range(n)]
def series(P,coef):  # sum coef(m) F^(m)
    n=len(P[0]); A=[[Fr(0)]*n for _ in range(n)]
    for m in range(len(P)): A=add(A,scal(coef(m),P[m]))
    return A
def matinv_unip(A):  # inverse of a matrix = unit*I + nilpotent (exact)
    n=len(A); c=A[0][0]; Nm=add(scal(1/c,A),eye(n),-1); R=eye(n); cur=eye(n)
    for _ in range(n+1):
        cur=scal(-1,mm(cur,Nm)); R=add(R,cur)
    return scal(1/c,R)
def coker(cols_blocks):
    # cokernel of [A1 | A2 | ...] (all n x n): exponents of the finite part and number of free summands
    n=len(cols_blocks[0]); M=[sum((blk[i] for blk in cols_blocks),[]) for i in range(n)]
    ex=smith2(M)
    return sorted(e for e in ex if e>0)
def halve(ex): return sorted((e if e>=INF else e-1) for e in ex if e>=2)  # the free part stays free
def Psi(Ln,j):
    P=divpows(Ln); n=len(P[0])
    Ch=series(P,lambda s: Fr(1,dfact(2*s-1))); Sh=series(P,lambda s: Fr(1,dfact(2*s+1)))
    Shi=matinv_unip(Sh)
    return add(scal(2,add(scal(2,diagD(Ln,0)),scal(j,eye(n)))), mm(add(Ch,scal((-1)**j,eye(n)),-1),Shi))
def glue(X,Y):
    n=len(X); Z=[[Fr(0)]*(2*n) for _ in range(2*n)]
    for i in range(n):
        for j in range(n):
            Z[i][j]=X[i][j]; Z[n+i][n+j]=Y[i][j]; Z[n+i][j]=(Y[i][j]-X[i][j])/2
    return Z
LMAX=int(sys.argv[1]); IMAX=int(sys.argv[2])
cnt={'odd_a':0,'odd_b':0,'even_a':0,'even_b':0,'law':0,'ctl_signfree':0,'ctl_wrongsign':0,'cells':0}
bad=[]
for lam in range(1,LMAX+1):
    L=T(lam); n=len(L['fl']); P=divpows(L)
    for i in range(0,IMAX+1):
        cnt['cells']+=1
        tau=add(P[1] if len(P)>1 else scal(0,eye(n)),scal(2,diagD(L,i)))
        expF=series(P,lambda m:Fr(1))
        sgn=[[Fr((-1)**(L['fl'][r]+i)) if r==c else Fr(0) for c in range(n)] for r in range(n)]
        a=mm(sgn,expF)
        Xbar=coker([tau,add(a,eye(n),-1)]); X=coker([tau]); twoX=halve(X)
        if Xbar==twoX: cnt['law']+=1
        else: bad.append(('law',lam,i))
        a2=add(expF,eye(n),-1)   # control: sign-free fold
        if coker([tau,a2])!=twoX: cnt['ctl_signfree']+=1
        l=(lam-1)//2 if lam%2 else (lam-2)//2; Ln=T(l); m_=len(Ln['fl']); Pn=divpows(Ln)
        if lam%2==1:
            c=(i+1)//2
            if coker([Psi(Ln,i)])==Xbar: cnt['odd_a']+=1
            else: bad.append(('odd_a',lam,i))
            Sig=add(Pn[1] if len(Pn)>1 else scal(0,eye(m_)),scal(4,diagD(Ln,c)))
            if coker([Sig])==twoX: cnt['odd_b']+=1
            else: bad.append(('odd_b',lam,i))
            # control: wrong sign in Psi
            Pw=add(Psi(Ln,i),mm(scal(2*(-1)**i,eye(m_)),matinv_unip(series(Pn,lambda s: Fr(1,dfact(2*s+1))))))
            if coker([Pw])!=Xbar: cnt['ctl_wrongsign']+=1
        else:
            A1=Psi(Ln,i+1); A0=Psi(Ln,i)
            if coker([glue(A1,A0)])==Xbar: cnt['even_a']+=1
            else: bad.append(('even_a',lam,i))
            th1=scal(Fr(1,2),mm(A1,add(A1,scal(2,eye(m_)),-1))); th0=scal(Fr(1,2),mm(A0,add(A0,scal(2,eye(m_)))))
            if coker([glue(th1,th0)])==twoX: cnt['even_b']+=1
            else: bad.append(('even_b',lam,i))
print("G3 cells",cnt); print("BAD",bad[:20], len(bad))
print("VIGIA-INNER-DONE")
