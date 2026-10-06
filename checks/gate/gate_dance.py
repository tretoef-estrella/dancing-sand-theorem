# Gate of §3-§4 of the paper as printed: explicit lattices T(lambda) (§3.3),
# sigma = F + 2^a (i + floor), its 2-adic Smith form computed directly, against
# small clocks + coker(2^k M) with M from the closed form of Theorem 4.4, and
# against the formal dance (Propositions 4.1-4.2). Own code, exact arithmetic.
from fractions import Fraction as Fr
import sys, itertools
INF=10**9
def v2(x):
    x=Fr(x)
    if x==0: return INF
    a,b=x.numerator,x.denominator; v=0
    while a%2==0: a//=2; v+=1
    while b%2==0: b//=2; v-=1
    return v
def smith2(Mat):
    # 2-adic Smith exponents of a square matrix over Z_(2) (entries Fractions with odd denominators)
    A=[row[:] for row in Mat]; n=len(A); ex=[]
    rows=list(range(n)); cols=list(range(len(A[0])))
    while rows and cols:
        best=None
        for r in rows:
            for c in cols:
                if A[r][c]!=0:
                    v=v2(A[r][c])
                    if best is None or v<best[0]: best=(v,r,c)
        if best is None: break
        v,r,c=best; ex.append(v); p=A[r][c]
        for r2 in rows:
            if r2!=r and A[r2][c]!=0:
                f=A[r2][c]/p
                for c2 in cols: A[r2][c2]-=f*A[r][c2]
        rows.remove(r); cols.remove(c)
    ex+= [INF]*(n-len(ex))
    return sorted(ex)
# lattices: list of (floor, Fvector) ; F as dict basis index -> list of (j, coeff)
def lat0(): return {'fl':[0],'F':[[]]}
def Phi(N):
    m=len(N['fl']); fl=[];F=[]
    # index 2*j+e  for b_e n_j
    for j in range(m):
        for e in (0,1):
            fl.append(2*N['fl'][j]+e)
    for j in range(m):
        F.append([(2*j+1,1)])                      # F(b0 n)=b1 n
        F.append([(2*jj,2*c) for (jj,c) in N['F'][j]])   # F(b1 n)=2 b0 Fn
    return {'fl':fl,'F':F}
def VxPhi(N):
    P=Phi(N); m=len(P['fl']); fl=[];F=[]
    # basis b_e (x) p_j, index 2*j+e ; floor = floor(p_j)+e
    for j in range(m):
        for e in (0,1): fl.append(P['fl'][j]+e)
    for j in range(m):
        # F(b0 x p) = b1 x p + b0 x Fp
        F.append([(2*j+1,1)]+[(2*jj,c) for (jj,c) in P['F'][j]])
        # F(b1 x p) = b1 x Fp
        F.append([(2*jj+1,c) for (jj,c) in P['F'][j]])
    return {'fl':fl,'F':F}
memo={}
def T(lam):
    if lam in memo: return memo[lam]
    if lam==0: r=lat0()
    elif lam%2==1: r=Phi(T((lam-1)//2))
    else: r=VxPhi(T((lam-2)//2))
    memo[lam]=r; return r
def digits(lam):
    x=lam+1; k=x.bit_length()-1; I=[t for t in range(k) if (x>>t)&1]; return k,I
def sigma_smith(lam,i,a):
    L=T(lam); n=len(L['fl'])
    M=[[Fr(0)]*n for _ in range(n)]
    for j in range(n):
        M[j][j]+= (2**a)*(i+L['fl'][j])
        for (jj,c) in L['F'][j]: M[jj][j]+=c
    return smith2(M)
def qk(k,I):
    # polynomial as dict frozenset->int
    q={frozenset():-1}
    for t in range(k):
        sq={}
        for A,x in q.items():
            for B,y in q.items():
                if A&B: continue
                C=A|B; sq[C]=sq.get(C,0)+x*y
        if t in I:
            for A,x in q.items():
                if t not in A:
                    C=A|{t}; sq[C]=sq.get(C,0)-x
        q={A:x for A,x in sq.items() if x!=0}
    return q
def closedM(lam,i,a):
    k,I=digits(lam); K=2**k; q=qk(k,I)
    ds=sorted([frozenset(c) for r in range(len(I)+1) for c in itertools.combinations(I,r)],key=lambda D:sum(2**t for t in D))
    o=lambda D:sum(2**t for t in D)
    M=[]
    for D in ds:
        row=[]
        for Dp in ds:
            if Dp<=D:
                Dl=D-Dp; c=-Fr(2)**(1-K+o(Dl))*q.get(Dl,0)
                pr=Fr(1)
                for d in range(o(D),o(Dp)+K): pr*=(2**a)*(i+d)
                row.append(c*pr)
            else: row.append(Fr(0))
        M.append(row)
    return M,k,I
def predicted(lam,i,a):
    M,k,I=closedM(lam,i,a)
    ex=[]
    for h in range(1,k):
        ex+=[h]*(2**(len(I)+k-1-h))
    ex+= [e+k if e<INF else INF for e in smith2(M)]
    ex+= [0]*(2**(k+len(I))-len(ex))
    return sorted(ex)
# formal dance (Props 4.1-4.2) on payments only (late-binding bug of the first run fixed: closures now bind pay, cpl)
def dance_M(lam,i,a):
    k,I=digits(lam)
    slots=[frozenset()]
    pay={frozenset():(lambda f:Fr((2**a)*(i+f)))}
    cpl={}
    for t in range(k):
        newslots=[];npay={};ncpl={}
        def dob(pay,cpl,slots,lo):
            P={};C={}
            for s in slots:
                P[s]=(lambda f,s=s:-pay[s](2*f+lo)*pay[s](2*f+lo+1)/2)
            for s in slots:
                for u in slots:
                    if s<u:
                        mids=[w for w in slots if s<w<u]
                        def kk(f,s=s,u=u,mids=mids):
                            v=pay[s](2*f+lo+1)*cpl.get((u,s),lambda f:0)(2*f+lo)+cpl.get((u,s),lambda f:0)(2*f+lo+1)*pay[u](2*f+lo)
                            for w in mids:
                                v+=cpl.get((w,s),lambda f:0)(2*f+lo+1)*cpl.get((u,w),lambda f:0)(2*f+lo)
                            return -v/2
                        C[(u,s)]=kk
            return P,C
        if t not in I:
            npay,ncpl=dob(pay,cpl,slots,0); newslots=slots
        else:
            PA,CA=dob(pay,cpl,slots,0); PC,CC=dob(pay,cpl,slots,1)
            for s in slots:
                sa=s; sc=s|{t}
                npay[sa]=PA[s]; npay[sc]=PC[s]
            for (u,s),fn in CA.items(): ncpl[(u,s)]=fn
            for (u,s),fn in CC.items(): ncpl[(u|{t},s|{t})]=fn
            for s in slots:
                ncpl[(s|{t},s)]=(lambda f,s=s,pay=pay:-pay[s](2*f+1))
                for u in slots:
                    if s<u and (u,s) in cpl:
                        ncpl[(u|{t},s)]=(lambda f,s=s,u=u,cpl=cpl:-cpl[(u,s)](2*f+1))
            newslots=slots+[s|{t} for s in slots]
        slots=newslots; pay=npay; cpl=ncpl
    o=lambda D:sum(2**t for t in D)
    ds=sorted(slots,key=o)
    return [[(pay[D](0) if D==Dp else (cpl[(D,Dp)](0) if (D,Dp) in cpl else Fr(0))) for Dp in ds] for D in ds]
ok=bad=0; badd=0
LMAX=int(sys.argv[1]); IMAX=int(sys.argv[2])
for lam in range(0,LMAX+1):
    for a in (1,2):
        for i in range(0,IMAX+1):
            if lam==0 and i==0: continue
            Mc,k,I=closedM(lam,i,a); Md=dance_M(lam,i,a)
            if Mc!=Md: badd+=1; print("DANCE!=CLOSED",lam,i,a)
            if 2**(k+len(I))<=64:
                if sigma_smith(lam,i,a)==predicted(lam,i,a): ok+=1
                else: bad+=1; print("SMITH MISMATCH",lam,i,a)
print("Theorem D (direct Smith of sigma on T(lam) = small + coker(2^k M)):",ok,"ok",bad,"bad")
print("closed form = formal dance: mismatches",badd)
# controls (v2): the closed form with the factor 2^{o(Delta)} dropped must differ from the dance, and its predicted Smith form
# must differ from the direct one in some cell.
def closedM_ctrl(lam,i,a):
    k,I=digits(lam); K=2**k; q=qk(k,I)
    ds=sorted([frozenset(c) for r in range(len(I)+1) for c in itertools.combinations(I,r)],key=lambda D:sum(2**t for t in D))
    o=lambda D:sum(2**t for t in D)
    M=[]
    for D in ds:
        row=[]
        for Dp in ds:
            if Dp<=D:
                Dl=D-Dp; c=-Fr(2)**(1-K)*q.get(Dl,0)
                pr=Fr(1)
                for d in range(o(D),o(Dp)+K): pr*=(2**a)*(i+d)
                row.append(c*pr)
            else: row.append(Fr(0))
        M.append(row)
    return M,k,I
cdance=csmith=ctot=0
for lam in range(0,LMAX+1):
    for a in (1,2):
        for i in range(1,IMAX+1):
            Mx,k,I=closedM_ctrl(lam,i,a)
            if not I: continue
            ctot+=1
            if Mx!=dance_M(lam,i,a): cdance+=1
            if 2**(k+len(I))<=64:
                ex=[]
                for h in range(1,k): ex+=[h]*(2**(len(I)+k-1-h))
                ex+=[e+k if e<INF else INF for e in smith2(Mx)]
                ex+=[0]*(2**(k+len(I))-len(ex))
                if sorted(ex)!=sigma_smith(lam,i,a): csmith+=1
print("control (2^{o(Delta)} dropped): differs from the dance in %d of %d cells with I nonempty; Smith prediction wrong in %d cells"%(cdance,ctot,csmith))
print("VIGIA-INNER-DONE")
