# Brute force for C38 (§10.1: the fold in the group ring, Lemma 10.1, Corollary 10.2 in module form).
# Coordinates exactly as in the Lean project: G n = Fin n -> ZMod 2 (tuples), lap (C17), psi (C18),
# tensorPow (C18: tensorFd = b0⊗F r on slot0 + b1⊗F r on slot1 + b1⊗F (r-1) on slot0).
import itertools, random
random.seed(38)
fails=0; checks=0
def check(c,msg):
    global fails,checks
    checks+=1
    if not c:
        fails+=1; print("FAIL",msg)
def basis(n): return list(itertools.product([0,1],repeat=n))
def Fd(n,r,f):
    if n==0: return {(): f[()] if r==0 else 0}
    s0={t[1:]:f[t] for t in f if t[0]==0}; s1={t[1:]:f[t] for t in f if t[0]==1}
    a=Fd(n-1,r,s0); b=Fd(n-1,r,s1); c=Fd(n-1,r-1,s0) if r>=1 else {k:0 for k in s0}
    out={}
    for k in a: out[(0,)+k]=a[k]
    for k in b: out[(1,)+k]=b[k]+c[k]
    return out
def wt(t): return len(t)-2*sum(t)
def psi(n,f):
    if n==0: return {():f[()]}
    s0={g[1:]:f[g] for g in f if g[0]==0}; s1={g[1:]:f[g] for g in f if g[0]==1}
    t0={k:s0[k]+s1[k] for k in s0}; t1={k:-s1[k] for k in s1}
    p0=psi(n-1,t0); p1=psi(n-1,t1); out={}
    for k in p0: out[(0,)+k]=p0[k]
    for k in p1: out[(1,)+k]=p1[k]
    return out
def add(g,h): return tuple((x+y)%2 for x,y in zip(g,h))
def aE(n): return tuple([1]*n)
def ei(n,i): return tuple(1 if j==i else 0 for j in range(n))
def lap(n,f): return {g: n*f[g]-sum(f[add(g,ei(n,i))] for i in range(n)) for g in f}
def transl(n,f,v=None):
    v=aE(n) if v is None else v
    return {g:f[add(g,v)] for g in f}
def expF(n,f,B):
    tot={k:0 for k in f}
    for r in range(B):
        d=Fd(n,r,f)
        for k in d: tot[k]+=d[k]
    return tot
def sign(n,f,c): return {k:(-1)**(abs((c-wt(k))//2))*f[k] for k in f}
def aOp(n,f,c,B): return sign(n,expF(n,f,B),c)
def tau(n,f,c): d=Fd(n,1,f); return {k:d[k]+c*f[k]-wt(k)*f[k] for k in f}
# (L0) F^{(r)} = 0 for r > n
for n in range(0,7):
    for r in range(n+1,n+3):
        f={g:random.randint(-5,5) for g in basis(n)}
        check(all(v==0 for v in Fd(n,r,f).values()),"L0")
# (L1) psi ∘ transl = aOp ∘ psi; (L2) B ≥ n+1 stabilises; controls
ctrl={'swap':0,'nosign':0,'B=n':0}; nctrl=0
for n in range(0,7):
    for t in range(25):
        f={g:random.randint(-9,9) for g in basis(n)}
        p=psi(n,f); lhs=psi(n,transl(n,f))
        check(lhs==aOp(n,p,n,n+1),"L1")
        check(aOp(n,p,n,n+5)==aOp(n,p,n,n+1),"L2")
        # psi ∘ lap = tau ∘ psi (C18, sanity)
        check(psi(n,lap(n,f))==tau(n,p,n),"psi_comm")
        if n>=1:
            nctrl+=1
            if lhs!=expF(n,sign(n,p,n),n+1): ctrl['swap']+=1
            if lhs!=expF(n,p,n+1): ctrl['nosign']+=1
            if lhs!=aOp(n,p,n,n): ctrl['B=n']+=1
print("controls L1 (fire = differ):",ctrl,"of",nctrl)
# (G1) transl involution, commutes with lap; (G2) push: surjective, ker = range(transl-1), push∘lap = lapBar∘push
def cosets(n):
    seen={}; reps=[]
    for g in basis(n):
        h=add(g,aE(n)); key=min(g,h)
        if key not in seen: seen[key]=len(reps); reps.append(key)
    return reps, lambda g: seen[min(g,add(g,aE(n)))]
for n in range(0,7):
    reps,mk=cosets(n)
    for t in range(15):
        f={g:random.randint(-9,9) for g in basis(n)}
        check(transl(n,transl(n,f))==f,"G1 inv")
        check(transl(n,lap(n,f))==lap(n,transl(n,f)),"G1 comm")
        push=lambda F:[sum(F[g] for g in F if mk(g)==j) for j in range(len(reps))]
        def lapBar(u): return [n*u[j]-sum(u[mk(add(reps[j],ei(n,i)))] for i in range(n)) for j in range(len(reps))]
        check(push(lap(n,f))==lapBar(push(f)),"G2 intertwine")
        tf=transl(n,f); check(push({g:tf[g]-f[g] for g in f})==[0]*len(reps),"G2 range⊆ker")
# Smith forms (integer elimination)
def smith(M):
    M=[row[:] for row in M]; m=len(M); k=len(M[0]) if m else 0; d=[]
    r=0
    for c in range(k):
        if r>=m: break
        while True:
            piv=None
            for i in range(r,m):
                for j in range(c,k):
                    if M[i][j]!=0 and (piv is None or abs(M[i][j])<abs(M[piv[0]][piv[1]])): piv=(i,j)
            if piv is None: return d
            i,j=piv; M[r],M[i]=M[i],M[r]
            for row in M: row[c],row[j]=row[j],row[c]
            p=M[r][c]; done=True
            for i in range(r+1,m):
                q=M[i][c]//p
                if q:
                    for j in range(c,k): M[i][j]-=q*M[r][j]
                if M[i][c]: done=False
            for j in range(c+1,k):
                q=M[r][j]//p
                if q:
                    for i in range(r,m): M[i][j]-=q*M[i][c]
                if M[r][j]: done=False
            if done:
                bad=None
                for i in range(r+1,m):
                    for j in range(c+1,k):
                        if M[i][j]%p: bad=(i,j)
                if bad:
                    for j in range(c,k): M[r][j]+=M[bad[0]][j]
                    continue
                d.append(abs(p)); r+=1; break
    return d
def colmat(op,dom):
    # columns = images of basis vectors; returns rows indexed by dom
    cols=[]
    for b in dom:
        f={g:(1 if g==b else 0) for g in dom}; cols.append(op(f))
    return [[cols[j][g] for j in range(len(dom))] for g in dom]
def coker_inv(mats,size):
    M=[sum((mt[i] for mt in mats),[]) for i in range(size)]
    d=smith(M); free=size-len(d)
    return free, sorted(x for x in d if x>1)
def two(xs):
    out=[]
    for x in xs:
        v=0
        while x%2==0: x//=2; v+=1
        if v: out.append(v)
    return sorted(out)
for n in range(1,7):
    dom=basis(n)
    A1=colmat(lambda f:lap(n,f),dom); A2=colmat(lambda f:{g:transl(n,f)[g]-f[g] for g in f},dom)
    left=coker_inv([A1,A2],len(dom))
    T1=colmat(lambda f:tau(n,f,n),dom); T2=colmat(lambda f:{k:aOp(n,f,n,n+1)[k]-f[k] for k in f},dom)
    right=coker_inv([T1,T2],len(dom))
    check(left==right,"C (module form) n=%d"%n)
    reps,mk=cosets(n)
    def lapBarM():
        R=len(reps); M=[[0]*R for _ in range(R)]
        for j in range(R):
            M[j][j]+=n
            for i in range(n): M[mk(add(reps[j],ei(n,i)))][j]-=1
        return M
    bar=coker_inv([lapBarM()],len(reps))
    check(bar==left,"G3 n=%d"%n)
    cube=coker_inv([A1],len(dom))
    # fold law sanity (Theorem DW): 2-part of K̄(n) = 2·Syl2 K(Q_n)
    dw = sorted(v-1 for v in two(cube[1]) if v>=2)
    check(two(bar[1])==dw,"DW sanity n=%d"%n)
    # controls: translation by e_1 instead of a; aOp without sign
    c1=coker_inv([A1,colmat(lambda f:{g:transl(n,f,ei(n,0))[g]-f[g] for g in f},dom)],len(dom))
    c2=coker_inv([T1,colmat(lambda f:{k:expF(n,f,n+1)[k]-f[k] for k in f},dom)],len(dom))
    print("n=%d fold coker free=%d 2-part=%s | ctrl e1 %s | ctrl nosign %s"%(n,bar[0],two(bar[1]),c1!=left,c2!=left))
print("checks",checks,"failures",fails)
