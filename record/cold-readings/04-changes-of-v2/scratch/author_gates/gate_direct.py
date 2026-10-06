# gate_direct.py — direct 2-adic Smith forms of the Laplacians of Q_n, of the folded cube Q_n/<1>,
# and of the control quotient Q_n/<x1x2>; compared with the printed rule (rule_abs.py) and the fold law.
# Grepy Bross, 5 Oct 2026. Independent of the dance engines: plain integer elimination modulo 2^31.
import sys, numpy as np
exec(open(__file__.replace('gate_direct.py','rule_abs.py')).read().split("if __name__")[0])
E=31; MOD=1<<E; MASK=MOD-1
def smith2(L):
    A=np.array(L,dtype=np.int64)&MASK
    out={}; zeros=0
    while A.shape[0]>0:
        low=A & (-A); low=np.where(A==0, MOD, low)
        idx=np.argmin(low); r,c=divmod(int(idx),A.shape[1]); m=int(low[r,c])
        if m==MOD: zeros+=A.shape[0]; break
        v=m.bit_length()-1
        p=int(A[r,c]); u=p>>v; uinv=pow(u,-1,MOD)
        row=(A[r]*uinv)&MASK               # pivot row scaled: pivot = 2^v
        col=A[:,c]>>v                       # multipliers (entries divisible by 2^v)
        A=(A-np.outer(col,row))&MASK        # clears column c (pivot row becomes 0 too)
        A=np.delete(np.delete(A,r,0),c,1)
        if v>0: out[v]=out.get(v,0)+1
    return out,zeros
def lap(n, mode):
    if mode=='cube':
        N=1<<n; rep=lambda w:w
    elif mode=='fold':
        N=1<<(n-1); rep=lambda w: (w ^ ((1<<n)-1)) if (w>>(n-1))&1 else w
    else:  # quotient by e1+e2 : representative with bit0 = 0
        N=1<<(n-1); rep=lambda w: (w ^ 3) if w&1 else w
    reps=sorted(set(rep(w) for w in range(1<<n))); pos={w:i for i,w in enumerate(reps)}
    assert len(reps)==N
    L=np.zeros((N,N),dtype=np.int64)
    for w in reps:
        i=pos[w]
        for j in range(n):
            L[i,i]+=1; L[i,pos[rep(w^(1<<j))]]-=1
    return L
def halve(d): return {e-1:c for e,c in d.items() if e>=2}
nmax=int(sys.argv[1])
bad=0; direct={}
for n in range(2,nmax+1):
    sc,zc=smith2(lap(n,'cube')); rule=syl2(n); direct[n]=sc
    sf,zf=smith2(lap(n,'fold'))
    ok1 = (sc==rule and zc==1); ok2=(sf==halve(sc) and zf==1)
    if n>=3:
        sx,zx=smith2(lap(n,'x12')); ctl=(sx!=halve(sc))
    else: ctl=None
    bad+= (not ok1)+(not ok2)
    print(n,'rule==direct',ok1,'fold law',ok2,'x1x2 control fires',ctl, 'Syl2K',dict(sorted(sc.items())),'Syl2Kbar',dict(sorted(sf.items())),flush=True)
print('BAD',bad)
# controls on the rule (v2): (c1) no pooling (the raw clocks themselves); (c2) the term h(D) omitted from the raw clocks.
import copy
_bc=big_clocks
def bc_nopool(lam,i):
    global pava_int
    keep=pava_int; pava_int=lambda x: list(x)
    try: return _bc(lam,i)
    finally: pava_int=keep
def bc_noh(lam,i):
    k,I=digits(lam); raw=[]
    for D in dancers(I):
        o=sum(1<<t for t in D)
        if i==0 and o==0: raw.append(INF); continue
        xi=lam+1-2*o; raw.append(phi(xi)+kappa(i+o-1,xi))
    return [INF]+pava_int(raw[1:]) if i==0 else pava_int(raw)
for name,f in (('c1 no pooling',bc_nopool),('c2 h(D) omitted',bc_noh)):
    big_clocks=f; fired=[n for n in direct if syl2(n)!=direct[n]]; big_clocks=_bc
    print('control',name,'fails (as it must) at n =',fired)
