# chkC51.py — brute force for Lean piece C51 (Theorem DW and its consequences), Grepy Escribano, 10 Oct 2026.
# Direct 2-adic Smith forms of the Laplacians of Q_n and of the folded cube Q_n/<1> (engine of paper/gate/gate_direct.py,
# copied, independent of the dance). Checks, for n = 1..NMAX:
#  (DW)  Syl2 Kbar(n) = 2*Syl2 K(Q_n)   (exponents lowered by one, Z/2 dropped); one zero invariant factor each.
#  (DW') Syl2 K(Q_n) = (Z/2)^{a_n} + H with H free of Z/2 and 2H = Syl2 Kbar(n); a_n = 2^{n-2} - 2^{floor((n-2)/2)}.
#  (L)   l0(Syl2 Kbar) = l1(Syl2 K) = 2^{2^{n-1}-1-a_n}   (n >= 2).
#  (R)   rank_F2 of the folded Laplacian = a_n   (n >= 2).
# Controls (must fire): quotient by x1x2 in place of the fold; a_n + 1; F2-rank of the cube Laplacian in place of the folded one.
import sys, numpy as np
E=31; MOD=1<<E; MASK=MOD-1
def smith2(L):
    A=np.array(L,dtype=np.int64)&MASK; out={}; zeros=0; units=0
    while A.shape[0]>0:
        low=A & (-A); low=np.where(A==0, MOD, low)
        idx=np.argmin(low); r,c=divmod(int(idx),A.shape[1]); m=int(low[r,c])
        if m==MOD: zeros+=A.shape[0]; break
        v=m.bit_length()-1; p=int(A[r,c]); u=p>>v; uinv=pow(u,-1,MOD)
        row=(A[r]*uinv)&MASK; col=A[:,c]>>v
        A=(A-np.outer(col,row))&MASK; A=np.delete(np.delete(A,r,0),c,1)
        if v>0: out[v]=out.get(v,0)+1
        else: units+=1
    return out,zeros,units
def lap(n, mode):
    if mode=='cube': N=1<<n; rep=lambda w:w
    elif mode=='fold': N=1<<(n-1); rep=lambda w: (w ^ ((1<<n)-1)) if (w>>(n-1))&1 else w
    else: N=1<<(n-1); rep=lambda w: (w ^ 3) if w&1 else w
    reps=sorted(set(rep(w) for w in range(1<<n))); pos={w:i for i,w in enumerate(reps)}; assert len(reps)==N
    L=np.zeros((N,N),dtype=np.int64)
    for w in reps:
        i=pos[w]
        for j in range(n): L[i,i]+=1; L[i,pos[rep(w^(1<<j))]]-=1
    return L
def halve(d): return {e-1:c for e,c in d.items() if e>=2}
def an(n): return 2**(n-2)-2**((n-2)//2)
def ncyc(d): return sum(d.values())
nmax=int(sys.argv[1]); checks=0; fails=0; ctl={'x12':0,'an+1':0,'cuberank':0}
def chk(ok,msg):
    global checks,fails
    checks+=1
    if not ok: fails+=1; print('FAIL',msg,flush=True)
for n in range(1,nmax+1):
    sc,zc,uc=smith2(lap(n,'cube')); sf,zf,uf=smith2(lap(n,'fold'))
    chk(zc==1 and zf==1, f'n={n} zeros {zc},{zf}')
    chk(sf==halve(sc), f'n={n} DW')
    if n>=2:
        a=an(n); chk(sc.get(1,0)==a, f'n={n} a_n={a} vs {sc.get(1,0)}')
        H={e:c for e,c in sc.items() if e>=2}
        chk(halve(H)==sf and 1 not in H, f'n={n} DW-prime')
        l0bar=ncyc(sf); l1=ncyc(halve(sc))
        chk(l0bar==l1==2**(n-1)-1-a, f'n={n} layers {l0bar},{l1}')
        chk(ncyc(sc)==2**(n-1)-1, f'n={n} l0 of K')
        rank_fold=uf; chk(rank_fold==a, f'n={n} F2 rank {rank_fold} vs {a}')
        if rank_fold!=a+1: ctl['an+1']+=1
        if uc!=a: ctl['cuberank']+=1
        if n>=3:
            sx,zx,ux=smith2(lap(n,'x12'))
            if sx!=halve(sc): ctl['x12']+=1
    else:
        chk(sc=={} and sf=={}, 'n=1 trivial')
    print(n,'Syl2K',dict(sorted(sc.items())),'Syl2Kbar',dict(sorted(sf.items())),'rankF2(fold)',uf,flush=True)
print('CHECKS',checks,'FAILURES',fails,'CONTROLS',ctl)
