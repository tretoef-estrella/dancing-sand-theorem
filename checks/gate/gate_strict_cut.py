# gate_strict_cut.py — «The Dancing Sand Theorem» v2, §7. From the definitions of §7.1 and §7.3, over every house with
# k <= K_MAX, every I, every l, alpha in {1,2,3}: (1) the strict (Cut) of Theorem 7.8: fit(x_H) drops strictly at the
# boundary b of J_H and at its mirror; (2) the integer claims where Lemma 7.2(b) is applied: the penalty shifts of
# Theorem 7.10 (U2), P_r, P_c <= P_MAX, and the deletion of the dancer ∅ in the house l = 2^k - 1 (Theorem 7.10, i = 0); (3) controls.
# v3 (after cold reader 4): the penalty shifts are counted only where they are non-zero (houses with a boundary); the shifted
# fit must also be the real fit plus the shift with the same level sets; (4) Lemma 7.9 (integrality): the real fit of x_H,
# of every shifted sequence and of every deleted sequence takes integer values; (5) three house-level controls that can
# fail: strictness tested one dancer after b, the shift moved one dancer late, and integrality of x_H + e_0 (not a house).
import sys, itertools
from fractions import Fraction as Fr
def s2(x): return bin(x).count('1')
def kap(a,b): return s2(a)+s2(b)-s2(a+b)
def oo(E): return sum(1<<t for t in E)
def fit(x):
    B=[]
    for v in x:
        B.append([Fr(v),1])
        while len(B)>1 and B[-2][0]*B[-1][1] <= B[-1][0]*B[-2][1]:
            s,c=B.pop(); B[-1][0]+=s; B[-1][1]+=c
    z=[]
    for s,c in B: z+=[s/c]*c
    return z,B
def ifit(x):
    z,B=fit(x); out=[]
    for s,c in B:
        S=s.numerator if s.denominator==1 else None
        assert S is not None
        r=S%c; out+=[-(-S//c)]*r+[S//c]*(c-r)
    return out
K_MAX=int(sys.argv[1]); P_MAX=int(sys.argv[2])
stats=dict(houses=0,bnd=0,strict_fail=0,pen_checks=0,pen_fail=0,del_checks=0,del_fail=0,nonint=0,
           ctl_strict_next_tests=0,ctl_strict_next_fires=0,ctl_late_tests=0,ctl_late_fires=0,ctl_e0_fires=0)
def levels(z):
    cuts=[j for j in range(1,len(z)) if z[j-1]!=z[j]]
    return tuple(cuts)
def integral(z): return all(v.denominator==1 for v in z)
for k in range(1,K_MAX+1):
    for r in range(k+1):
        for I in itertools.combinations(range(k),r):
            Iset=set(I)
            def h(t):
                return min([u for u in list(I)+[k] if u>t])-t
            Ds=sorted([frozenset(c) for q in range(r+1) for c in itertools.combinations(I,q)],key=oo)
            N=len(Ds); full=frozenset(I)
            for ell in range(1<<k):
                for a in (1,2,3):
                    R=lambda E: sum(h(t)-a*(1<<t) for t in E)-kap(ell,oo(E))
                    J=lambda E: 1 if ell+oo(E)>=(1<<k) else 0
                    x=[R(D)-R(full-D) for D in Ds]
                    z,_=fit(x); y=ifit(x)
                    stats['houses']+=1
                    Jv=[J(D) for D in Ds]
                    b=next((j for j in range(N) if Jv[j]==1),None)
                    if b is not None and b>0:
                        stats['bnd']+=1
                        mb=N-b
                        if not (z[b-1]>z[b]): stats['strict_fail']+=1
                        if mb<N and not (z[mb-1]>z[mb]): stats['strict_fail']+=1
                    if not integral(z): stats['nonint']+=1
                    xe=[x[0]+1]+x[1:]
                    if not integral(fit(xe)[0]): stats['ctl_e0_fires']+=1
                    if b is not None and b>0:
                        if b+1<N:
                            stats['ctl_strict_next_tests']+=1
                            if not (z[b]>z[b+1]): stats['ctl_strict_next_fires']+=1
                        for Pr in range(P_MAX+1):
                            for Pc in range(P_MAX+1):
                                if Pr==Pc==0: continue
                                sh=[-Pr*Jv[j]+Pc*J(full-Ds[j]) for j in range(N)]
                                xs=[x[j]+sh[j] for j in range(N)]
                                zs,_=fit(xs)
                                stats['pen_checks']+=1
                                ok=(ifit(xs)==[y[j]+sh[j] for j in range(N)] and zs==[z[j]+sh[j] for j in range(N)]
                                    and levels(zs)==levels(z) and integral(zs))
                                if not ok: stats['pen_fail']+=1
                                late=[sh[0]]+sh[:-1]
                                if late!=sh:
                                    stats['ctl_late_tests']+=1
                                    if ifit([x[j]+late[j] for j in range(N)])!=[y[j]+late[j] for j in range(N)]: stats['ctl_late_fires']+=1
                    if ell==(1<<k)-1 and N>1:
                        stats['del_checks']+=1
                        zd,_=fit(x[1:])
                        if ifit(x[1:])!=y[1:] or zd!=z[1:] or not integral(zd): stats['del_fail']+=1
print('RESULT', stats)
# Controls
xc=[3,4,3,4]; dc=[1,1,0,0]
lhs=ifit([u+v for u,v in zip(xc,dc)]); rhs=[u+v for u,v in zip(ifit(xc),dc)]
print('CONTROL counterexample of the reader: integer shift fails ->', lhs!=rhs, lhs, rhs)
zc,_=fit(xc); print('CONTROL it is a non-strict cut at 2 ->', zc[1]==zc[2])
