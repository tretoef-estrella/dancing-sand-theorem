# Brute force for piece C10 (Lemma 4.5, rescaling of Theorem 4.4, closed-form valuation).
from fractions import Fraction as Fr
from itertools import combinations
import sys
def subsets(S):
    S=sorted(S)
    for r in range(len(S)+1):
        for c in combinations(S,r): yield frozenset(c)
def v2(x):
    x=Fr(x); assert x!=0
    n,d=x.numerator,x.denominator; v=0
    while n%2==0: n//=2; v+=1
    while d%2==0: d//=2; v-=1
    return v
def a_table(I,T,mode="ok"):
    U=frozenset(range(T+1)); allD=list(subsets(U))
    a=[{D:(-1 if not D else 0) for D in allD}]
    for t in range(T):
        prev=a[-1]; nxt={}
        for D in allD:
            s=0
            for D1 in subsets(D):
                s+=prev[D1]*prev[D-D1]
            tt = t+1 if mode=="shiftI" else t
            if tt in I and t in D: s-=prev[D-{t}]
            nxt[D]=s
        a.append(nxt)
    return a
def c_table(I,T,mode="ok"):
    U=frozenset(range(T+1)); allD=list(subsets(U))
    c=[{D:(Fr(1) if not D else Fr(0)) for D in allD}]
    for h in range(T):
        prev=c[-1]; nxt={}
        for D in allD:
            s=Fr(0)
            for D1 in subsets(D): s+=prev[D1]*prev[D-D1]
            s=-s/2
            if h in I and h in D: s-=prev[D-{h}]
            nxt[D]=s
        c.append(nxt)
    return c
oE=lambda D: sum(2**t for t in D)
cnt={}; fails=[]
def ok(name,cond,info):
    cnt[name]=cnt.get(name,0)+1
    if not cond: fails.append((name,info))
ctrl={"no-cross-double":0,"shiftI":0,"card-1":0,"rescale-wrong":0,"valuation-no-delta":0}
KMAX=int(sys.argv[1]) if len(sys.argv)>1 else 5
for k in range(1,KMAX+1):
    for I in subsets(range(k)):
        a=a_table(I,k); c=c_table(I,k); ash=a_table(I,k,"shiftI")
        for t in range(k+1):
            for D in a[t]:
                # support
                if not D<=frozenset(x for x in I if x<t): ok("support",a[t][D]==0,(k,I,t,D))
                # rescaling
                ok("rescale", c[t][D]==-Fr(2)**(1-2**t)*Fr(2)**oE(D)*a[t][D],(k,I,t,D))
                if c[t][D]!=-Fr(2)**(1-2**(t+1))*Fr(2)**oE(D)*a[t][D]: ctrl["rescale-wrong"]+=1
        for t in range(1,k+1): ok("const1",a[t][frozenset()]==1,(k,I,t))
        for D in subsets(I):
            if not D: continue
            for t in range(max(D)+1,k+1):
                val=a[t][D]; ok("nonzero",val!=0,(k,I,t,D))
                if val!=0:
                    ok("deficit",v2(val)==t-len(D)-min(D),(k,I,t,D,val))
                    if v2(val)!=t-(len(D)-1)-min(D): ctrl["card-1"]+=1
                if ash[t][D]==0 or v2(ash[t][D])!=t-len(D)-min(D): ctrl["shiftI"]+=1
        # Lemma 4.5 uniform form with delta
        for D in subsets(I):
            d = 0 if not D else k-len(D)-min(D)
            ok("lemma45", a[k][D]!=0 and v2(a[k][D])==d,(k,I,D))
        # subadditivity
        for D1 in subsets(range(k)):
            for D2 in subsets(range(k)):
                if D1 and D2 and not (D1&D2):
                    dl=lambda D: k-len(D)-min(D)
                    ok("subadd", dl(D1)+dl(D2)-dl(D1|D2)==k-max(min(D1),min(D2)) and k-max(min(D1),min(D2))>=1,(k,D1,D2))
        # closed form valuation (Part C)
        K=2**k
        for alpha in (1,2):
            for i in range(0,4):
                for D in subsets(I):
                    for Dp in subsets(D):
                        if i+oE(D)<1: continue
                        Dl=D-Dp
                        prod=Fr(1)
                        for dd in range(oE(D),oE(Dp)+K): prod*=Fr(2)**alpha*(i+dd)
                        M=-Fr(2)**(1-K+oE(Dl))*a[k][Dl]*prod
                        ok("M-integer",M.denominator==1,(k,I,alpha,i,D,Dp))
                        delt=0 if not Dl else k-len(Dl)-min(Dl)
                        rhs=1-K+oE(Dl)+delt+sum(alpha+v2(i+dd) for dd in range(oE(D),oE(Dp)+K))
                        ok("M-val",M!=0 and v2(M)==rhs,(k,I,alpha,i,D,Dp))
                        if v2(M)!=rhs-delt: ctrl["valuation-no-delta"]+=1
                        ok("window",oE(Dp)+K-oE(D)==K-oE(Dl) and K-oE(Dl)>=1,(k,D,Dp))
        # control: no cross doubling (a_{t+1} = a_t(D) + sum over unordered splits?) -> use squares only of diag
        for t in range(k):
            pass
# no-cross-double control: replace q^2 coefficient by sum over UNORDERED splits
def a_unordered(I,T):
    U=frozenset(range(T+1)); allD=list(subsets(U))
    a=[{D:(-1 if not D else 0) for D in allD}]
    for t in range(T):
        prev=a[-1]; nxt={}
        for D in allD:
            s=0; seen=set()
            for D1 in subsets(D):
                key=frozenset([D1,D-D1])
                if key in seen: continue
                seen.add(key); s+=prev[D1]*prev[D-D1]
            if t in I and t in D: s-=prev[D-{t}]
            nxt[D]=s
        a.append(nxt)
    return a
for k in range(1,KMAX+1):
    for I in subsets(range(k)):
        a=a_unordered(I,k)
        for D in subsets(I):
            if D:
                if a[k][D]==0 or v2(a[k][D])!=k-len(D)-min(D): ctrl["no-cross-double"]+=1
# example lambda=6
a=a_table(frozenset({0,1}),2)
ex={frozenset():1,frozenset({0}):2,frozenset({1}):-1,frozenset({0,1}):-1}
ok("example6",all(a[2][D]==v for D,v in ex.items()) and a[1][frozenset()]==1 and a[1][frozenset({0})]==1,a[2])
print("COUNTS",cnt); print("TOTAL FAILURES",len(fails)); print(fails[:5])
print("CONTROLS",ctrl,"ALL FIRE" if all(v>0 for v in ctrl.values()) else "SOME SILENT")
