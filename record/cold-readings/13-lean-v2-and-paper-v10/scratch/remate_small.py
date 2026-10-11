# Grepy Remate: independent small-case check (own Smith form, no sympy)
from itertools import product
def snf(M):
    A=[r[:] for r in M]; m=len(A); n=len(A[0]); d=[]; t=0
    while t<min(m,n):
        piv=[(abs(A[i][j]),i,j) for i in range(t,m) for j in range(t,n) if A[i][j]]
        if not piv: break
        _,i,j=min(piv); A[t],A[i]=A[i],A[t]
        for r in A: r[t],r[j]=r[j],r[t]
        done=False
        while not done:
            done=True
            for i in range(t+1,m):
                q=A[i][t]//A[t][t]
                for j in range(n): A[i][j]-=q*A[t][j]
                if A[i][t]: done=False
            for j in range(t+1,n):
                q=A[t][j]//A[t][t]
                for i in range(m): A[i][j]-=q*A[i][t]
                if A[t][j]: done=False
            if not done:
                piv=[(abs(A[i][j]),i,j) for i in range(t,m) for j in range(t,n) if A[i][j] and (i==t or j==t)]
                _,i,j=min(piv); A[t],A[i]=A[i],A[t]
                for r in A: r[t],r[j]=r[j],r[t]
                continue
            bad=[(i,j) for i in range(t+1,m) for j in range(t+1,n) if A[i][j]%A[t][t]]
            if bad:
                i,_=bad[0]
                for j in range(n): A[t][j]+=A[i][j]
                done=False
        d.append(abs(A[t][t])); t+=1
    return d+[0]*(min(m,n)-len(d))
def lap(n,fold):
    V=list(product([0,1],repeat=n))
    key=(lambda v: min(v,tuple(1-x for x in v))) if fold else (lambda v:v)
    R=sorted(set(key(v) for v in V)); ix={r:i for i,r in enumerate(R)}
    L=[[0]*len(R) for _ in R]
    for r in R:
        L[ix[r]][ix[r]]+=n
        for i in range(n):
            w=list(r); w[i]^=1; L[ix[r]][ix[key(tuple(w))]]-=1
    return L
def twoexps(d):
    out=[]
    for x in d:
        if x==0: continue
        e=0
        while x%2==0: x//=2; e+=1
        if e: out.append(e)
    return sorted(out)
def rankF2(M):
    A=[[x%2 for x in r] for r in M]; rk=0; cols=len(A[0])
    for c in range(cols):
        p=next((i for i in range(rk,len(A)) if A[i][c]),None)
        if p is None: continue
        A[rk],A[p]=A[p],A[rk]
        for i in range(len(A)):
            if i!=rk and A[i][c]: A[i]=[(a+b)%2 for a,b in zip(A[i],A[rk])]
        rk+=1
    return rk
aN=lambda n: 2**max(n-2,0)-2**(max(n-2,0)//2)
def v2(x):
    e=0
    while x%2==0: x//=2; e+=1
    return e
gmax=lambda N: max(x+v2(x) for x in range(1,N)) if N>1 else 0
def layer(E,j): return 2**sum(e>j for e in E)
def cExp(E,r): return max([e for e in range(1,40) if 2**r<=layer(E,e-1)],default=0)
for n in range(1,6):
    K=twoexps(snf(lap(n,False))); KB=twoexps(snf(lap(n,True)))
    l0KB=layer(KB,0); rhsL1=2**(2**(n-1)-1-aN(n))
    rk=rankF2(lap(n,True))
    print(f"n={n} Syl2K exps={K} Syl2KBar exps={KB} snfKBar={snf(lap(n,True))} | L1: {l0KB}=={rhsL1} {l0KB==rhsL1} | R: rank={rk} aN={aN(n)} {rk==aN(n)}")
    if n>=2:
        ok1=cExp(K,1)==max(gmax(n),v2(n)+n-1); ok2=all(cExp(K,r)==gmax(n) for r in range(2,n))
        print(f"   G1: cExp1={cExp(K,1)} max={max(gmax(n),v2(n)+n-1)} {ok1} second={ok2}")
print("control: rank at n=1 if lapBar were Laplacian of Q1 instead:",rankF2(lap(1,False)))
