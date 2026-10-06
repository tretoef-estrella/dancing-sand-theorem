# Gate of §9 as printed (Corollaries 1.5-1.7, Props 9.3-9.5, Lemmas 9.1, 9.6), on the rule of rule_abs.py.
import sys
from functools import lru_cache
sys.path.insert(0, __file__.rsplit('/',1)[0])
from rule_abs import *
@lru_cache(None)
def Vsym(l):
    out={}
    def add(a,c): out[a]=out.get(a,0)+c
    if l==0: add(1,1)
    elif l%2==1: add(l+1,1)
    else:
        add(l-1,2)
        for l2,c2 in Vsym((l-2)//2): add(2*l2+1,c2)
    return tuple(sorted(out.items()))
@lru_cache(None)
def M(n):
    if n==0: return ((0,1),)
    out={}
    for l,c in M(n-1):
        for l2,c2 in Vsym(l): out[l2]=out.get(l2,0)+c*c2
    return tuple(sorted(out.items()))
def g(N): return max(phi(y) for y in range(1,N)) if N>1 else -10**9
def spectrum(n):
    s={}
    for lam,c in M(n):
        for e,m in X(lam,(n-lam)//2).items(): s[e]=s.get(e,0)+c*m
    s.pop(INF,None); return s
def topk(s,r):
    out=[]
    for e in sorted(s,reverse=True):
        out+=[e]*min(s[e],r-len(out))
        if len(out)>=r: break
    return out
NMAX=int(sys.argv[1]); bad={}
def B(key): bad[key]=bad.get(key,0)+1
cnt={}
def C(key): cnt[key]=cnt.get(key,0)+1
for n in range(2,NMAX+1):
    s=spectrum(n); C('bai')
    if sum(s.values())!=2**(n-1)-1: B('bai_count')
    if s.get(1,0)!=2**(n-2)-2**((n-2)//2): B('bai_z2')
    if n>=4:
        G=g(n-1); t=topk(s,n+1); C('podium')
        if n%2==0: pred=[max(G,phi(n)-1)]+[G]*n
        elif phi(n-1)<=G: pred=[G]*(n+1)
        else: pred=[phi(n-1)]*(n-1)+[max(G,phi(n-1)-2),G]
        if t!=pred: B('podium')
        if t[n-1]==G and not (n%2==1 and phi(n-1)-2>G): pass
        # control: c_n = G always
        if t[n-1]!=G: C('control_cn_not_G')
    if n>=3:
        t=topk(s,n+1)
        if t[0]!=max(g(n),v2(n)+n-1): B('gao41')
        if any(x!=g(n) for x in t[1:n-1]): B('gao42')
        if t[n-1]!=max(g(n-1),v2(n-1)+n-3): B('conj414')
    if n>=4 and topk(s,n+1)[n]!=g(n-1): B('poster')
    # Lemma 9.6
    md=dict(M(n)); C('mult')
    if md.get(n,0)!=1 or md.get(n-2,0)!=n-1-(1 if n%2==0 else 0): B('mult')
    if n%2==1 and n>=5 and md.get(n-4,0)!=(n-1)*(n-2)//2-1-(1 if n%4==1 else 0): B('mult4')
# Props 9.3, 9.4, 9.5 and Lemma 9.1 on cells
def Ys(lam):
    k,I=digits(lam); out=[]; P=0
    out.append(lam+1)
    for t in I: P+=1<<t; out.append(lam+1-P)
    return out
for lam in range(1,301):
    k,I=digits(lam); ds=dancers(I); Y=Ys(lam)
    # Prop 9.3 (i=1)
    e=big_clocks(lam,1); C('p93')
    if e[0]!=max(phi(y) for y in Y): B('p93a')
    m1=max([phi(y) for y in Y[1:]],default=-10**9)
    if any(e[j]>m1 for j in range(1,len(ds))): B('p93b')
    if I and I[0]==0 and e[1]!=m1: B('p93c')
    # Prop 9.4 (i=0)
    if I:
        e0=big_clocks(lam,0); m2=max([phi(y) for y in Y[2:]],default=-10**9)
        C('p94')
        if e0[1]!=max(phi(Y[1])-(1<<I[0]),m2): B('p94a')
        if any(e0[j]>m2 for j in range(2,len(ds))): B('p94b')
    for i in range(1,(301-lam)//2+1):
        n=lam+2*i; bc=big_clocks(lam,i); C('ceil')
        if max(bc)>g(n-i+1): B('ceil')
        if max(bc)>g(n-i): C('ceil_control_fires')
        if min(bc)<2: B('lemma91')
# Cor 1.7
for e_ in range(1,9):
    s1=spectrum(2**e_); s0=spectrum(2**e_-1); C('c17')
    pred={k_:2*v for k_,v in s0.items()}; z=2**e_+e_-1; pred[z]=pred.get(z,0)+1
    if s1!=pred: B('c17')
print("counts:",cnt); print("BAD:",bad if bad else "none")
print("VIGIA-INNER-DONE")
