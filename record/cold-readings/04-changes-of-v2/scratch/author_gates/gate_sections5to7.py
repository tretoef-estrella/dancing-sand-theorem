# Gate of §5-§7 as printed (own code, written from the paper's text only).
import sys, itertools
from fractions import Fraction as Fr
sys.setrecursionlimit(10000)
exec(open(__file__.replace('gate_sections5to7.py','gate_dance.py')).read().split('ok=bad=0')[0])
def s2(x): return bin(x).count('1')
def kap(a,b): return s2(a)+s2(b)-s2(a+b)
def oo(E): return sum(2**t for t in E)
def dancers(I): return sorted([frozenset(c) for r in range(len(I)+1) for c in itertools.combinations(I,r)],key=oo)
def nxt(t,I,k):
    u=[x for x in list(I)+[k] if x>t]; return min(u)
def hgap(t,I,k): return nxt(t,I,k)-t
def gold(Dl,I,k):
    if not Dl: return 0
    mn=min(Dl); return sum(hgap(u,I,k) for u in I if u not in Dl and u>mn)
def fitreal(x):
    blocks=[]  # [sum,count]
    for v in x:
        blocks.append([Fr(v),1])
        while len(blocks)>1 and blocks[-2][0]/blocks[-2][1] <= blocks[-1][0]/blocks[-1][1]:
            s,c=blocks.pop(); blocks[-1][0]+=s; blocks[-1][1]+=c
    z=[];
    for s,c in blocks: z+= [s/c]*c
    return z,blocks
def fitint(x):
    z,blocks=fitreal(x); out=[]
    for s,c in blocks:
        assert s.denominator==1; S=int(s); r=S%c
        out+= [-(-S//c)]*r + [S//c]*(c-r)
    return out
def separated(x):
    z,blocks=fitreal(x); ms=[s/c for s,c in blocks]
    import math
    return all(math.floor(ms[j])>=math.ceil(ms[j+1]) for j in range(len(ms)-1))
def cut_at(x,b):
    if b<=0 or b>=len(x): return True
    return fitreal(x)[0]==fitreal(x[:b])[0]+fitreal(x[b:])[0]
def RH(E,I,k,ell,a): return sum(hgap(t,I,k)-a*2**t for t in E)-kap(ell,oo(E))
def JH(E,k,ell): return 1 if ell+oo(E)>=2**k else 0
def xH(I,k,ell,a):
    ds=dancers(I); IS=frozenset(I); return [RH(D,I,k,ell,a)-RH(IS-D,I,k,ell,a) for D in ds],ds
def run(t,ell):  # consecutive ones of ell starting at bit t
    r=0
    while (ell>>(t+r))&1: r+=1
    return r
stats={'walk':0,'walkbad':0,'E':0,'M':0,'G':0,'Gbad':0,'Ebad':0,'Mbad':0,'cut':0,'cutbad':0,'lam':0,'lambad':0,'sep':0,'sepbad':0,'interval_empty':0}
def build(I,k,ell,a,mode,nogold=False):
    I=tuple(sorted(I))
    if not I: return {frozenset():0}
    c=I[-1]; Ip=I[:-1]; h=k-c; ellp=ell%(2**c)
    Vp=build(Ip,c,ellp,a,mode,nogold)
    T=(ell>>c)&1
    kap_=min(run(c,ell),h) if T==1 else 1+min(run(c+1,ell),h-1)
    tau=h-a*2**c-(kap_ if T==1 else 0)
    dp=dancers(Ip); IpS=frozenset(Ip)
    xp,_=xH(Ip,c,ellp,a); yp=fitint(xp)
    Jp={D:JH(D,c,ellp) for D in dp}
    d1={D:-tau-(kap_*Jp[D] if T==1 else 0)+(kap_*Jp[IpS-D] if T==0 else 0) for D in dp}
    X1={D:yp[j]+d1[D] for j,D in enumerate(dp)}
    # walk gate
    x,ds=xH(I,k,ell,a); y=fitint(x); N2=len(dp)
    pred=[max(X1[D],0) for D in dp]+[min(-X1[IpS-D],0) for D in dp]
    stats['walk']+=1
    if pred!=y: stats['walkbad']+=1
    v={}
    for D in dp:
        v[D]=Vp[D]-(kap_*Jp[D] if T==1 else 0)
        v[D|{c}]=tau+Vp[D]-(kap_*Jp[D] if T==0 else 0)
    if X1[IpS]>0: return v
    F1=[D for D in dp if X1[D]<=0]; f=F1[0]; IS=frozenset(I)
    F=set(F1)|{IS-D for D in F1}
    c3=v[f]; c4=v[IS-f]
    lo=c3; hi=c4
    idx=dp.index(f)
    if idx>0:
        p=dp[idx-1]; lo=max(lo,v[IS-p]); hi=min(hi,v[p])
    if lo>hi: stats['interval_empty']+=1
    if mode=='lo': cF=lo
    elif mode=='hi': cF=hi
    elif mode=='mid': cF=(lo+hi)//2
    elif mode=='bad': cF=v[IpS]   # control: natural price
    for D in F: v[D]=cF
    return v
def check_house(I,k,ell,a,mode,nogold=False):
    V=build(I,k,ell,a,mode)
    x,ds=xH(I,k,ell,a); y=fitint(x); IS=frozenset(I)
    okE=all(V[D]-V[IS-D]==y[j] for j,D in enumerate(ds))
    okM=all(V[ds[j]]>=V[ds[j+1]] for j in range(len(ds)-1))
    okG=True
    for aa in ds:
        for bb in ds:
            if bb<aa:
                g=0 if nogold else gold(aa-bb,I,k)
                if V[aa]-V[bb] > RH(aa,I,k,ell,a)-RH(bb,I,k,ell,a)+g: okG=False
    J=[JH(D,k,ell) for D in ds]
    b=next((j for j in range(len(ds)) if J[j]==1),None)
    okC=True if b is None else (cut_at(x,b) and cut_at(x,len(ds)-b))
    okL=all(abs(t)<=a*(2**k-1) for t in y)
    return okE,okM,okG,okC,okL,separated(x)
mode_list=['lo','hi','mid']
LMAX=int(sys.argv[1]); AMAX=int(sys.argv[2])
nh=0
for lam in range(1,LMAX+1):
    k,I=digits(lam)
    if not I: continue
    for a in range(1,AMAX+1):
        for ell in range(2**k):
            for mode in mode_list:
                okE,okM,okG,okC,okL,sep=check_house(I,k,ell,a,mode)
                nh+=1
                for key,ok in (('E',okE),('M',okM),('G',okG),('cut',okC),('lam',okL),('sep',sep)):
                    stats[key]+=1
                    if not ok: stats[key+'bad' if key in ('cut','lam','sep') else key+'bad']+=1
print("Theorem F on houses lam<=%d, alpha<=%d, every ell, three prices: %d house-checks"%(LMAX,AMAX,nh))
print(stats)
# controls
cg=0; cb=0
for lam in range(1,64):
    k,I=digits(lam)
    if not I: continue
    for ell in range(2**k):
        if not check_house(I,k,ell,1,'mid',nogold=True)[2]: cg+=1
        r=check_house(I,k,ell,1,'bad')
        if not all(r[:3]): cb+=1
print("CONTROL no gold: (G) fails in",cg,"houses (lam<64, alpha=1); CONTROL c_F = v'(I'): fails in",cb,"houses")
# cost form, Prop 5.3, 5.4, Theorem O, Theorem 7.10 on real cells
cf=cfb=0; p53=p53b=0; p54=p54b=0; sm=smb=0; Ob=0; On=0
def u_clock(lam,i,D):
    xi=lam+1-2*oo(D); k,I=digits(lam)
    return xi+ (len(bin(xi))-len(bin(xi).rstrip('0'))) + kap(i+oo(D)-1,xi) + sum(hgap(t,I,k) for t in D)
for lam in range(1,64):
    k,I=digits(lam); K=2**k; ds=dancers(I); IS=frozenset(I)
    for a in (1,2):
        for i in range(0,41):
            if i==0 and a==2: continue
            Mc,_,_=closedM(lam,i,a)
            if i>=1:
                m=i-1
                for r_,D in enumerate(ds):
                    for c_,Dp in enumerate(ds):
                        if Dp<=D:
                            pv=a*K+kap(m,K)+RH(D,I,k,m,a)-RH(Dp,I,k,m+K,a)+gold(D-Dp,I,k)
                            cf+=1
                            if v2(Mc[r_][c_])!=pv: cfb+=1
                if a==1:
                    for D in ds:
                        p53+=1
                        if u_clock(lam,i,D)!=k+K+kap(m,K)+RH(D,I,k,m,1)-RH(IS-D,I,k,m+K,1): p53b+=1
            else:
                for D in ds:
                    if D:
                        p54+=1
                        if u_clock(lam,0,D)!=k+K+RH(D,I,k,K-1,1)-RH(IS-D,I,k,K-1,1): p54b+=1
            if i<=12 and len(ds)<=16:
                if i>=1:
                    x=[RH(D,I,k,i-1,a)-RH(IS-D,I,k,i-1+K,a) for D in ds]
                    pred=sorted(a*K+kap(i-1,K)+t for t in fitint(x))
                else:
                    x=[RH(D,I,k,K-1,a)-RH(IS-D,I,k,K-1,a) for D in ds][1:]
                    pred=sorted([INF]+[a*K+t for t in fitint(x)])
                sm+=1
                if smith2(Mc)!=pred: smb+=1
print("cost form (Prop 5.2): %d entries, %d bad; Prop 5.3: %d, %d bad; Prop 5.4: %d, %d bad"%(cf,cfb,p53,p53b,p54,p54b))
print("Theorem 7.10 (Smith of M = pooled clocks), lam<64, i<=12, alpha=1,2: %d cells, %d bad"%(sm,smb))
# Theorem O: count golden bijections L_r -> F_r by brute force, |I|<=3 (s in range(0,4)) plus six sets of size 2-3: 61 cases. The paper (v2) cites gate_theoremO.py, |I| <= 5, with controls.
def golden(a_,b_,I):
    if not b_<=a_: return False
    Dl=a_-b_
    if not Dl: return True
    mn=min(Dl); return all(u in Dl for u in I if u>=mn)
cnt_bad=0; tot=0
for s in range(0,4):
    I=list(range(s)); ds=dancers(I); N=len(ds)
    for r in range(0,N+1):
        L=ds[N-r:]; Fr_=ds[:r]; c=0
        for perm in itertools.permutations(Fr_):
            if all(golden(L[j],perm[j],I) for j in range(r)): c+=1
        tot+=1
        if c!=1: cnt_bad+=1
for I in ([0,2],[1,3],[0,2,3],[1,2,4],[0,3],[0,1,3]):
    ds=dancers(I); N=len(ds)
    for r in range(N+1):
        L=ds[N-r:]; Fr_=ds[:r]; c=0
        for perm in itertools.permutations(Fr_):
            if all(golden(L[j],perm[j],I) for j in range(r)): c+=1
        tot+=1
        if c!=1: cnt_bad+=1
print("Theorem O (exactly one golden bijection): %d (I,r) cases, %d bad"%(tot,cnt_bad))
print("VIGIA-INNER-DONE")
