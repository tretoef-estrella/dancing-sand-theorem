# cold reader 8: recount the pooling cells and the integrality controls of §12, from the definitions of the paper only
from fractions import Fraction as Fr
def s2(x): return bin(x).count('1')
def kap(a,b): return s2(a)+s2(b)-s2(a+b)
def fam(l):
    x=l+1; k=x.bit_length()-1; I=[t for t in range(k) if x>>t&1]; return k,I
def gaps(I,k):
    nx=I[1:]+[k]; return {t:n-t for t,n in zip(I,nx)}
def dancers(I):  # subsets as bitmasks over positions, sorted by o_D
    ds=[]
    for mask in range(1<<len(I)):
        D=[I[j] for j in range(len(I)) if mask>>j&1]; ds.append(D)
    ds.sort(key=lambda D:sum(1<<t for t in D)); return ds
def pava(x):  # antitonic (non-increasing) least-squares fit; returns list of (sum, count) blocks
    bl=[]
    for v in x:
        bl.append([Fr(v),1])
        while len(bl)>1 and bl[-2][0]/bl[-2][1] < bl[-1][0]/bl[-1][1]:   # violation of non-increasing: pool
            s,c=bl.pop(); bl[-1][0]+=s; bl[-1][1]+=c
    # merge equal adjacent means (level sets)
    out=[]
    for s,c in bl:
        if out and out[-1][0]/out[-1][1]==s/c: out[-1][0]+=s; out[-1][1]+=c
        else: out.append([s,c])
    return out
def nonincreasing(x): return all(x[j]>=x[j+1] for j in range(len(x)-1))
def integral(bl): return all((s/c).denominator==1 for s,c in bl)
def R(E,h,alpha,mu): return sum(h[t]-alpha*(1<<t) for t in E)-kap(mu,sum(1<<t for t in E))
def clocks(l,i,alpha):
    k,I=fam(l); K=1<<k; h=gaps(I,k); ds=dancers(I)
    comp=lambda D:[t for t in I if t not in D]
    if i>=1:
        m=i-1; return [R(D,h,alpha,m)-R(comp(D),h,alpha,m+K) for D in ds]
    return [R(D,h,alpha,K-1)-R(comp(D),h,alpha,K-1) for D in ds[1:]]   # x# for D != ∅
def count_pool(L,imax,alphas,cond=lambda l,i:True):
    n=0; bad=0
    for l in range(1,L+1):
        for i in range(0,imax+1):
            if not cond(l,i): continue
            for a in alphas:
                x=clocks(l,i,a)
                if not x: continue
                if not integral(pava(x)): bad+=1
                if not nonincreasing(x): n+=1
    return n,bad
print('(a) λ<64,i≤12,α=1,2: pooling cells, non-integral:',count_pool(63,12,[1,2]))
print('(b) λ≤127,i≤30,α=1,2:',count_pool(127,30,[1,2]))
print('(c)   of which i≥1:',count_pool(127,30,[1,2],lambda l,i:i>=1))
print('(d) λ≤63,i≤8,α=1,2:',count_pool(63,8,[1,2]))
# (e) raw clocks u_i(D) = const + x_D, α=1, 1 added at the first dancer
n=tot=0
for l in range(1,256):
    k,I=fam(l)
    if not I: continue
    for i in range(1,41):
        x=clocks(l,i,1); x[0]+=1; tot+=1
        if not integral(pava(x)): n+=1
print('(e) non-integral with +1 at first dancer:',n,'of',tot)
# (f) houses
def house_x(I,k,ell,alpha):
    h=gaps(I,k); ds=dancers(I); comp=lambda D:[t for t in I if t not in D]
    return [R(D,h,alpha,ell)-R(comp(D),h,alpha,ell) for D in ds]
def houses(kmax):
    for k in range(1,kmax+1):
        for mask in range(1<<k):
            I=[t for t in range(k) if mask>>t&1]
            for ell in range(1<<k):
                for alpha in (1,2,3): yield I,k,ell,alpha
nf=tot=badh=0
for I,k,ell,alpha in houses(6):
    x=house_x(I,k,ell,alpha); tot+=1
    if not integral(pava(x)): badh+=1
    x[0]+=1
    if not integral(pava(x)): nf+=1
print('(f) houses k≤6: total',tot,' non-integral x_H:',badh,' non-integral with +1 at first dancer:',nf)
b7=t7=0
for I,k,ell,alpha in houses(7):
    t7+=1
    if not integral(pava(house_x(I,k,ell,alpha))): b7+=1
print('(g) houses k≤7: total',t7,' non-integral fits:',b7)
