#!/usr/bin/env python3
"""counts.py — re-count the cells and houses printed in §12 of v5 from their ranges.
Family lambda: lambda+1 = 2^k + sum_{t in I} 2^t. Cell = (lambda, i, alpha). House = (I, k, l, alpha), I ⊆ [0,k), 0<=l<2^k."""
def fam(lam):
    N=lam+1; k=N.bit_length()-1; I=[t for t in range(k) if N>>t&1]; return k,I
def cells(lmin,lmax,imax,alphas):
    out={'all':0,'i0':0,'i0_Ine':0,'i0_Ie':0,'ige1':0,'ige1_Ine':0}
    for lam in range(lmin,lmax+1):
        k,I=fam(lam)
        for i in range(0,imax+1):
            for a in alphas:
                out['all']+=1
                if i==0:
                    out['i0']+=1; out['i0_Ine' if I else 'i0_Ie']+=1
                else:
                    out['ige1']+=1
                    if I: out['ige1_Ine']+=1
    return out
def houses(kmax,amax,kmin=1,Ine=False):
    n=0
    for k in range(kmin,kmax+1):
        for Imask in range(1<<k):
            if Ine and Imask==0: continue
            n+= (1<<k)*amax
    return n
def deletions(kmax,amax):  # house l = 2^k-1 with I != empty
    return sum(((1<<k)-1)*amax for k in range(1,kmax+1))
for lmin in (1,0):
    print(f'--- families from lambda = {lmin}')
    s2=sum(2**len(fam(l)[1]) for l in range(lmin,64)); s3=sum(3**len(fam(l)[1]) for l in range(lmin,64))
    print('12.1 Props 5.2/5.3/5.4: entries', s3*40*2, ' clocks5.3', s2*40, ' clocks5.4', s2-(64-lmin))
    print('12.1 Thm 7.10 lambda<64,i<=12,a=1,2:', cells(lmin,63,12,(1,2))['all'])
    print('12.2 reader4/6 lambda<=127,i<=30,a=1,2:', cells(lmin,127,30,(1,2)))
    print('12.2 reader5/6 lambda<=255,i<=40,a=1:', cells(lmin,255,40,(1,)))
print('houses k<=6 a<=3:', houses(6,3), ' with I!=0:', houses(6,3,Ine=True), ' k<=7:', houses(7,3))
print('houses incl k=0, k<=6:', houses(6,3,kmin=0))
print('deletions k<=6:', deletions(6,3), ' k<=7:', deletions(7,3))
print('8001*24 =', 8001*24)
