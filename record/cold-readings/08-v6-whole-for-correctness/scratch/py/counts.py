# recount the pure counts of §12 (cells, houses, clocks, entries) by enumeration
def fam(l):
    x=l+1; k=x.bit_length()-1; I=[t for t in range(k) if x>>t&1]; return k,I
def cells(L,imax,alphas,cond):
    return sum(1 for l in range(1,L+1) for i in range(0,imax+1) for a in alphas if cond(l,i))
# reader 4 / 6: λ ≤ 127, i ≤ 30, α=1,2
print('7874?',cells(127,30,[1,2],lambda l,i:True))
print('i=0:',cells(127,30,[1,2],lambda l,i:i==0),' i=0,I!=∅:',cells(127,30,[1,2],lambda l,i:i==0 and fam(l)[1]),' i=0,I=∅:',cells(127,30,[1,2],lambda l,i:i==0 and not fam(l)[1]),' i>=1:',cells(127,30,[1,2],lambda l,i:i>=1))
print('7634?',cells(127,30,[1,2],lambda l,i:not(i==0 and fam(l)[1])))
# reader 5: λ ≤ 255, i ≤ 40, α=1
print('10455?',cells(255,40,[1],lambda l,i:True),' i>=1:',cells(255,40,[1],lambda l,i:i>=1),' I!=∅,i>=1:',cells(255,40,[1],lambda l,i:i>=1 and fam(l)[1]))
# houses
def houses(kmax,amax,needI=False):
    return sum((2**k-1 if needI else 2**k)*2**k*amax for k in range(1,kmax+1))
print('16380?',houses(6,3),' 16002?',houses(6,3,True),' x3=',3*houses(6,3,True),' 65532?',houses(7,3))
# §12.1 Props 5.2-5.4 row: λ<64, i=1..40
cl=sum(2**len(fam(l)[1]) for l in range(1,64)); ent=sum(3**len(fam(l)[1]) for l in range(1,64))
print('14560?',cl*40,' 301?',cl-63,' 109200?',ent*40*2)
print('1638?',cells(63,12,[1,2],lambda l,i:True))
