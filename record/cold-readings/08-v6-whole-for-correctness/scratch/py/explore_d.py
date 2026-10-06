# which range gives reader 3's «1 401 cells» and «274 cells where pooling acts»? cumulative counts per i, per α, λ from 0 or 1
import importlib.util,sys
spec=importlib.util.spec_from_file_location('pc','scratch/py/pooling_counts.py')
src=open('scratch/py/pooling_counts.py').read().split("print('(a)")[0]
exec(src)
for a in (1,2):
    row=[]
    for i in range(0,13):
        n=sum(1 for l in range(1,64) if (lambda x: x and not nonincreasing(x))(clocks(l,i,a)))
        row.append(n)
    print('α=%d pooling cells per i=0..12 (λ 1..63):'%a,row,' cumulative i≤8:',sum(row[:9]),' i≤10:',sum(row[:11]),' i≤12:',sum(row))
# dim T(λ) = 2^(k+|I|); cells with dim ≤ cap
for cap in (64,128,256,512):
    c=[l for l in range(1,64) if (1<<(fam(l)[0]+len(fam(l)[1])))<=cap]
    print('dim≤%d: %d families'%(cap,len(c)))
