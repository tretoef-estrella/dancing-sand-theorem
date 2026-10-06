import sys
sys.argv=[sys.argv[0]]+sys.argv[1:]
exec(open('scratch/pdfcheck.py').read().split('def main():')[0])
s=open('scratch/v4_bbox.html',encoding='utf-8').read()
P=parse(s)
for pi,ws in enumerate(P,1):
    L=lines_of(ws)
    for k,ln in enumerate(L):
        if any(t.startswith(('reducibili','monotonici','lev')) and t.endswith(('‐','-')) for t in ln[5]):
            for j in range(max(0,k-1),min(len(L),k+3)):
                print(pi,j,round(L[j][0],1),L[j][5][:3],'...',L[j][5][-3:])
            print('--')
    if pi==11:
        print('p11 last bands:',[(round(l[0]),l[5][:4]) for l in L[-3:]])
