# find phrases in the pdf text (whitespace and hyphen-at-line-end normalized), by page; print context
import re,sys
t=open('scratch/v6_raw.txt').read()
pages=t.split('\f')
norm=[re.sub(r'\s+',' ',p) for p in pages]
for p in sys.argv[1:]:
    hits=[(i+1,m.start()) for i,pg in enumerate(norm) for m in re.finditer(re.escape(p),pg)]
    print('##',repr(p),[h[0] for h in hits])
    for pg,s in hits[:3]:
        print('   p%d: ...%s...'%(pg,norm[pg-1][max(0,s-150):s+250]))
