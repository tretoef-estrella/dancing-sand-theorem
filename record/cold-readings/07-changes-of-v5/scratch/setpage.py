#!/usr/bin/env python3
"""setpage.py N 'text' — replace the line of page N in checks/PAGES.md (save as you go)."""
import sys,re
n=int(sys.argv[1]); txt=sys.argv[2]
p='checks/PAGES.md'; L=open(p,encoding='utf-8').read().split('\n')
for i,l in enumerate(L):
    if re.match(rf'^- p\. {n} — ',l): L[i]=f'- p. {n} — {txt}'; break
else: raise SystemExit('page line not found')
open(p,'w',encoding='utf-8').write('\n'.join(L))
