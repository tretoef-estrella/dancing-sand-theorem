import sys, unicodedata, collections
t=open(sys.argv[1],encoding='utf-8').read()
c=collections.Counter()
for i,ch in enumerate(t):
    if 0x300<=ord(ch)<=0x36f and i>0:
        c[t[i-1]+ch]+=1
for k,v in c.most_common():
    print(repr(k), unicodedata.name(k[1]), 'on', unicodedata.name(k[0], k[0]), v)
