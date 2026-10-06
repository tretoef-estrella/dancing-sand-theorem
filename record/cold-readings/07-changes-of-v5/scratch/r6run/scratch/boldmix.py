import re,sys
t=open(sys.argv[1],encoding='utf-8').read().split('\n')
for i,l in enumerate(t,1):
    for m in re.finditer(r'\*\*(.+?)\*\*', l):
        s=m.group(1)
        if '`' in s:
            outside=re.sub(r'`[^`]*`','',s)
            words=[w for w in re.findall(r'[A-Za-z]+',outside)]
            if words:
                print(i, repr(s[:140]), '| text words in bold:', words[:8])
