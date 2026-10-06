import re, sys, html
md = open(sys.argv[1], encoding='utf-8').read()
bb = open(sys.argv[2], encoding='utf-8').read()
words = [html.unescape(w) for w in re.findall(r'<word [^>]*>([^<]*)</word>', bb)]
names = re.findall(r'`([A-Za-z0-9_./]+(?:\.py|/))`', md)
from collections import Counter
cm = Counter(names)
bad = 0
for nme, c in sorted(cm.items()):
    cw = sum(1 for w in words if w.strip('.,;:()') == nme)
    flag = '' if cw >= c else '   <-- fewer whole words in the pdf than in the md'
    if flag: bad += 1
    print('%-24s md %d  pdf whole-word %d%s' % (nme, c, cw, flag))
print('code names:', len(cm), ' broken or missing:', bad)
print('FIN-OK')
