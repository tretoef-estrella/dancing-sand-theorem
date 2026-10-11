# Grepy Cotejo: what rule (68) changes in v9: html of v9 built by md2html_v8.py vs md2html_v9.py, difference by tokens
import difflib, re, sys
a = open(sys.argv[1], encoding='utf-8').read(); b = open(sys.argv[2], encoding='utf-8').read()
ta = re.split(r'(<[^>]+>)', a); tb = re.split(r'(<[^>]+>)', b)
sm = difflib.SequenceMatcher(None, ta, tb, autojunk=False)
n = 0
for tag, i1, i2, j1, j2 in sm.get_opcodes():
    if tag == 'equal': continue
    n += 1
    old = re.sub(r'<[^>]+>', '', ''.join(ta[i1:i2])); new = ''.join(tb[j1:j2])
    print(f'{n}: v8-rule text «{old[:80]}» -> v9 «{new[:200]}»')
print('changes:', n)
