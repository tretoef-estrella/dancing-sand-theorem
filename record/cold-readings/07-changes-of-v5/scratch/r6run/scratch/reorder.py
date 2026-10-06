import re
p = 'REPORT_COLD_6.md'
s = open(p, encoding='utf-8').read()
a = s.index('### Item 1 —'); b = s.index('## 2. The presentation edits')
block = s[a:b]
parts = re.split(r'(?=^### Item \d+ —)', block, flags=re.M)
parts = [x for x in parts if x.strip()]
def num(x): return int(re.match(r'### Item (\d+)', x).group(1))
parts.sort(key=num)
note = '### Item 2 — the presentation edits must not change content\n\nSee §2 below (the normalizing comparison).\n\n'
out = []
for x in parts:
    if num(x) == 3:
        out.append(note)
    out.append(x.rstrip('\n') + '\n\n')
s = s[:a] + ''.join(out) + s[b:]
open(p, 'w', encoding='utf-8').write(s)
print([num(x) for x in parts])
