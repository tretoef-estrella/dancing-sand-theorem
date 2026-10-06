#!/usr/bin/env python3
"""refs.py — Grepy el lector frío del cubo 6, 2026-10-05. Own check of mission §2 item 9 / §3 item 9 (citations).
Keys listed (lines '- [KEY] ...' after '## References') against keys cited in the body (every bracket group,
split at commas, whose first word looks like a key). Also: alphabetical order (case-insensitive), and
every old key ([GMM19], [DEGJPP24]) must be gone. Control: a fake citation [Zzz99] appended to the body must
be reported as cited-but-not-listed.
"""
import re, sys
text = open(sys.argv[1], encoding='utf-8').read()
body, refs = text.split('\n## References\n')
if '--control' in sys.argv:
    body += '\nA fake citation [Zzz99, p. 3].\n'
listed = re.findall(r'^- \[([^\]]+)\]', refs, flags=re.M)
keypat = re.compile(r'^(?:[A-Za-z]{1,8}\d{2}|OEIS)$')
cited = {}
for g in re.findall(r'\[([^\[\]]+)\]', body):
    for part in g.split(','):
        w = part.strip().split(' ')[0]
        if keypat.match(w):
            cited[w] = cited.get(w, 0) + 1
print('listed', len(listed), 'cited', len(cited))
print('listed not cited:', [k for k in listed if k not in cited])
print('cited not listed:', [k for k in cited if k not in listed])
print('alphabetical:', listed == sorted(listed, key=str.lower))
for old in ('GMM19', 'DEGJPP24'):
    print(f'old key {old} occurrences in whole text:', text.count('[' + old))
for k in ('MGM19', 'DEGJPP23'):
    print(f'{k} cited {cited.get(k, 0)} times')
print('citation counts:', sorted(cited.items()))
