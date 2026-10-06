# hunks_normalized.py — cold reader 5. For every hunk of DIFF_v2_to_v3.txt: are the removed and added texts
# the same after normalization? Normalization: drop the line structure, every whitespace character,
# the blockquote marker '>' at the start of a line, and a list bullet '- ' at the start of a line.
# Nothing else is removed (bold markers, backticks, punctuation, words and symbols are kept).
import re, difflib
L = open('material/paper/DIFF_v2_to_v3.txt', encoding='utf-8').read().split('\n')
hunks = []; cur = None
for line in L[2:]:
    if line.startswith('@@'):
        cur = {'head': line, 'old': [], 'new': []}; hunks.append(cur); continue
    if cur is None: continue
    if line.startswith('-'): cur['old'].append(line[1:])
    elif line.startswith('+'): cur['new'].append(line[1:])
def norm(lines):
    out = []
    for l in lines:
        l = re.sub(r'^\s*>\s?', '', l)
        l = re.sub(r'^\s*-\s', '', l)
        out.append(l)
    return re.sub(r'\s+', '', ''.join(out))
same = 0
for n, h in enumerate(hunks, 1):
    a, b = norm(h['old']), norm(h['new'])
    if a == b:
        same += 1; print(f'HUNK {n:2d} {h["head"]}: SAME after normalization'); continue
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    print(f'HUNK {n:2d} {h["head"]}: DIFFERS')
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op != 'equal':
            print(f'   {op}: OLD «{a[max(0,i1-25):i2+25]}»')
            print(f'   {"":{len(op)}}  NEW «{b[max(0,j1-25):j2+25]}»')
print(f'TOTAL {len(hunks)} hunks; {same} identical after normalization')
print('FIN-OK')
