# M5: the numbered statements of §2–§10 of the paper v8, against the «Paper v8» column of the certificate §3 table.
import re
paper = open('material/paper/THE_DANCING_SAND_THEOREM_v8.md').read().split('\n')
stmts = []
for i, l in enumerate(paper, 1):
    for m in re.finditer(r'\*\*(Lemma|Proposition|Theorem|Corollary) (\d+)\.(\d+)', l):
        sec = int(m.group(2))
        if 2 <= sec <= 10: stmts.append((m.group(1), f'{m.group(2)}.{m.group(3)}', i))
print('numbered statements in §2–§10:', len(stmts))
cert = open('material/certificate/LEAN_CERTIFICATE_DANCING_SAND_v1.md').read()
tab = cert.split('| Piece | Paper v8 | Lean folder | Main Lean results |')[1].split('\n\n')[0]
cited = {}
for row in tab.splitlines():
    cells = [c.strip() for c in row.split('|')]
    if len(cells) < 4 or not cells[1].startswith('C'): continue
    piece, col = cells[1], cells[2]
    nums = set()
    for a, b, c in re.findall(r'(\d+)\.(\d+)(?:[–-](?:\d+\.)?(\d+))?', col):
        lo = int(b); hi = int(c) if c else lo
        for x in range(lo, hi + 1): nums.add(f'{a}.{x}')
    for n in nums: cited.setdefault(n, []).append(piece)
missing = [s for s in stmts if s[1] not in cited]
print('statements not named in the «Paper v8» column:', missing)
print('names in the column that are not numbered statements of §2–§10:', sorted(set(cited) - {s[1] for s in stmts}, key=lambda x: tuple(map(int, x.split('.')))))
for s in stmts: print(f'  {s[0]:12s} {s[1]:6s} line {s[2]:5d}  pieces: {cited.get(s[1])}')
