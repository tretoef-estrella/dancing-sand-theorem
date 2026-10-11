# Grepy Cotejo: my own parser of the 68 brute-force logs against Table 6a of the certificate (no make_tables.py)
import re, sys, os, ast
bf, cert = sys.argv[1], sys.argv[2]
txt = open(cert, encoding='utf-8').read()
rows = re.findall(r'^\| (C\d+[a-h]?) \| `[0-9a-f]{8}` \|[^|]*\|[^|]*\|[^|]*\| (.*) \|$', txt, re.M)
print('Table 6a rows:', len(rows))
def num(s): return int(re.sub(r'[^0-9]', '', s))
bad = 0
for p, cell in rows:
    m = re.match(r'([0-9][0-9\s\u00a0\u202f\u2009]*) checks(?: in (\d+) kinds?)?, (\d+) failures; controls (\d+)/(\d+)', cell)
    if not m: print("UNPARSED", p, repr(cell)); continue
    tc, tk, tf, ca, cb = num(m.group(1)), (int(m.group(2)) if m.group(2) else None), int(m.group(3)), int(m.group(4)), int(m.group(5))
    L = open(os.path.join(bf, f'chk{p}.log'), encoding='utf-8').read()
    lines = L.split('\n')
    # 1. an explicit total
    tot = None; how = ''
    for pat in [r'^chk\w+: (\d+) checks, (\d+) failures', r'^(?:cells \d+ )?checks:? (\d+),? fail', r'^CHECKS (\d+) FAILURES', r'^TOTAL (\d+) FAILURES']:
        mm = re.search(pat, L, re.M)
        if mm: tot = int(mm.group(1)); how = 'total'; break
    kinds = None; ksum = None
    mm = re.search(r'^COUNTS (\{.*\})$', L, re.M)
    if mm:
        d = ast.literal_eval(mm.group(1)); ksum = sum(d.values()); kinds = len(d)
    else:
        ch = re.findall(r'^checked (.+): (\d+)$', L, re.M)
        if ch: ksum = sum(int(v) for _, v in ch); kinds = len(ch)
        else:
            c4 = re.findall(r'^([A-Z]): (\d+) ', L, re.M)
            if c4: ksum = sum(int(v) for _, v in c4); kinds = len(c4)
    if tot is None:
        mine = (ksum, kinds); how = 'by kind'
    else:
        mine = (tot, None)
        if ksum is not None and ksum != tot: print(f'  NOTE {p}: total {tot} but kinds sum {ksum}')
    # failures
    fails = re.findall(r'(?i)fail(?:ures|s)?:? (\d+)', L) + re.findall(r'(?i), (\d+) failures', L)
    fl = set(int(x) for x in fails)
    # controls
    cfa = cfb = None
    for pat in [r'controls:? (\d+)/(\d+) fire', r'controls fired (\d+) (?:of|/) (\d+)']:
        mm = re.search(pat, L, re.I)
        if mm: cfa, cfb = int(mm.group(1)), int(mm.group(2)); break
    if cfa is None:
        mm = re.search(r'CONTROLS (\{.*\})', L) or re.search(r'^controls[^{\n]*: (\{.*\})', L, re.M) or re.search(r'^controls (\{.*\})', L, re.M)
        if mm:
            d = ast.literal_eval(mm.group(1)); cfb = len(d); cfa = sum(1 for v in d.values() if v)
        else:
            i = [k for k, l in enumerate(lines) if l.startswith('controls (')]
            if i:
                block = []
                for l in lines[i[0]+1:]:
                    if l.startswith('  '): block.append(l)
                    else: break
                cfb = len(block); cfa = sum(1 for l in block if int(l.rsplit(':', 1)[1]) > 0)
    ok = (mine[0] == tc and mine[1] == tk and fl == {0} and (cfa, cfb) == (ca, cb))
    if not ok: bad += 1
    print(f"{'OK ' if ok else 'BAD'} {p:5} table: {tc} checks{' in '+str(tk)+' kinds' if tk else ''}, {tf} failures, controls {ca}/{cb} | "
          f"log ({how}): {mine[0]}{' in '+str(mine[1])+' kinds' if mine[1] else ''}, failures {sorted(fl)}, controls {cfa}/{cfb}")
print('rows that disagree:', bad)
