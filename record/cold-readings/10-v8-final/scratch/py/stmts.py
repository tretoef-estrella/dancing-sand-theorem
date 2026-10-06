# Extract numbered statements of the paper from each md version and compare them, normalized for typography only.
import re, sys, difflib
LAB = re.compile(r'^(?:> )?\*\*((?:Main Theorem|Theorem|Lemma|Proposition|Corollary)[^*]*?)\*\*')
def key(lab):
    m = re.match(r'(Main Theorem|Theorem DW|Theorem D|Theorem [0-9.]+|Lemma [0-9.]+|Proposition [0-9.]+|Corollary [0-9.]+)', lab)
    return m.group(1) if m else lab
def extract(path):
    L = open(path, encoding='utf-8').read().split('\n')
    out = {}; order = []
    i = 0
    while i < len(L):
        m = LAB.match(L[i])
        if not m: i += 1; continue
        k = key(m.group(1)); blk = [L[i]]; j = i + 1
        while j < len(L):
            s = L[j]
            if s.startswith('*Proof') or s.startswith('#') or LAB.match(s): break
            if s.strip() == '':
                n = j + 1
                while n < len(L) and L[n].strip() == '': n += 1
                if n < len(L) and (L[n].startswith('- ') or L[n].startswith('  ') or L[n].startswith('> ') or L[n].startswith('and ')):
                    j = n; continue
                break
            blk.append(s); j += 1
        if k in out: k = k + ' #2'
        out[k] = '\n'.join(blk); order.append(k); i = j
    return out, order
def norm(s):
    for a, b in [('ℤ','Z'),('ℚ','Q'),('𝔽','F'),('’',"'"),('⋯','…'),(' ',' '),(' ',' '),(' ',' '),('⁠','')]:
        s = s.replace(a, b)
    s = re.sub(r'^> ?', '', s, flags=re.M)
    s = s.replace('**', '').replace('`', '')
    return re.sub(r'\s+', ' ', s).strip()
def cmp(pa, pb, na, nb):
    A, oa = extract(pa); B, ob = extract(pb)
    print(f'===== {na} -> {nb}: {len(A)} statements in {na}, {len(B)} in {nb}')
    for k in oa:
        if k not in B: print(f'  ONLY IN {na}: {k}')
    for k in ob:
        if k not in A: print(f'  ONLY IN {nb}: {k}')
    nd = 0
    for k in ob:
        if k not in A: continue
        x, y = norm(A[k]), norm(B[k])
        if x == y: continue
        nd += 1
        xw, yw = x.split(' '), y.split(' ')
        print(f'  DIFF {k}:')
        for op, a1, a2, b1, b2 in difflib.SequenceMatcher(None, xw, yw, autojunk=False).get_opcodes():
            if op == 'equal': continue
            print(f'     {op}: «{" ".join(xw[max(0,a1-4):a2+2])}»  ->  «{" ".join(yw[max(0,b1-4):b2+2])}»')
    print(f'  statements whose normalized text differs: {nd}')
    return A, B
if __name__ == '__main__':
    V = {'v1':'material/evidence/versions/THE_DANCING_SAND_THEOREM_v1.md','v2':'material/evidence/versions/THE_DANCING_SAND_THEOREM_v2.md',
         'v3':'material/evidence/versions/THE_DANCING_SAND_THEOREM_v3.md','v4':'material/evidence/versions/THE_DANCING_SAND_THEOREM_v4.md',
         'v5':'material/evidence/versions/THE_DANCING_SAND_THEOREM_v5.md','v6':'material/evidence/versions/THE_DANCING_SAND_THEOREM_v6.md',
         'v7':'material/paper/THE_DANCING_SAND_THEOREM_v7.md','v8':'material/paper/THE_DANCING_SAND_THEOREM_v8.md'}
    if sys.argv[1:] == ['control']:
        # control: inject a change of hypothesis into a copy of v7 and a dropped (Cut) item; both must be reported
        t = open(V['v7'], encoding='utf-8').read()
        t2 = t.replace('(a) For an even payment system', '(a) For a payment system', 1).replace('- (Cut) `x_H` is cut', '- (Cot) `x_H` is cut', 1)
        assert t2 != t
        open('scratch/v7_control.md', 'w', encoding='utf-8').write(t2)
        cmp(V['v7'], 'scratch/v7_control.md', 'v7', 'v7ctl'); sys.exit()
    seq = ['v1','v2','v3','v4','v5','v6','v7','v8']
    for a, b in zip(seq, seq[1:]): cmp(V[a], V[b], a, b)
    cmp(V['v1'], V['v7'], 'v1', 'v7'); cmp(V['v3'], V['v7'], 'v3', 'v7')
    A, _ = extract(V['v7']); print('\n===== v7 Theorem 7.8 block as extracted:\n' + A['Theorem 7.8'])
