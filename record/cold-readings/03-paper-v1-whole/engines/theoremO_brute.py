"""theoremO_brute.py — brute-force count of golden bijections L_r -> F_r (Theorem O), cold reader 2026-10-05.
Golden (bits): q = p, or q = p with a non-empty block of TOP bits, all equal to 1, cleared.
Also checks that this bit description equals the definition γ(a∖b) = 0 (b ⊆ a) for every I ⊆ [0,k), k <= 6.
CONTROLS: (c1) 'clear ANY run of consecutive ones' (not only a top block); (c2) 'any sub-dancer' (b ⊆ a).
Usage: python3 engines/theoremO_brute.py SMAX
"""
import sys
SMAX = int(sys.argv[1])

def golden_top(p, s):
    out = [p]
    j = s - 1
    q = p
    while j >= 0 and (p >> j) & 1:
        q &= ~(1 << j)
        out.append(q)
        j -= 1
    return out

def golden_anyrun(p, s):
    out = {p}
    for lo in range(s):
        for hi in range(lo, s):
            blk = sum(1 << j for j in range(lo, hi + 1))
            if p & blk == blk:
                out.add(p & ~blk)
    return sorted(out)

def golden_subset(p, s):
    out = []; b = p
    while True:
        out.append(b)
        if b == 0: break
        b = (b - 1) & p
    return out

def count(s, r, gen):
    N = 1 << s
    rows = list(range(N - r, N)); cols = set(range(r))
    opts = {p: [q for q in gen(p, s) if q in cols] for p in rows}
    rows.sort(key=lambda p: len(opts[p]))
    used = set(); cnt = 0
    def bt(idx):
        nonlocal cnt
        if cnt > 5: return
        if idx == len(rows): cnt += 1; return
        for q in opts[rows[idx]]:
            if q not in used:
                used.add(q); bt(idx + 1); used.discard(q)
    bt(0)
    return cnt

# 1. bit description == gamma definition
bad = 0; checked = 0
for k in range(0, 7):
    for mask in range(1 << k):
        I = [t for t in range(k) if (mask >> t) & 1]; s = len(I); N = 1 << s
        h = {t: ((I[j + 1] if j + 1 < s else k) - t) for j, t in enumerate(I)}
        def gamma(q):
            if q == 0: return 0
            mn = I[(q & -q).bit_length() - 1]
            return sum(h[I[j]] for j in range(s) if not (q >> j) & 1 and I[j] > mn)
        for a in range(N):
            gs = set(golden_top(a, s))
            b = a
            while True:
                checked += 1
                if (gamma(a & ~b) == 0) != (b in gs): bad += 1
                if b == 0: break
                b = (b - 1) & a
print(f"golden(bits) == golden(gamma=0): {checked} arrows, {bad} disagreements")
# 2. counts
res = {"top": [], "anyrun": [], "subset": []}
for s in range(0, SMAX + 1):
    for r in range(0, (1 << s) + 1):
        for name, gen in (("top", golden_top), ("anyrun", golden_anyrun), ("subset", golden_subset)):
            res[name].append((s, r, count(s, r, gen)))
for name in res:
    not1 = [(s, r, c) for s, r, c in res[name] if c != 1]
    print(f"{name}: {len(res[name])} (s,r) pairs, count != 1 in {len(not1)}; first few: {not1[:6]}")
