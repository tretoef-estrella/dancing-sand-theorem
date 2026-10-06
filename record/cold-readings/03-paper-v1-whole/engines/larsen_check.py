"""larsen_check.py — Larsen's fusion graph [Lar24, §2] against the recursion of §1.2 (rule.multiplicities).
x_{n,k} = multiplicity of T(2n) in V^{⊗2k} = weighted number of paths of length k from 0 to n, arrows:
n -> n+1 (label 1); n -> n+1-2^i (label 2) for 0 <= i <= r, 2^r || n+1; no arrows into 0 (CONTROL: allow them)."""
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import rule

def arrows(n, allow0=False):
    out = Counter({n + 1: 1})
    r = ((n + 1) & -(n + 1)).bit_length() - 1
    for i in range(0, r + 1):
        tgt = n + 1 - 2 ** i
        if tgt == 0 and not allow0:
            continue
        out[tgt] += 2
    return out

def larsen(K, allow0=False):
    cur = Counter({0: 1}); res = {0: dict(cur)}
    for k in range(1, K + 1):
        nxt = Counter()
        for n, c in cur.items():
            for t, lab in arrows(n, allow0).items():
                nxt[t] += c * lab
        cur = +nxt; res[k] = dict(cur)
    return res

L = larsen(32); Lc = larsen(32, allow0=True)
bad = 0; ctrl = 0
for k in range(1, 33):
    m = rule.multiplicities(2 * k)
    pred = {lam // 2: c for lam, c in m.items()}
    if L[k] != pred:
        bad += 1; print("MISMATCH 2k =", 2 * k)
    if Lc[k] != pred:
        ctrl += 1
print(f"Larsen vs recursion: even n = 2..64: {bad} mismatches; control (arrows into 0 allowed) differs at {ctrl}/32")
# character check: paper's ch T(lambda) vs Larsen (2.2) — identical products; check dimension sum = 2^n
ok = all(sum(c * 2 ** (rule.family(lam)[0] + len(rule.family(lam)[1])) for lam, c in rule.multiplicities(n).items()) == 2 ** n for n in range(1, 65))
print("sum m_lambda(n) dim T(lambda) == 2^n for n <= 64:", ok)
