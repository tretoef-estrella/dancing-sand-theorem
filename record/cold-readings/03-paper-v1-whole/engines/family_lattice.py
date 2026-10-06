"""family_lattice.py — family-level machine check (cold reader, 2026-10-05).

Builds the dance lattice T(lambda) from the definitions of §3.1/§3.3 ONLY (T(0) = A; T(2l+1) = Phi(T(l));
T(2l+2) = V ⊗ Phi(T(l)); F on Phi: F(b0 n) = b1 n, F(b1 n) = 2 b0 Fn; F on V⊗M by the coproduct; weights), and
computes coker(sigma^(alpha)_i = F + 2^alpha (D + i)) on T(lambda) with the exact 2-adic Smith engine smith2
(mod 2^64). Compares with Theorem D + Theorem 7.10:
   {0: rank/2} ∪ small clocks ∪ {k + alpha K + kappa(m,K) + yhat_D}   (i >= 1)
   {0: rank/2} ∪ small clocks ∪ {inf} ∪ {k + alpha K + yhat♯_D}         (i = 0)
For alpha = 1 the big part is the rule of §1.2 (engines/rule.py) — checked too.
Cells whose predicted largest exponent is >= 60 are SKIPPED (mod 2^64 too small) and COUNTED (no silent cap).
CONTROL: the prediction with raw (unpooled) clocks must be rejected wherever pooling acts.
Usage: python3 engines/family_lattice.py LMAX IMAX
"""
import sys
import numpy as np
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from smith2 import smith2, BIG
import rule
from rule import integer_antitonic_fit

LMAX, IMAX = int(sys.argv[1]), int(sys.argv[2])


def s2(x): return bin(x).count("1")
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)


def Phi(F, w):
    n = len(w)
    G = np.zeros((2 * n, 2 * n), dtype=np.int64)  # basis: b0 n_j (0..n-1), b1 n_j (n..2n-1); columns = images
    for j in range(n):
        G[n + j, j] = 1                    # F(b0 n_j) = b1 n_j
        G[:n, n + j] = 2 * F[:, j]         # F(b1 n_j) = 2 b0 F n_j
    return G, [2 * x + 1 for x in w] + [2 * x - 1 for x in w]


def Vtensor(F, w):
    n = len(w)
    G = np.zeros((2 * n, 2 * n), dtype=np.int64)  # basis b0⊗m_j, b1⊗m_j
    for j in range(n):
        G[n + j, j] += 1                   # F b0 = b1
        G[:n, j] += F[:, j]                # b0 ⊗ F m
        G[n:, n + j] += F[:, j]            # F(b1 ⊗ m) = b1 ⊗ F m
    return G, [x + 1 for x in w] + [x - 1 for x in w]


def T(lam):
    if lam == 0:
        return np.zeros((1, 1), dtype=np.int64), [0]
    if lam % 2 == 1:
        return Phi(*T((lam - 1) // 2))
    return Vtensor(*Phi(*T((lam - 2) // 2)))


def family(lam):
    N = lam + 1
    k = N.bit_length() - 1
    I = [t for t in range(k) if (N >> t) & 1]
    h = {t: ((I[j + 1] if j + 1 < len(I) else k) - t) for j, t in enumerate(I)}
    return k, I, h


stats = Counter()
for lam in range(1, LMAX + 1):
    F, w = T(lam)
    rank = len(w)
    k, I, h = family(lam)
    K = 1 << k; s = len(I); N = 1 << s
    assert rank == 1 << (k + s) and max(w) == lam and w.count(lam) == 1
    oD = [sum(1 << I[j] for j in range(s) if (p >> j) & 1) for p in range(N)]
    Dfloor = np.diag([(lam - x) // 2 for x in w]).astype(np.int64)
    small = Counter()
    for a in range(1, k):
        small[a] += 2 ** (s + k - 1 - a)
    for alpha in (1, 2):
        def Rmu(mu, E):
            return sum(h[I[j]] - alpha * (1 << I[j]) for j in range(s) if (E >> j) & 1) - kappa(mu, oD[E])

        def Rs(E):
            return sum(h[I[j]] - alpha * (1 << I[j]) for j in range(s) if (E >> j) & 1) - kappa(K - 1, oD[E])
        for i in range(0, IMAX + 1):
            pred = Counter({0: rank // 2}) + small
            raw = Counter(pred)
            if i >= 1:
                m = i - 1
                x = [Rmu(m, D) - Rmu(m + K, N - 1 - D) for D in range(N)]
                y = integer_antitonic_fit(x)
                for v in y: pred[k + alpha * K + kappa(m, K) + v] += 1
                for v in x: raw[k + alpha * K + kappa(m, K) + v] += 1
            else:
                xs = [Rs(D) - Rs(N - 1 - D) for D in range(1, N)]
                y = integer_antitonic_fit(xs) if xs else []
                pred[BIG] += 1; raw[BIG] += 1
                for v in y: pred[k + alpha * K + v] += 1
                for v in xs: raw[k + alpha * K + v] += 1
            mx = max(e for e in pred if e != BIG)
            if mx >= 60:
                stats["SKIPPED (predicted exponent >= 60)"] += 1
                continue
            sigma = F + (1 << alpha) * (Dfloor + i * np.eye(rank, dtype=np.int64))
            got = smith2(sigma, 64)
            stats["cells compared"] += 1
            if got != pred:
                stats["FAIL lattice Smith != prediction"] += 1
                if stats["FAIL lattice Smith != prediction"] <= 5:
                    print("MISMATCH", lam, i, alpha, dict(got), dict(pred))
            if alpha == 1:
                rg = Counter({0: rank // 2}) + rule.X(lam, i)
                if rg != pred:
                    stats["FAIL rule.X != Theorem D/7.10 prediction (alpha=1)"] += 1
            if raw != pred:
                stats["cells where pooling acts"] += 1
                if got == raw:
                    stats["CONTROL raw NOT rejected"] += 1
                else:
                    stats["CONTROL raw rejected"] += 1
print(f"lambda <= {LMAX}, 0 <= i <= {IMAX}, alpha in (1,2)")
for key in sorted(stats):
    print(f"  {key}: {stats[key]}")
print("TOTAL FAIL COUNT:", sum(v for kk, v in stats.items() if kk.startswith("FAIL")))
