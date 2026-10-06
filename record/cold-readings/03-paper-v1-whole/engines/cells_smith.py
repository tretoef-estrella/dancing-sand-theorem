"""cells_smith.py — matrix-level machine check of §4–§7 (cold reader, 2026-10-05). Exact integers only.

For each cell (lambda, i, alpha):
  1. builds M = M^{(alpha)}(lambda, i) from the closed form of Theorem 4.4 (q_k in Z[y]/(y^2), windows of pi_0);
  2. checks the deficit law (Lemma 4.5) for every a_k(Delta);
  3. checks v_2 of EVERY support entry against the cost form (Prop. 5.2 for i >= 1, Prop. 5.4 for i = 0, D != ∅);
  4. computes the Smith exponents of M exactly (elimination modulo 2^E, E above v_2 of the relevant minor), and
     compares with Theorem 7.10: alpha*K + kappa(m,K) + yhat_D (i >= 1); {inf} ∪ {alpha*K + yhat♯_D} (i = 0).
  CONTROL: the same comparison with the RAW clocks (no pooling) must fail in every cell where pooling acts.
Usage: python3 engines/cells_smith.py LMAX IMAX
"""
import sys
from collections import Counter
from fractions import Fraction
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from rule import integer_antitonic_fit

LMAX, IMAX = int(sys.argv[1]), int(sys.argv[2])
INF = 10**9


def s2(x): return bin(x).count("1")
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)


def v2(x):
    if x == 0:
        return INF
    x = abs(x)
    return (x & -x).bit_length() - 1


def family(lam):
    N = lam + 1
    k = N.bit_length() - 1
    I = [t for t in range(k) if (N >> t) & 1]
    h = {t: ((I[j + 1] if j + 1 < len(I) else k) - t) for j, t in enumerate(I)}
    return k, I, h


def qpoly(k, I):
    """q_k as dict {mask over positions of I: coeff}; y_j <-> I[j]."""
    pos = {t: j for j, t in enumerate(I)}
    q = {0: -1}
    for t in range(k):
        sq = Counter()
        for a, ca in q.items():
            for b, cb in q.items():
                if a & b == 0:
                    sq[a | b] += ca * cb
        if t in pos:
            bit = 1 << pos[t]
            for a, ca in q.items():
                if not a & bit:
                    sq[a | bit] -= ca
        q = {m: c for m, c in sq.items() if c}
    return q


def smith_exps(rows, E):
    """exact Smith exponents of an integer matrix (list of rows), modulo 2^E; returns sorted list (INF if >= E)."""
    MOD = 1 << E
    A = [[x % MOD for x in r] for r in rows]
    R = len(A); C = len(A[0]) if R else 0
    rr = list(range(R)); cc = list(range(C))
    out = []
    while rr and cc:
        best = None
        for r in rr:
            for c in cc:
                x = A[r][c]
                if x:
                    v = (x & -x).bit_length() - 1
                    if best is None or v < best[0]:
                        best = (v, r, c)
                        if v == 0:
                            break
            if best and best[0] == 0:
                break
        if best is None:
            out += [INF] * min(len(rr), len(cc))
            break
        v, p, q = best
        u = A[p][q] >> v
        inv = pow(u, -1, MOD)
        rowp = A[p]
        for r in rr:
            if r != p and A[r][q]:
                f = ((A[r][q] >> v) * inv) % MOD
                Ar = A[r]
                for c in cc:
                    if rowp[c]:
                        Ar[c] = (Ar[c] - f * rowp[c]) % MOD
        out.append(v)
        rr.remove(p); cc.remove(q)
    return sorted(out)


stats = Counter()
cells = 0
for lam in range(1, LMAX + 1):
    k, I, h = family(lam)
    K = 1 << k
    s = len(I); N = 1 << s
    oD = [sum(1 << I[j] for j in range(s) if (p >> j) & 1) for p in range(N)]
    q = qpoly(k, I)
    # deficit law
    for D in range(N):
        a = q.get(D, 0)
        if D == 0:
            if a != 1:
                stats["FAIL a_k(∅) != 1"] += 1
        else:
            Ds = [I[j] for j in range(s) if (D >> j) & 1]
            if v2(a) != k - len(Ds) - min(Ds):
                stats["FAIL deficit law"] += 1
    stats["deficit-law coefficients checked"] += N

    def gamma(qm):
        if qm == 0:
            return 0
        jmin = (qm & -qm).bit_length() - 1
        mn = I[jmin]
        return sum(h[I[j]] for j in range(s) if not (qm >> j) & 1 and I[j] > mn)

    for alpha in (1, 2):
        def Rmu(mu, E):
            return sum(h[I[j]] - alpha * (1 << I[j]) for j in range(s) if (E >> j) & 1) - kappa(mu, oD[E])

        def Rsharp(E):
            return sum(h[I[j]] - alpha * (1 << I[j]) for j in range(s) if (E >> j) & 1) - kappa(K - 1, oD[E])

        for i in range(0, IMAX + 1):
            cells += 1
            # build M exactly
            M = [[0] * N for _ in range(N)]
            for D in range(N):
                for Dp in range(N):
                    if Dp & ~D:
                        continue
                    Delta = D & ~Dp
                    a = q.get(Delta, 0)
                    prod = 1
                    for d in range(oD[D], oD[Dp] + K):
                        prod *= (1 << alpha) * (i + d)
                    val = Fraction(-a * prod) * Fraction(2) ** (1 - K + oD[Delta])
                    assert val.denominator == 1, (lam, i, alpha, D, Dp)
                    M[D][Dp] = int(val)
            # cost form check
            for D in range(N):
                for Dp in range(N):
                    if Dp & ~D:
                        continue
                    if i >= 1:
                        m = i - 1
                        pred = alpha * K + kappa(m, K) + Rmu(m, D) - Rmu(m + K, Dp) + gamma(D & ~Dp)
                    else:
                        if D == 0:
                            pred = INF
                        else:
                            pred = alpha * K + Rsharp(D) - Rsharp(Dp) + gamma(D & ~Dp)
                    if v2(M[D][Dp]) != pred:
                        stats["FAIL cost form"] += 1
                    stats["entries checked"] += 1
            # predicted Smith exponents
            if i >= 1:
                m = i - 1
                x = [Rmu(m, D) - Rmu(m + K, N - 1 - D) for D in range(N)]
                y = integer_antitonic_fit(x)
                base = alpha * K + kappa(m, K)
                pred = sorted(base + v for v in y)
                raw = sorted(base + v for v in x)
                rows = M
                Ebits = sum(v2(M[D][D]) for D in range(N)) + 2
            else:
                xs = [Rsharp(D) - Rsharp(N - 1 - D) for D in range(1, N)]
                y = integer_antitonic_fit(xs) if xs else []
                pred = sorted(alpha * K + v for v in y)
                raw = sorted(alpha * K + v for v in xs)
                rows = M[1:]
                Ebits = sum(v2(M[D][D]) for D in range(1, N)) + 2
            if rows:
                got = smith_exps(rows, Ebits)
            else:
                got = []
            if got != pred:
                stats["FAIL Smith(M) != Theorem 7.10 prediction"] += 1
                if stats["FAIL Smith(M) != Theorem 7.10 prediction"] <= 5:
                    print("MISMATCH", lam, i, alpha, got, pred)
            if raw != pred:
                stats["cells where pooling acts"] += 1
                if got != raw:
                    stats["CONTROL raw clocks rejected"] += 1
                else:
                    stats["CONTROL raw clocks NOT rejected"] += 1
print(f"cells checked: {cells} (lambda <= {LMAX}, 0 <= i <= {IMAX}, alpha in (1,2))")
for key in sorted(stats):
    print(f"  {key}: {stats[key]}")
print("TOTAL FAIL COUNT:", sum(v for kk, v in stats.items() if kk.startswith("FAIL")))
