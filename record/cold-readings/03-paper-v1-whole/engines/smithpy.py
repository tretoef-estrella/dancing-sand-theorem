"""smithpy.py — helpers copied verbatim from engines/cells_smith.py (qpoly of Theorem 4.4, exact Smith exponents
modulo 2^E with Python ints), importable without running that script. Cold reader, 2026-10-05."""
from collections import Counter
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


