# Brute force for C14 (Theorem 4.4, the windows, and Theorem D), exact rationals.
# Every claim of C14 is tested on the dance of C13 (halved data, relabelling (s, j) -> 2s + j).
import itertools
from fractions import Fraction as Fr

cnt = {}; fails = []
ctrl = {}
def ok(name, c, info):
    cnt[name] = cnt.get(name, 0) + 1
    if not c: fails.append((name, info))
def fire(name, c):
    ctrl[name] = ctrl.get(name, 0) + (1 if c else 0)

def memo(fn):
    cache = {}
    def g(*a):
        if a not in cache: cache[a] = fn(*a)
        return cache[a]
    return g

def pT(p): return lambda s, f: -p(s, 2 * f) * p(s, 2 * f + 1)
def kT(p, k):
    def g(u, s1, f):
        mid = sum(k(s, s1, 2 * f + 1) * k(u, s, 2 * f) for s in range(s1 + 1, u))
        return -(p(s1, 2 * f + 1) * k(u, s1, 2 * f) + k(u, s1, 2 * f + 1) * p(u, 2 * f) + mid)
    return g
def split(p, k):
    dec = lambda t: (t // 2, t % 2)
    def p2(t, f):
        s, X = dec(t)
        return -p(s, 2 * f) * p(s, 2 * f + 1) if X == 0 else -p(s, 2 * f + 1) * p(s, 2 * f + 2)
    def k2(t2, t1, f):
        u, X2 = dec(t2); s1, X1 = dec(t1)
        if X1 == 0 and X2 == 0:
            if s1 < u:
                mid = sum(k(s, s1, 2 * f + 1) * k(u, s, 2 * f) for s in range(s1 + 1, u))
                return -(p(s1, 2 * f + 1) * k(u, s1, 2 * f) + k(u, s1, 2 * f + 1) * p(u, 2 * f) + mid)
            return 0
        if X1 == 1 and X2 == 1:
            if s1 < u:
                mid = sum(k(s, s1, 2 * f + 2) * k(u, s, 2 * f + 1) for s in range(s1 + 1, u))
                return -(p(s1, 2 * f + 2) * k(u, s1, 2 * f + 1) + k(u, s1, 2 * f + 2) * p(u, 2 * f + 1) + mid)
            return 0
        if X1 == 0 and X2 == 1:
            if u == s1: return -p(s1, 2 * f + 1)
            if s1 < u: return -k(u, s1, 2 * f + 1)
            return 0
        return 0
    return p2, k2

def dance(ds, p, k):
    r = 1
    for d in ds:
        if not d: p, k = memo(pT(p)), memo(kT(p, k))
        else:
            p, k = split(p, k); p, k = memo(p), memo(k); r *= 2
    return r, p, k

# ---- C15: Smith exponents (2-adic) of the final matrix, Theorem 7.10 ----
def v2(x):
    x = abs(x); v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def vq(q):  # 2-adic valuation of a nonzero Fraction
    return v2(q.numerator) - v2(q.denominator)
def s2(x): return bin(x).count("1")
def kap(a, b): return s2(a) + s2(b) - s2(a + b)
def oE(D): return sum(2 ** t for t in D)
def Iof(ds): return [t for t in range(len(ds)) if ds[t]]
def Dset(ds, s):
    I = Iof(ds); m = len(I)
    return frozenset(t for l, t in enumerate(I) if (s >> (m - 1 - l)) & 1)
def dancer(I, p):  # o-order: bit rank(t) of p
    return frozenset(t for l, t in enumerate(I) if (p >> l) & 1)
def smith_exps(Mat):
    A = [row[:] for row in Mat]; n = len(A); ex = []
    rows = list(range(n)); cols = list(range(n))
    while rows:
        best = None
        for r in rows:
            for c in cols:
                if A[r][c] != 0:
                    v = vq(A[r][c])
                    if best is None or v < best[0]: best = (v, r, c)
        if best is None:
            ex += [None] * len(rows); break
        v, r, c = best; ex.append(v)
        for r2 in rows:
            if r2 != r and A[r2][c] != 0:
                f = A[r2][c] / A[r][c]
                for c2 in cols: A[r2][c2] -= f * A[r][c2]
        for c2 in cols:
            if c2 != c and A[r][c2] != 0:
                f = A[r][c2] / A[r][c]
                for r2 in rows: A[r2][c2] -= f * A[r2][c]
        rows.remove(r); cols.remove(c)
    return ex
def pava_ifit(x):  # integer antitonic fit, non-increasing, as AntitonicFit.ifit
    blocks = []
    for v in x:
        blocks.append([Fr(v), 1])
        while len(blocks) > 1 and blocks[-2][0] / blocks[-2][1] <= blocks[-1][0] / blocks[-1][1]:
            S, p = blocks.pop(); blocks[-1][0] += S; blocks[-1][1] += p
    out = []
    for S, p in blocks:
        S = int(S); q, rho = divmod(S, p)
        out += [q + 1] * rho + [q] * (p - rho)
    return out
def hfun(I, k, t):
    return min([u for u in I + [k] if u > t]) - t
def ruler(I, k, al, mu, E):
    return sum(hfun(I, k, t) - al * 2 ** t for t in E) - kap(mu, oE(E))
def det_frac(Mt):
    A = [r[:] for r in Mt]; n = len(A); d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for c2 in range(c, n): A[r][c2] -= f * A[c][c2]
    return d
def dd_minors(Mt, r):
    n = len(Mt); best = None
    for R in itertools.combinations(range(n), r):
        for C in itertools.combinations(range(n), r):
            d = det_frac([[Mt[a][b] for b in C] for a in R])
            if d != 0:
                v = vq(d)
                if best is None or v < best: best = v
    return best

lists = [tuple(x) for n in range(1, 6) for x in itertools.product([False, True], repeat=n) if n + sum(x) <= 6]

# ---- C16: the cokernel over Z_2 and the raw clocks (Theorem 7.10 + Theorem D, per family) ----
import random
random.seed(16)
def phi(x): return x + v2(x)
def hD(I, k, D): return sum(hfun(I, k, t) for t in D)
def clock(I, k, i, D):
    lam1 = 2 ** k + oE(I); xi = lam1 - 2 * oE(D)
    return phi(xi) + kap(i + oE(D) - 1, xi) + hD(I, k, D)
INF = 10 ** 9
def big_from_matrix(ds, alpha, i):
    psig = lambda s, f, al=alpha, i=i: Fr(2) ** (al - 1) * (i + f)
    R, pk, kk = dance(ds, psig, lambda u, s, f: Fr(0))
    M = [[2 * pk(s, 0) if s == s1 else (2 * kk(s, s1, 0) if s1 < s else 0) for s1 in range(R)] for s in range(R)]
    k = len(ds)
    return sorted(INF if e is None else k + e for e in smith_exps(M))

# (L) coker of B with P B Q = diag(d), P, Q of odd determinant: 2-adic Smith exponents = v2(d_j)
def randodd(n):
    while True:
        P = [[Fr(random.randint(-3, 3)) for _ in range(n)] for _ in range(n)]
        d = det_frac(P)
        if d != 0 and d.numerator % 2 == 1: return P
def matmul(A, B): return [[sum(A[r][t] * B[t][c] for t in range(len(B))) for c in range(len(B[0]))] for r in range(len(A))]
def inv(A):
    n = len(A); M = [r[:] + [Fr(int(i == j)) for j in range(n)] for i, r in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0); M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]; M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [r[n:] for r in M]
for trial in range(300):
    n = random.randint(1, 4)
    d = [random.choice([0] + [(2 * random.randint(-3, 3) + 1) * 2 ** random.randint(0, 4) for _ in range(3)]) for _ in range(n)]
    P, Q = randodd(n), randodd(n)
    B = matmul(matmul(inv(P), [[Fr(d[r]) if r == c else Fr(0) for c in range(n)] for r in range(n)]), inv(Q))
    got = sorted(INF if e is None else e for e in smith_exps(B))
    want = sorted(INF if x == 0 else v2(x) for x in d)
    ok("L-coker-diagonal", got == want, (d,))
    c = 2 ** random.randint(0, 3)
    got2 = sorted(INF if e is None else e for e in smith_exps([[c * x for x in row] for row in B]))
    ok("L-scaled", got2 == sorted(INF if x == 0 else v2(c) + v2(x) for x in d), (d, c))
    fire("ctl-even-det-breaks", sorted(INF if e is None else e for e in smith_exps(matmul(B, [[Fr(2) if r == c2 == 0 else Fr(int(r == c2)) for c2 in range(n)] for r in range(n)]))) != want)

# (R0) ifit commutes with adding a constant
for trial in range(400):
    x = [random.randint(-6, 6) for _ in range(random.randint(1, 8))]; cc = random.randint(-5, 5)
    ok("R0-shift", pava_ifit([v + cc for v in x]) == [v + cc for v in pava_ifit(x)], (x, cc))

# (R1), (R2), (X) on every family of the list, alpha = 1 (and the C-form for alpha = 2, 3)
for ds in lists:
    k = len(ds); I = Iof(ds); m = len(I); N = 2 ** m; K = 2 ** k
    for i in range(4):
        if i >= 1:
            mu = i - 1
            for alpha in (1, 2, 3):
                x = [ruler(I, k, alpha, mu, dancer(I, j)) - ruler(I, k, alpha, mu + K, frozenset(I) - dancer(I, j)) for j in range(N)]
                y = pava_ifit(x); C = alpha * K + kap(mu, K)
                big = big_from_matrix(ds, alpha, i)
                ok("X1-exponents", big == sorted(k + C + y[p] for p in range(N)), (ds, alpha, i))
                ok("X1-positive", all(k + C + y[p] >= 1 for p in range(N)), (ds, alpha, i))
                if alpha == 1:
                    raw = [clock(I, k, i, dancer(I, p)) for p in range(N)]
                    pooled = pava_ifit(raw)
                    ok("R1-raw-clocks", all(pooled[p] == k + C + y[p] for p in range(N)), (ds, i, pooled, y))
                    ok("X-theorem-i>=1", big == sorted(pooled), (ds, i))
                    fire("ctl-unpooled-raw", big != sorted(raw))
                    fire("ctl-kappa-shift-wrong", pooled != pava_ifit([phi(2 ** k + oE(I) - 2 * oE(dancer(I, p))) + kap(i + oE(dancer(I, p)), 2 ** k + oE(I) - 2 * oE(dancer(I, p))) + hD(I, k, dancer(I, p)) for p in range(N)]))
        else:
            for alpha in (1, 2, 3):
                big = big_from_matrix(ds, alpha, 0)
                if m == 0:
                    ok("X3-I-empty", big == [INF], (ds, alpha)); continue
                xs = [ruler(I, k, alpha, K - 1, dancer(I, j + 1)) - ruler(I, k, alpha, K - 1, frozenset(I) - dancer(I, j + 1)) for j in range(N - 1)]
                ys = pava_ifit(xs)
                ok("X2-exponents", big == sorted([INF] + [k + alpha * K + ys[q] for q in range(N - 1)]), (ds, alpha))
                if alpha == 1:
                    raw = [clock(I, k, 0, dancer(I, q + 1)) for q in range(N - 1)]
                    pooled = pava_ifit(raw)
                    ok("R2-raw-clocks", all(pooled[q] == k + K + ys[q] for q in range(N - 1)), (ds, pooled, ys))
                    ok("X-theorem-i=0", big == sorted([INF] + pooled), (ds,))
                    fire("ctl-sharp-with-i1-clock", big != sorted([INF] + pava_ifit([clock(I, k, 1, dancer(I, q + 1)) for q in range(N - 1)])))

# The worked example of section 1.2 (n = 6)
def bigX(ds, i):
    k = len(ds); I = Iof(ds); N = 2 ** len(I)
    if i >= 1: return pava_ifit([clock(I, k, i, dancer(I, p)) for p in range(N)])
    return ["inf"] + pava_ifit([clock(I, k, 0, dancer(I, q + 1)) for q in range(N - 1)])
ok("example-n6-lambda6", bigX((True, True), 0) == ["inf", 6, 6, 3], bigX((True, True), 0))
ok("example-n6-lambda4", bigX((True, False), 1) == [6, 6], bigX((True, False), 1))
ok("example-n6-lambda2", bigX((True,), 2) == [5, 2], bigX((True,), 2))

print("COUNTS", cnt)
print("FAILURES", len(fails), fails[:10])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
