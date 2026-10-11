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
for ds in lists:
    k = len(ds); I = Iof(ds); m = len(I); N = 2 ** m; K = 2 ** k
    # slot of the dancer p: bit reversal
    slot = {}
    for p in range(N):
        D = dancer(I, p)
        ss = [s for s in range(N) if Dset(ds, s) == D]
        ok("P1-bijection", len(ss) == 1, (ds, p)); slot[p] = ss[0]
    for alpha in (1, 2, 3):
        for i in range(4):
            psig = lambda s, f, al=alpha, i=i: Fr(2) ** (al - 1) * (i + f)
            ksig = lambda u, s, f: Fr(0)
            R, pk, kk = dance(ds, psig, ksig)
            M = [[2 * pk(s, 0) if s == s1 else (2 * kk(s, s1, 0) if s1 < s else 0) for s1 in range(R)] for s in range(R)]
            ok("integer", all(e.denominator == 1 for row in M for e in row), (ds, alpha, i))
            Mo = [[M[slot[p]][slot[q]] for q in range(N)] for p in range(N)]
            ex = sorted(smith_exps(M), key=lambda v: (v is None, v))
            exo = sorted(smith_exps(Mo), key=lambda v: (v is None, v))
            ok("P2-perm-invariance", ex == exo, (ds, alpha, i))
            if i >= 1:
                mu = i - 1
                x = [ruler(I, k, alpha, mu, dancer(I, j)) - ruler(I, k, alpha, mu + K, frozenset(I) - dancer(I, j)) for j in range(N)]
                y = pava_ifit(x)
                C = alpha * K + kap(mu, K)
                want = sorted(C + y[N - 1 - j] for j in range(N))
                ok("T1-exponents-i>=1", ex == want, (ds, alpha, i, ex, want))
                ok("T1-nonincreasing", all(y[j] >= y[j + 1] for j in range(N - 1)), (ds, alpha, i))
                ok("T1-det-nonzero", None not in ex, (ds, alpha, i))
                for r in range(N + 1):
                    ok("T1-dd-formula", sum(sorted(ex)[:r]) == r * C + sum(y[N - r:]), (ds, alpha, i, r))
                    if N <= 4 and r >= 1:
                        ok("T1-dd-by-minors", dd_minors(M, r) == r * C + sum(y[N - r:]), (ds, alpha, i, r))
                fire("ctl-kappa-i-not-i-1", ex != sorted(alpha * K + kap(i, K) + y[N - 1 - j] for j in range(N)))
                fire("ctl-natural-not-pooled", ex != sorted(C + x[j] for j in range(N)))
            else:
                ok("T2-det-zero", None in ex, (ds, alpha))
                if m >= 1:
                    xs = [ruler(I, k, alpha, K - 1, dancer(I, j + 1)) - ruler(I, k, alpha, K - 1, frozenset(I) - dancer(I, j + 1)) for j in range(N - 1)]
                    ys = pava_ifit(xs)
                    fin = sorted(v for v in ex if v is not None)
                    want = sorted(alpha * K + ys[j] for j in range(N - 1))
                    ok("T2-exponents-i=0", fin == want and ex.count(None) == 1, (ds, alpha, ex, want))
                    for r in range(N):
                        ok("T2-dd-formula", sum(fin[:r]) == r * alpha * K + sum(ys[N - 1 - r:]), (ds, alpha, r))
                        if N <= 4 and r >= 1:
                            ok("T2-dd-by-minors", dd_minors(M, r) == r * alpha * K + sum(ys[N - 1 - r:]), (ds, alpha, r))
                    fire("ctl-sharp-with-i=1-clocks", fin != sorted(alpha * K + kap(0, K) + v for v in pava_ifit([ruler(I, k, alpha, 0, dancer(I, j)) - ruler(I, k, alpha, K, frozenset(I) - dancer(I, j)) for j in range(N)])[:N - 1]))
                else:
                    ok("T2-I-empty-zero", all(e == 0 for row in M for e in row), (ds, alpha))
print("COUNTS", cnt)
print("FAILURES", len(fails), fails[:10])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
