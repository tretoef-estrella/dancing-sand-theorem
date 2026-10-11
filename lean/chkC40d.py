#!/usr/bin/env python3
"""Brute force for Lean piece C40d (paper v8 §10.3, Proposition 10.7: the whole dance of a
system on T(l)). Grepy Escribano, 9 Oct 2026. Definitions copied from chkC40c.py (independent
lattice model, exact rationals, 2-adic Smith forms); payment systems with random data."""
import random
import sys
sys.path.insert(0, '.')
from fractions import Fraction
from math import comb
import chk_lattice_lib as L

random.seed(4004)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)

MMAX = 6
FLO = -6
FH = 24

def get(x, m, f): return x.get((m, f), Fraction(0))
def add(x, y): return {k: get(x, *k) + get(y, *k) for k in set(x) | set(y)}
def sub(x, y): return {k: get(x, *k) - get(y, *k) for k in set(x) | set(y)}
def smul(c, x): return {k: c * v for k, v in x.items()}
def mul(x, y):
    z = {}
    for m in range(MMAX):
        for f in range(FLO, FH):
            s = Fraction(0)
            for a in range(m + 1):
                s += comb(m, a) * get(x, a, f) * get(y, m - a, f - a)
            if s: z[(m, f)] = s
    return z
def fd(m): return {(m, f): Fraction(1) for f in range(FLO, FH)}
def dg(q): return {(0, f): Fraction(q(f)) for f in range(0, FH)}
def dfi(s):
    p = 1
    for k in range(1, 2 * s, 2): p *= k
    return Fraction(1, p)
def tw(x):
    t00, t11, t10, t01 = {}, {}, {}, {}
    for q in range(MMAX):
        for f in range(FLO, FH // 2):
            t00[(q, f)] = dfi(q) * get(x, 2 * q, 2 * f)
            t11[(q, f)] = dfi(q) * get(x, 2 * q, 2 * f + 1)
            t10[(q, f)] = dfi(q + 1) * get(x, 2 * q + 1, 2 * f + 1)
            if q + 1 < MMAX:
                t01[(q + 1, f)] = (2 * q + 2) * dfi(q + 1) * get(x, 2 * q + 1, 2 * f)
    return t00, t11, t10, t01
def vplus(x): return {(m, f): get(x, m, f + 1) for m in range(MMAX) for f in range(FLO, FH - 1)}
def vprime(x): return {(m, f): get(x, m + 1, f + 1) for m in range(MMAX - 1) for f in range(FLO, FH - 1)}
def rnd_op(lo=-3, hi=3, MM=None):
    MM = MMAX if MM is None else MM
    return {(m, f): Fraction(random.randint(lo, hi)) for m in range(MM) for f in range(FLO, FH)}

# ---------- lattices ----------
def mats(B, W, F):
    idx = {b: k for k, b in enumerate(B)}; n = len(B)
    Fm = [[Fraction(0)] * n for _ in range(n)]
    for b in B:
        for t, c in F[b].items(): Fm[idx[t]][idx[b]] += c
    return [W[b] for b in B], Fm, idx
def fdiv(Fm, bound):
    n = len(Fm); I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    pows = [I]; P = I; fact = 1
    for r in range(1, bound):
        P = L.matmul(P, Fm); fact *= r; pows.append([[c / fact for c in row] for row in P])
    return pows
class Lat:
    def __init__(self, B, W, F, top):
        self.B, self.Wd, self.Fd_ = B, W, F
        self.Wl, self.Fm, self.idx = mats(B, W, F)
        self.top = top; self.n = len(B)
        self.pows = fdiv(self.Fm, MMAX + 3)
def act(x, Lt, B=None):
    n = Lt.n; B = MMAX if B is None else B
    R = [[Fraction(0)] * n for _ in range(n)]
    for m in range(min(B, len(Lt.pows))):
        Pm = Lt.pows[m]
        for i in range(n):
            c = get(x, m, (Lt.top - Lt.Wl[i]) // 2)
            if c:
                for j in range(n):
                    if Pm[i][j]: R[i][j] += c * Pm[i][j]
    return R
def sysact(G, Lt, B=None):
    r = len(G); n = Lt.n
    M = [[Fraction(0)] * (r * n) for _ in range(r * n)]
    for s in range(r):
        for s2 in range(r):
            A = act(G[s][s2], Lt, B)
            for i in range(n):
                for j in range(n): M[s * n + i][s2 * n + j] = A[i][j]
    return M
def T(m): B, W, F = L.lat_T(m); return Lat(B, W, F, m)
def PhiT(m): B, W, F = L.lat_T(m); B2, W2, F2 = L.phi(B, W, F); return Lat(B2, W2, F2, 2 * m + 1)
def VPhiT(m):
    B, W, F = L.lat_T(m); B2, W2, F2 = L.tensV(*L.phi(B, W, F)); return Lat(B2, W2, F2, 2 * m + 2)
def eq(X, Y): return all(a == b for ra, rb in zip(X, Y) for a, b in zip(ra, rb))
def to_int(M):
    out = []
    for r in M:
        row = []
        for x in r:
            assert x.denominator == 1, "non-integral entry"
            row.append(int(x))
        out.append(row)
    return out
def smith(M, c=1):
    Mi = to_int([[c * x for x in r] for r in M]); n = len(Mi)
    return L.key(L.smith2(Mi, n, n))

# ---------- matrices of formal operators ----------
def mmul(X, Y):
    n, k, m = len(X), len(Y), len(Y[0])
    Z = [[{} for _ in range(m)] for _ in range(n)]
    for i in range(n):
        for j in range(m):
            acc = {}
            for t in range(k): acc = add(acc, mul(X[i][t], Y[t][j]))
            Z[i][j] = acc
    return Z
def msub(X, Y): return [[sub(a, b) for a, b in zip(ra, rb)] for ra, rb in zip(X, Y)]
def blocks(G):
    n = len(G); P = [[None] * n for _ in range(n)]; C = [[None] * n for _ in range(n)]
    Bb = [[None] * n for _ in range(n)]; D = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            t00, t11, t10, t01 = tw(G[i][j]); P[i][j], C[i][j], Bb[i][j], D[i][j] = t10, t11, t00, t01
    return P, C, Bb, D
def vsplit(G):
    n = len(G); H = [[{} for _ in range(2 * n)] for _ in range(2 * n)]
    for s in range(n):
        for s2 in range(n):
            H[2 * s][2 * s2] = G[s][s2]
            H[2 * s + 1][2 * s2] = vprime(G[s][s2])
            H[2 * s + 1][2 * s2 + 1] = vplus(G[s][s2])
    return H

# ---------- payment systems and C11/C12 data (as chkC40b) ----------
def paySys(p, kap, n):
    G = [[{} for _ in range(n)] for _ in range(n)]
    for s in range(n):
        for s2 in range(n):
            if s == s2: G[s][s2] = add(fd(1), dg(lambda f: 2 * p[s](f)))
            elif s2 < s: G[s][s2] = dg(lambda f, s=s, s2=s2: 2 * kap[s][s2](f))
    return G
def pT(p): return [(lambda f, s=s: -(p[s](2 * f) * p[s](2 * f + 1))) for s in range(len(p))]
def kT(p, k):
    n = len(p)
    return [[(lambda f, u=u, s2=s2: -(p[s2](2 * f + 1) * k[u][s2](2 * f) + k[u][s2](2 * f + 1) * p[u](2 * f)
             + sum(k[s][s2](2 * f + 1) * k[u][s](2 * f) for s in range(n) if s2 < s < u))) for s2 in range(n)] for u in range(n)]
def pSp(p):
    n = len(p); out = []
    for s in range(n):
        out.append(lambda f, s=s: -(p[s](2 * f) * p[s](2 * f + 1)))
        out.append(lambda f, s=s: -(p[s](2 * f + 1) * p[s](2 * f + 2)))
    return out
def kSp(p, k):
    n = len(p)
    def val(qp, q, f):
        u, X = divmod(qp, 2); s2, Y = divmod(q, 2)
        if Y == 0 and X == 0:
            if s2 < u:
                return -(p[s2](2 * f + 1) * k[u][s2](2 * f) + k[u][s2](2 * f + 1) * p[u](2 * f)
                         + sum(k[s][s2](2 * f + 1) * k[u][s](2 * f) for s in range(n) if s2 < s < u))
            return 0
        if Y == 1 and X == 1:
            if s2 < u:
                return -(p[s2](2 * f + 2) * k[u][s2](2 * f + 1) + k[u][s2](2 * f + 2) * p[u](2 * f + 1)
                         + sum(k[s][s2](2 * f + 2) * k[u][s](2 * f + 1) for s in range(n) if s2 < s < u))
            return 0
        if Y == 0 and X == 1:
            if u == s2: return -p[s2](2 * f + 1)
            if s2 < u: return -k[u][s2](2 * f + 1)
            return 0
        return 0
    return [[(lambda f, qp=qp, q=q: val(qp, q, f)) for q in range(2 * n)] for qp in range(2 * n)]
def rnd_data(n, lo=-5, hi=5):
    tabp = [[random.randint(lo, hi) for _ in range(200)] for _ in range(n)]
    tabk = [[[random.randint(lo, hi) for _ in range(200)] for _ in range(n)] for _ in range(n)]
    p = [(lambda f, s=s: tabp[s][f]) for s in range(n)]
    k = [[(lambda f, u=u, s=s: tabk[u][s][f]) for s in range(n)] for u in range(n)]
    return p, k

# ======================= C40d: Proposition 10.7 (the whole dance on T(l)) =======================
def digits(l):
    out = []
    while l > 0:
        if l % 2 == 1: out.append(False); l = (l - 1) // 2
        else: out.append(True); l = (l - 2) // 2
    return out
def dance_data(l, p, k):
    """the data dance along ds l; returns (k_len, m, clocks list of (valuation offset a, count), final p, k, n)"""
    n = len(p); clocks = []; a = 0; cur = l
    for dg_ in digits(l):
        nxt = (cur - 1) // 2 if not dg_ else (cur - 2) // 2
        dimN = T(nxt).n
        if not dg_:
            clocks.append((a, n * dimN)); p, k = pT(p), kT(p, k)
        else:
            clocks.append((a, 2 * n * dimN)); p, k = pSp(p), kSp(p, k); n = 2 * n
        a += 1; cur = nxt
    return clocks, p, k, n
def finalM(p, k, n):
    return [[Fraction(2 * p[s](0)) if s == s2 else (Fraction(2 * k[s][s2](0)) if s2 < s else Fraction(0))
             for s2 in range(n)] for s in range(n)]
def predicted(l, r, p, k, h):
    clocks, pf, kf, nf = dance_data(l, p, k)
    K = len(digits(l))
    lst = []
    for a, cnt in clocks:
        if h + a > 0: lst += [h + a] * cnt
    return L.key(lst + smith(finalM(pf, kf, nf), 2 ** (h + K))), clocks, pf, kf, nf

# (Q0) dim T(l) = 2^{len(ds l) + mCount(ds l)}
for l in range(0, 16):
    ds_ = digits(l)
    ok(T(l).n == 2 ** (len(ds_) + sum(ds_)), ("Q0", l))

# (Q1) Proposition 10.7, scaled, payment systems with random data; (Q2) the flat count
for l in range(0, 8):
    Tl = T(l)
    ds_ = digits(l); K = len(ds_); m = sum(ds_)
    for r in (1, 2, 3):
        if r * Tl.n > 48: continue
        for trial in range(2):
            p, k = rnd_data(r)
            G = paySys(p, k, r)
            S = sysact(G, Tl, l + 1)
            for h in range(0, 3):
                pred, clocks, pf, kf, nf = predicted(l, r, p, k, h)
                ok(smith(S, 2 ** h) == pred, ("Q1", l, r, h, trial))
            ok(nf == r * 2 ** m, ("slots", l, r))
            ok(clocks == [(a, r * 2 ** (K + m - 1 - a)) for a in range(K)], ("Q2 flat", l, r))

# (Q4) σ^{(α)}_i: p = 2^{α−1}(i + f), κ = 0
for l in range(0, 8):
    Tl = T(l)
    for alpha in (1, 2, 3):
        for i in (0, 1, 2, 5):
            p = [(lambda f, alpha=alpha, i=i: 2 ** (alpha - 1) * (i + f))]
            k = [[(lambda f: 0)]]
            G = paySys(p, k, 1)
            for h in (0, 1):
                pred, _, _, _, _ = predicted(l, 1, p, k, h)
                ok(smith(sysact(G, Tl, l + 1), 2 ** h) == pred, ("Q4 sigma", l, alpha, i, h))

# (Q3) associated final matrices give isomorphic cokernels: u·G for odd u; and random pairs of size 1
for l in range(0, 7):
    Tl = T(l)
    for r in (1, 2):
        if r * Tl.n > 32: continue
        p, k = rnd_data(r); u = random.choice([3, -1, 5, -7])
        G = paySys(p, k, r); Gu = [[smul(Fraction(u), x) for x in row] for row in G]
        ok(smith(sysact(G, Tl, l + 1)) == smith(sysact(Gu, Tl, l + 1)), ("Q3 unit", l, r))
    seen = {}
    for trial in range(12):
        p, k = rnd_data(1, -8, 8)
        _, pf, kf, nf = dance_data(l, p, k)
        key_final = tuple(smith(finalM(pf, kf, nf), 2 ** len(digits(l))))
        co = tuple(smith(sysact(paySys(p, k, 1), Tl, l + 1)))
        if key_final in seen: ok(seen[key_final] == co, ("Q3 pairs", l))
        else: seen[key_final] = co
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0
# 1. the clocks without the shift a (every clock at 2^h)
l = 5; Tl = T(l); p, k = rnd_data(1); G = paySys(p, k, 1)
clocks, pf, kf, nf = dance_data(l, p, k)
bad = L.key([1] * sum(c for _, c in clocks) + smith(finalM(pf, kf, nf), 2 ** (1 + len(digits(l)))))
if smith(sysact(G, Tl, l + 1), 2) != bad: fired += 1
# 2. the final matrix scaled by 2^{h+k−1} instead of 2^{h+k}
bad = L.key([1 + a for a, c in clocks for _ in range(c)] + smith(finalM(pf, kf, nf), 2 ** len(digits(l))))
if smith(sysact(G, Tl, l + 1), 2) != bad: fired += 1
# 3. the split move counted with r instead of 2r slots (h = 1, so the clock at a = 0 counts)
l = 4; Tl = T(l); clocks, pf, kf, nf = dance_data(l, p, k)
bad = L.key([1 + a for a, c in clocks for _ in range(c // 2 if a == 0 else c)] + smith(finalM(pf, kf, nf), 2 ** (1 + len(digits(l)))))
if len(smith(sysact(paySys(p, k, 1), Tl, l + 1), 2)) != len(bad) or smith(sysact(paySys(p, k, 1), Tl, l + 1), 2) != bad: fired += 1
# 4. each clock counted with the lattice of the move (T(l_j)) instead of the next lattice (T(l_{j+1}))
l = 6; Tl = T(l); p2, k2 = rnd_data(1)
clocks, pf, kf, nf = dance_data(l, p2, k2)
cur = l; badc = []; n = 1
for a, dg_ in enumerate(digits(l)):
    badc += [1 + a] * ((1 if not dg_ else 2) * n * T(cur).n)
    if dg_: n *= 2
    cur = (cur - 1) // 2 if not dg_ else (cur - 2) // 2
bad = L.key(badc + smith(finalM(pf, kf, nf), 2 ** (1 + len(digits(l)))))
if smith(sysact(paySys(p2, k2, 1), Tl, l + 1), 2) != bad: fired += 1
# 5. (Q0) with 2^{len} instead of 2^{len+m}
if any(T(l).n != 2 ** len(digits(l)) for l in range(0, 8)): fired += 1
print("controls fired", fired, "of 5")
