#!/usr/bin/env python3
"""Brute force for Lean piece C40c (paper v8 §10.3, the proof of Proposition 10.7, one step):
the action of a system on a DP-lattice, the twist map and the V-split on systems, and one move of
the dance as a Schur step on cokernels. Grepy Escribano, 9 Oct 2026.
Independent lattice model (chk_lattice_lib: T(l), Φ, V ⊗ −, F^(r) = F^r / r! over Q), exact
rationals; formal operators as tables (m, f) ↦ x_m(f) (coefficient at the TARGET floor);
payment systems with random integer data (C11/C12 data as in chkC40b); 2-adic Smith forms."""
import random
import sys
sys.path.insert(0, '.')
from fractions import Fraction
from math import comb
import chk_lattice_lib as L

random.seed(4003)
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

# ---------- (N1), (N2) the dance lattices: (top l) and (nil (l+1)); nil of Φ ----------
for l in range(0, 13):
    Lt = T(l)
    ok(all(w <= l and (l - w) % 2 == 0 for w in Lt.Wl), ("N2 top", l))
    pw = fdiv(Lt.Fm, l + 4)
    ok(all(not any(row) for s in range(l + 1, l + 4) for row in pw[s]), ("N2 nil", l))
for l in range(0, 7):
    Lt = T(l); pw = fdiv(Lt.Fm, l + 3)
    BN = next(s for s in range(l + 3) if all(not any(row) for row in pw[s]))
    Bp, Wp, Fp = L.phi(*L.lat_T(l)); P = Lat(Bp, Wp, Fp, 2 * l + 1); pp = fdiv(P.Fm, 2 * BN + 3)
    ok(all(not any(row) for s in range(2 * BN, 2 * BN + 3) for row in pp[s]), ("N1", l))

# ---------- (A1) agreement, (A2) ring map, (A4) the last level ----------
def junk(x):
    y = dict(x)
    for m in range(MMAX):
        for f in range(FLO, m): y[(m, f)] = Fraction(random.randint(-9, 9))
    return y
for m in range(0, 4):
    Lt = T(m)
    for r in (1, 2):
        G = [[rnd_op() for _ in range(r)] for _ in range(r)]
        H = [[rnd_op() for _ in range(r)] for _ in range(r)]
        ok(eq(sysact(G, Lt), sysact([[junk(x) for x in row] for row in G], Lt)), ("A1", m, r))
        I = [[fd(0) if i == j else {} for j in range(r)] for i in range(r)]
        ok(eq(sysact(I, Lt), [[Fraction(int(i == j)) for j in range(r * Lt.n)] for i in range(r * Lt.n)]), ("A2 one", m))
        ok(eq(sysact(mmul(G, H), Lt), L.matmul(sysact(G, Lt), sysact(H, Lt))), ("A2 mul", m, r))
        ok(eq(sysact(msub(G, H), Lt), [[a - b for a, b in zip(ra, rb)] for ra, rb in zip(sysact(G, Lt), sysact(H, Lt))]), ("A2 sub", m))
        ok(eq(sysact([[smul(3, x) for x in row] for row in G], Lt), [[3 * a for a in row] for row in sysact(G, Lt)]), ("A2 smul", m))
One = T(0)
for r in (1, 2, 3):
    G = [[rnd_op() for _ in range(r)] for _ in range(r)]
    ok(eq(sysact(G, One), [[get(G[s][s2], 0, 0) for s2 in range(r)] for s in range(r)]), ("A4", r))

# ---------- (T1) the twist map on systems, (T2) the V-split on systems ----------
for m in range(0, 3):
    N = T(m); P = PhiT(m)
    for r in (1, 2):
        G = [[rnd_op(MM=5) for _ in range(r)] for _ in range(r)]
        Pb, Cb, Bb, Db = blocks(G)
        big = sysact(G, P); sP, sC, sB, sD = (sysact(X, N) for X in (Pb, Cb, Bb, Db))
        good = True
        for s in range(r):
            for s2 in range(r):
                for (e, j) in P.B:
                    for (e2, j2) in P.B:
                        a = big[s * P.n + P.idx[(e2, j2)]][s2 * P.n + P.idx[(e, j)]]
                        blk = {(0, 0): sB, (1, 0): sP, (0, 1): sD, (1, 1): sC}[(e2, e)]
                        if a != blk[s * N.n + N.idx[j2]][s2 * N.n + N.idx[j]]: good = False
        ok(good, ("T1", m, r))
    # (T2) on V ⊗ Φ(T(m)) with M = Φ(T(m)), and on V ⊗ T(m)
    for (Mb, Mt) in ((P, 2 * m + 1), (N, m)):
        Bv, Wv, Fv = L.tensV(Mb.B, Mb.Wd, Mb.Fd_); V = Lat(Bv, Wv, Fv, Mt + 1)
        for r in (1, 2):
            G = [[rnd_op(MM=5) for _ in range(r)] for _ in range(r)]
            big = sysact(G, V); small = sysact(vsplit(G), Mb)
            good = True
            for s in range(r):
                for s2 in range(r):
                    for (a, j) in V.B:
                        for (a2, j2) in V.B:
                            x = big[s * V.n + V.idx[(a2, j2)]][s2 * V.n + V.idx[(a, j)]]
                            y = small[(2 * s + a2) * Mb.n + Mb.idx[j2]][(2 * s2 + a) * Mb.n + Mb.idx[j]]
                            if x != y: good = False
            ok(good, ("T2", m, r, Mt))

# ---------- (S1) a twist move, (S2) a split move: Smith forms of the cokernels ----------
for m in range(0, 4):
    N = T(m); P = PhiT(m); V = VPhiT(m)
    for r in (1, 2, 3):
        if r * V.n > 72: continue
        p, k = rnd_data(r)
        G = paySys(p, k, r)
        Gp = paySys(pT(p), kT(p, k), r)
        for h in range(0, 3):
            lhs = smith(sysact(G, P), 2 ** h)
            rhs = L.key([h] * (r * N.n) if h > 0 else []) + smith(sysact(Gp, N), 2 ** (h + 1))
            ok(lhs == L.key(rhs), ("S1", m, r, h))
        Gs = paySys(pSp(p), kSp(p, k), 2 * r)
        for h in range(0, 3):
            lhs = smith(sysact(G, V), 2 ** h)
            rhs = L.key([h] * (2 * r * N.n) if h > 0 else []) + smith(sysact(Gs, N), 2 ** (h + 1))
            ok(lhs == L.key(rhs), ("S2", m, r, h))
# (S1) also for a clean system that is not a payment system: G = U · paySys · U' with U, U' unit triangular
for m in range(0, 3):
    N = T(m); P = PhiT(m)
    for r in (1, 2):
        p, k = rnd_data(r)
        G = paySys(p, k, r); Gp = paySys(pT(p), kT(p, k), r)
        u = Fraction(random.choice([1, -1, 3, -3, 5]))
        Gu = [[smul(u, x) for x in row] for row in G]; Gpu = [[smul(u, x) for x in row] for row in Gp]
        for h in range(0, 3):
            lhs = smith(sysact(Gu, P), 2 ** h)
            rhs = L.key(([h] * (r * N.n) if h > 0 else []) + smith(sysact(Gpu, N), 2 ** (h + 1)))
            ok(lhs == rhs, ("S1 unit", m, r, h))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0
# 1. (N2) with (nil l) instead of (nil (l+1)): F^(l) ≠ 0 on T(l), l ≥ 1
if any(any(any(row) for row in fdiv(T(l).Fm, l + 1)[l]) for l in range(1, 6)): fired += 1
# 2. (T1) with B and Dd exchanged
N = T(2); P = PhiT(2); G = [[rnd_op(MM=5)]]
Pb, Cb, Bb, Db = blocks(G); big = sysact(G, P); sB = sysact(Bb, N); sD = sysact(Db, N)
if any(big[P.idx[(0, j2)]][P.idx[(0, j)]] != sD[N.idx[j2]][N.idx[j]] for j in N.B for j2 in N.B): fired += 1
# 3. (S1) without the summand (A/2^h)^{rank P}
p, k = rnd_data(1); G = paySys(p, k, 1); Gp = paySys(pT(p), kT(p, k), 1)
if smith(sysact(G, PhiT(2)), 4) != L.key(smith(sysact(Gp, T(2)), 8)): fired += 1
# 4. (S2) with 2^h instead of 2^(h+1) on the next system
Gs = paySys(pSp(p), kSp(p, k), 2)
if smith(sysact(G, VPhiT(1)), 2) != L.key([1] * (2 * T(1).n) + smith(sysact(Gs, T(1)), 2)): fired += 1
# 5. (A4) reading the coefficient at the floor 1
G = [[rnd_op() for _ in range(2)] for _ in range(2)]
if not eq(sysact(G, One), [[get(G[s][s2], 0, 1) for s2 in range(2)] for s in range(2)]): fired += 1
# 6. (S1) with the twist data of the wrong system (pT of other data)
p2, k2 = rnd_data(1)
if smith(sysact(G := paySys(p, k, 1), PhiT(2)), 2) != L.key([1] * T(2).n + smith(sysact(paySys(pT(p2), kT(p2, k2), 1), T(2)), 4)): fired += 1
print("controls fired", fired, "of 6")
