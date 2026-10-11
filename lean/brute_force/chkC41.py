#!/usr/bin/env python3
"""Brute force for Lean piece C41 (paper v8 §10.4, Lemma 10.8: the inverse block, as the lift
identity G L = 2^k I M along the whole dance on T(l)). Grepy Escribano, 9 Oct 2026. Definitions copied from chkC40c.py (independent
lattice model, exact rationals, 2-adic Smith forms); payment systems with random data."""
import random
import sys
sys.path.insert(0, '.')
from fractions import Fraction
from math import comb
import chk_lattice_lib as L

random.seed(4101)
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

# ======================= C41: Lemma 10.8, the inverse block (the lift identity) =======================
def digits(l):
    out = []
    while l > 0:
        if l % 2 == 1: out.append(False); l = (l - 1) // 2
        else: out.append(True); l = (l - 2) // 2
    return out
def zeros(a, b): return [[Fraction(0)] * b for _ in range(a)]
def ident(a): return [[Fraction(int(i == j)) for j in range(a)] for i in range(a)]
def mm(X, Y):
    n, k, m = len(X), len(Y), len(Y[0]) if Y else 0
    Z = zeros(n, m)
    for i in range(n):
        Xi = X[i]; Zi = Z[i]
        for t in range(k):
            a = Xi[t]
            if a:
                Yt = Y[t]
                for j in range(m):
                    if Yt[j]: Zi[j] += a * Yt[j]
    return Z
def inv(M):
    n = len(M); A = [list(r) + [Fraction(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        piv = next((i for i in range(c, n) if A[i][c] != 0), None)
        if piv is None: return None
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]; A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [r[n:] for r in A]
def sub_(M, rows, cols): return [[M[i][j] for j in cols] for i in rows]
def finalM(p, k, n):
    return [[Fraction(2 * p[s](0)) if s == s2 else (Fraction(2 * k[s][s2](0)) if s2 < s else Fraction(0))
             for s2 in range(n)] for s in range(n)]

def lift(l, p, k, ctrl=None):
    """returns (G matrix on T(l), L, I, O, final p, final k, final slots, number of moves);
    checks at every level that the Schur complement is 2 * the next system."""
    R = len(p); Tl = T(l)
    big = sysact(paySys(p, k, R), Tl, l + 1)
    if l == 0:
        n = Tl.n * R
        return big, ident(n), ident(n), ident(n), p, k, R, 0, True
    if l % 2 == 1:
        lp = (l - 1) // 2; slots = R; p2, k2 = pT(p), kT(p, k)
    else:
        lp = (l - 2) // 2; slots = 2 * R; p2, k2 = pSp(p), kSp(p, k)
    n1 = T(lp).n
    e0 = [sl * 2 * n1 + jj for sl in range(slots) for jj in range(n1)]
    e1 = [sl * 2 * n1 + n1 + jj for sl in range(slots) for jj in range(n1)]
    if ctrl == 'split_order' and l % 2 == 0:   # slot (s, a) read as a*R + s instead of 2s + a
        perm = [ (sl % 2) * R + sl // 2 for sl in range(slots)]
        e0 = [perm[sl] * 2 * n1 + jj for sl in range(slots) for jj in range(n1)]
        e1 = [perm[sl] * 2 * n1 + n1 + jj for sl in range(slots) for jj in range(n1)]
    P = sub_(big, e1, e0); C = sub_(big, e1, e1); Bb = sub_(big, e0, e0); Dd = sub_(big, e0, e1)
    Pi = inv(P)
    Gn, Ln, In, On, pf, kf, nf, kk, good = lift(lp, p2, k2, ctrl)
    S = [[a - b for a, b in zip(ra, rb)] for ra, rb in zip(Dd, mm(mm(Bb, Pi), C))]
    good = good and (Pi is not None) and S == [[2 * x for x in r] for r in Gn]
    N = len(big); F = len(Ln[0])
    Lc = zeros(N, F); Ic = zeros(N, F); Oc = zeros(F, N)
    U = mm(mm(Pi, C), Ln)
    for a, i in enumerate(e1):
        Lc[i] = list(Ln[a])
    for a, i in enumerate(e0):
        Lc[i] = [Fraction(0)] * F if ctrl == 'no_correction' else [-x for x in U[a]]
    rdI = e1 if ctrl == 'I_reads_e1' else e0
    for a, i in enumerate(rdI): Ic[i] = list(In[a])
    rdO = e0 if ctrl == 'O_reads_e0' else e1
    for a, i in enumerate(rdO):
        for f in range(F): Oc[f][i] = On[f][a]
    return big, Lc, Ic, Oc, pf, kf, nf, kk + 1, good

def check(l, p, k, ctrl=None, scale=None):
    G, Lm, Im, Om, pf, kf, nf, K, good = lift(l, p, k, ctrl)
    M = finalM(pf, kf, nf)
    sc = Fraction(2 ** (K if scale is None else scale))
    lhs = mm(G, Lm); rhs = [[sc * x for x in r] for r in mm(Im, M)]
    res = {'schur': good, 'lift': lhs == rhs, 'OL': mm(Om, Lm) == ident(nf), 'K': K}
    Gi = inv(G); Mi = inv(M)
    if Gi is not None and Mi is not None:
        res['inv'] = Mi == [[sc * x for x in r] for r in mm(mm(Om, Gi), Im)]
    else:
        res['inv'] = None
    res['n'] = nf
    return res

# (V1)-(V3): every l ≤ 7, sizes 1-3, two random data each; the field form when invertible
for l in range(0, 8):
    ds_ = digits(l); m = sum(ds_)
    for r in (1, 2, 3):
        if r * T(l).n > 48: continue
        for trial in range(2):
            p, k = rnd_data(r)
            res = check(l, p, k)
            ok(res['schur'], ("schur = 2 next", l, r, trial))
            ok(res['lift'], ("G L = 2^k I M", l, r, trial))
            ok(res['OL'], ("O L = id", l, r, trial))
            ok(res['K'] == len(ds_) and res['n'] == r * 2 ** m, ("count", l, r))
            # the field form needs an invertible system: data with p(f) != 0 everywhere
            pn = [(lambda f, s=s, t=[random.choice([-5, -3, -1, 1, 3, 5]) for _ in range(200)]: t[f]) for s in range(r)]
            res2 = check(l, pn, k)
            ok(res2['inv'] is True, ("M^-1 = 2^k O G^-1 I (p != 0)", l, r, trial))
            if res['inv'] is not None: ok(res['inv'], ("M^-1 = 2^k O G^-1 I", l, r, trial))
# (V4) σ^{(α)}_i with i ≥ 1 (invertible), l ≤ 7
for l in range(0, 8):
    for alpha in (1, 2, 3):
        for i in (1, 2, 5):
            p = [(lambda f, alpha=alpha, i=i: 2 ** (alpha - 1) * (i + f))]
            k = [[(lambda f: 0)]]
            res = check(l, p, k)
            ok(res['schur'] and res['lift'] and res['OL'] and res['inv'], ("sigma", l, alpha, i))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0; tried = 0
for ctrl, lv in (('I_reads_e1', 5), ('O_reads_e0', 5), ('no_correction', 5), ('split_order', 6)):
    tried += 1
    p, k = rnd_data(2)
    res = check(lv, p, k, ctrl)
    if not (res['lift'] and res['OL'] and res['schur']): fired += 1
    else: print("control did not fire:", ctrl)
tried += 1
p, k = rnd_data(2); res = check(7, p, k, None, scale=len(digits(7)) - 1)   # 2^{k-1} instead of 2^k (k = 3 at l = 7)
if not res['lift']: fired += 1
else: print("control did not fire: scale")
print("controls fired", fired, "of", tried)
