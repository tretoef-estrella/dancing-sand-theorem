#!/usr/bin/env python3
"""Lattice model of T(λ), divided powers, 2-adic Smith forms (lines 1–168 of chkC38b.py, copied as a library for chkC39.py).
Grepy Escribano, 8 Oct 2026. Independent lattice model of T(λ) (from chkC32),
divided powers F^(r) = F^r / r! over Q (the lattice is torsion-free), 2-adic Smith forms."""
import random
from fractions import Fraction
from collections import Counter

random.seed(38)
MOD = 1 << 60
checks = fails = 0

def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)

def v2(x):
    x %= MOD
    if x == 0: return None
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def smith2(M, nrows, ncols):
    """2-adic Smith exponents of the cokernel of an nrows x ncols integer matrix:
    one entry per row of the target; None = a free summand (Z_2)."""
    A = [[x % MOD for x in r] for r in M]
    out = []
    rows = list(range(nrows)); cols = list(range(ncols))
    while True:
        best = None
        for i in rows:
            for j in cols:
                vv = v2(A[i][j])
                if vv is not None and (best is None or vv < best[0]):
                    best = (vv, i, j)
                    if vv == 0: break
            if best is not None and best[0] == 0: break
        if best is None: break
        vv, pi, pj = best
        out.append(vv)
        u = A[pi][pj] >> vv
        uinv = pow(u, -1, MOD)
        for i in rows:
            if i == pi: continue
            a = A[i][pj]
            if a == 0: continue
            c = ((a >> vv) * uinv) % MOD
            rowp = A[pi]; rowi = A[i]
            for j in cols: rowi[j] = (rowi[j] - c * rowp[j]) % MOD
        rows.remove(pi); cols.remove(pj)
    out += [None] * len(rows)
    return sorted([x for x in out if x != 0], key=lambda x: (x is None, x))

def key(xs): return sorted(xs, key=lambda x: (x is None, x))

def rank_mod_p(M, nrows, ncols, p=1000003):
    A = [[x % p for x in r] for r in M]; r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, nrows) if A[i][c]), None)
        if piv is None: continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], -1, p)
        for i in range(nrows):
            if i != r and A[i][c]:
                f = A[i][c] * inv % p
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r

# ---------- lattice model of T(λ) (as in chkC32) ----------
def lat_T(l):
    if l == 0: return [()], {(): 0}, {(): {}}
    if l % 2 == 1:
        B, W, F = lat_T((l - 1) // 2); return phi(B, W, F)
    B, W, F = lat_T((l - 2) // 2); return tensV(*phi(B, W, F))
def phi(B, W, F):
    nb = [(e, j) for e in (0, 1) for j in B]
    nw = {(e, j): 2 * W[j] + (1 if e == 0 else -1) for (e, j) in nb}
    nf = {}
    for j in B:
        nf[(0, j)] = {(1, j): 1}
        d = {}
        for t, c in F[j].items(): d[(0, t)] = d.get((0, t), 0) + 2 * c
        nf[(1, j)] = d
    return nb, nw, nf
def tensV(B, W, F):
    nb = [(a, j) for a in (0, 1) for j in B]
    nw = {(a, j): (1 if a == 0 else -1) + W[j] for (a, j) in nb}
    nf = {}
    for (a, j) in nb:
        d = {}
        if a == 0: d[(1, j)] = d.get((1, j), 0) + 1
        for t, c in F[j].items(): d[(a, t)] = d.get((a, t), 0) + c
        nf[(a, j)] = d
    return nb, nw, nf

LAT = {}
def lat(l):
    if l not in LAT:
        B, W, F = lat_T(l); idx = {b: k for k, b in enumerate(B)}; N = len(B)
        Fm = [[Fraction(0)] * N for _ in range(N)]
        for b in B:
            for t, c in F[b].items(): Fm[idx[t]][idx[b]] += c
        LAT[l] = (B, [W[b] for b in B], Fm)
    return LAT[l]

def matmul(X, Y):
    n = len(X); m = len(Y[0]); k = len(Y)
    return [[sum(X[i][t] * Y[t][j] for t in range(k) if X[i][t]) for j in range(m)] for i in range(n)]

def expF(l, B):
    """Σ_{r<B} F^(r) with F^(r) = F^r / r!; returns (matrix, list of the F^(r))"""
    _, W, Fm = lat(l); N = len(W)
    Id = [[Fraction(int(i == j)) for j in range(N)] for i in range(N)]
    P = Id; S = [row[:] for row in Id]; pows = [Id]; fact = 1
    for r in range(1, B):
        P = matmul(P, Fm); fact *= r
        D = [[Fraction(x) / fact for x in row] for row in P]
        pows.append(D)
        S = [[S[i][j] + D[i][j] for j in range(N)] for i in range(N)]
    return S, pows

def to_int(M):
    """2-adic integers: odd denominators are units of Z_2 (inverted mod 2^60); an even
    denominator is a failure (returns None)."""
    out = []
    for row in M:
        r = []
        for x in row:
            x = Fraction(x)
            if x.denominator % 2 == 0: return None
            r.append(x.numerator * pow(x.denominator, -1, MOD) % MOD)
        out.append(r)
    return out

def xbar_mat(l, c, B, sign=True):
    """columns [τ | a − 1] on T(l), τ = F + c − H, a = signOp_c ∘ expF_B"""
    _, W, Fm = lat(l); N = len(W)
    E, _ = expF(l, B)
    tau = [[Fm[i][j] + (c - W[i] if i == j else 0) for j in range(N)] for i in range(N)]
    a = [[((-1) ** abs((c - W[i]) // 2) if sign else 1) * E[i][j] for j in range(N)] for i in range(N)]
    am1 = [[a[i][j] - (1 if i == j else 0) for j in range(N)] for i in range(N)]
    M = to_int([tau[i] + am1[i] for i in range(N)])
    return M, N

def xbar(l, c, B, sign=True):
    M, N = xbar_mat(l, c, B, sign); return smith2(M, N, 2 * N)

def xfam(l, i):
    """X^(1)(λ, i) = coker τ_i on T(λ) (chkC32 lat_op, α = 1)"""
    _, W, Fm = lat(l); N = len(W)
    M = to_int([[Fm[r][s] + (l + 2 * i - W[r] if r == s else 0) for s in range(N)] for r in range(N)])
    return smith2(M, N, N)

def tdot(l):
    if l == 0: return [1]
    if l % 2 == 1: return [l + 1]
    m = (l - 2) // 2
    return [l - 1, l - 1] + [2 * x + 1 for x in tdot(m)]
def Lst(n):
    L = [0]
    for _ in range(n): L = [x for lam in L for x in tdot(lam)]
    return L

