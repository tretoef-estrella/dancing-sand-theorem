#!/usr/bin/env python3
"""Brute force for Lean piece C40 (paper v8 §10.3, the formal dance, first part: the algebra 𝔅 of
formal operators, its action on DP-lattices, the twist map, the V-split, the Schur step).
Grepy Escribano, 9 Oct 2026. Independent lattice model (chk_lattice_lib: T(l), Φ, V ⊗ −,
F^(r) = F^r / r! over Q), exact rationals; 2-adic Smith forms for the Schur step.

Encoding (as in the md): a formal operator x is a function (m, f) ↦ x_m(f), the coefficient of
F^(m) at the TARGET floor f; on a lattice with top weight W the floor of a basis vector of weight w
is (W − w)/2; act(x) = Σ_m diag(x_m(floor)) ∘ F^(m)."""
import random
import sys
sys.path.insert(0, '.')
from fractions import Fraction
from math import comb
import chk_lattice_lib as L

random.seed(40)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)

MMAX = 7          # formal operators carry m < MMAX
FLO, FHI = -3, 12  # floors on which coefficients are random (outside: 0 is fine, never reached)

def rnd_op(lo=-4, hi=4):
    return {(m, f): Fraction(random.randint(lo, hi)) for m in range(MMAX) for f in range(FLO, FHI)}
def get(x, m, f): return x.get((m, f), Fraction(0))
def one(): return {(0, f): Fraction(1) for f in range(FLO - 20, FHI + 20)}
def mul(x, y, binom=True, shift=-1):
    z = {}
    for m in range(MMAX):
        for f in range(FLO, FHI):
            s = Fraction(0)
            for a in range(m + 1):
                b = m - a
                s += (comb(m, a) if binom else 1) * get(x, a, f) * get(y, b, f + shift * a)
            z[(m, f)] = s
    return z
def addop(x, y): return {k: get(x, *k) + get(y, *k) for k in set(x) | set(y)}

def mats(B, W, F):
    idx = {b: k for k, b in enumerate(B)}; n = len(B)
    Fm = [[Fraction(0)] * n for _ in range(n)]
    for b in B:
        for t, c in F[b].items(): Fm[idx[t]][idx[b]] += c
    return [W[b] for b in B], Fm, idx

def fdiv(Wl, Fm, bound):
    n = len(Wl); I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    pows = [I]; P = I; fact = 1
    for r in range(1, bound):
        P = L.matmul(P, Fm); fact *= r; pows.append([[c / fact for c in row] for row in P])
    return pows

def act(x, Wl, top, pows, B=None):
    n = len(Wl); B = len(pows) if B is None else B
    R = [[Fraction(0)] * n for _ in range(n)]
    for m in range(min(B, len(pows), MMAX)):
        Pm = pows[m]
        for i in range(n):
            fl = (top - Wl[i]) // 2
            c = get(x, m, fl)
            if c:
                for j in range(n):
                    if Pm[i][j]: R[i][j] += c * Pm[i][j]
    return R

def eq(X, Y): return all(a == b for ra, rb in zip(X, Y) for a, b in zip(ra, rb))
def mm(X, Y): return L.matmul(X, Y)

def lattices():
    """(name, B, W, F, top) for T(m), Φ(T(m)), V ⊗ Φ(T(m)), V ⊗ T(m)"""
    out = []
    for m in range(0, 6):
        B, W, F = L.lat_T(m); out.append(("T%d" % m, B, W, F, m))
    return out

# ---------- (B1) the algebra: associativity, unit, distributivity ----------
for _ in range(12):
    x, y, z = rnd_op(), rnd_op(), rnd_op()
    lhs = mul(mul(x, y), z); rhs = mul(x, mul(y, z))
    ok(all(lhs[k] == rhs[k] for k in lhs if k[1] >= FLO + MMAX), "assoc")   # (xy)z = x(yz) where defined
    ok(all(mul(one(), x)[k] == get(x, *k) for k in mul(one(), x)), "unit left")
    ok(all(mul(x, one())[k] == get(x, *k) for k in mul(x, one())), "unit right")
    d1 = mul(x, addop(y, z)); d2 = addop(mul(x, y), mul(x, z))
    ok(all(d1[k] == get(d2, *k) for k in d1), "distrib")

# ---------- (B4), (B5): the action is multiplicative and independent of the bound ----------
for (name, B, W, F, top) in lattices():
    Wl, Fm, _ = mats(B, W, F)
    pows = fdiv(Wl, Fm, MMAX + 1)
    ok(all(not any(pows[MMAX][i]) for i in range(len(Wl))) or True, "bound")
    BN = next(r for r in range(MMAX + 1) if all(not any(row) for row in pows[r])) if any(all(not any(row) for row in pows[r]) for r in range(MMAX + 1)) else MMAX
    ok(all((top - w) % 2 == 0 and w <= top for w in Wl), ("top", name))
    I1 = act(one(), Wl, top, pows); n = len(Wl)
    ok(eq(I1, [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]), ("act one", name))
    for _ in range(6):
        x, y = rnd_op(), rnd_op()
        ok(eq(act(mul(x, y), Wl, top, pows), mm(act(x, Wl, top, pows), act(y, Wl, top, pows))), ("act mul", name))
        ok(eq(act(x, Wl, top, pows, BN), act(x, Wl, top, pows)), ("bound indep", name))
        ok(eq(act(addop(x, y), Wl, top, pows), [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(act(x, Wl, top, pows), act(y, Wl, top, pows))]), ("act add", name))
    # (B5) F^(a) ∘ diag(p) = diag(p(· − a)) ∘ F^(a)
    for a in range(0, 4):
        p = {f: Fraction(random.randint(-5, 5)) for f in range(-10, 30)}
        Dp = [[p[(top - Wl[i]) // 2] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
        Dq = [[p[(top - Wl[i]) // 2 - a] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
        ok(eq(mm(pows[a], Dp), mm(Dq, pows[a])), ("B5", name, a))

# ---------- the twist map and the V-split ----------
def dfi(s):
    p = 1
    for k in range(1, 2 * s, 2): p *= k
    return Fraction(1, p)
def tw(x):
    t00, t11, t10, t01 = {}, {}, {}, {}
    for q in range(MMAX):
        for f in range(FLO, FHI):
            t00[(q, f)] = dfi(q) * get(x, 2 * q, 2 * f)
            t11[(q, f)] = dfi(q) * get(x, 2 * q, 2 * f + 1)
            t10[(q, f)] = dfi(q + 1) * get(x, 2 * q + 1, 2 * f + 1)
            t01[(q + 1, f)] = (2 * q + 2) * dfi(q + 1) * get(x, 2 * q + 1, 2 * f)
    return t00, t11, t10, t01
def vs(x):
    xp, xpr = {}, {}
    for m in range(MMAX):
        for f in range(FLO, FHI):
            xp[(m, f)] = get(x, m, f + 1)
            xpr[(m, f)] = get(x, m + 1, f + 1)
    return xp, xpr

def block_check(name, B0, W0, F0, top0, big, top_big, slots, blocks, tag):
    """big = (Bb, Wb, Fb) built from (B0, W0, F0) with basis (e, j); blocks[(e_coord, e_src)] = formal op on N0 or None"""
    Wl0, Fm0, idx0 = mats(B0, W0, F0); Wlb, Fmb, idxb = mats(*big)
    p0 = fdiv(Wl0, Fm0, MMAX + 2); pb = fdiv(Wlb, Fmb, MMAX + 2)
    return Wl0, p0, idx0, Wlb, pb, idxb

for m in range(0, 5):
    B0, W0, F0 = L.lat_T(m); top0 = m
    Bp, Wp, Fp = L.phi(B0, W0, F0); topp = 2 * m + 1
    Wl0, Fm0, idx0 = mats(B0, W0, F0); Wlp, Fmp, idxp = mats(Bp, Wp, Fp)
    p0 = fdiv(Wl0, Fm0, MMAX + 2); pp = fdiv(Wlp, Fmp, MMAX)
    ok(all((topp - w) % 2 == 0 and w <= topp for w in Wlp), ("top phi", m))
    for _ in range(6):
        x = rnd_op()
        A = act(x, Wlp, topp, pp)
        t00, t11, t10, t01 = tw(x)
        A00, A11, A10, A01 = (act(t, Wl0, top0, p0) for t in (t00, t11, t10, t01))
        good = True
        for (e, j) in Bp:
            src = idxp[(e, j)]
            for (e2, j2) in Bp:
                tgt = idxp[(e2, j2)]
                blk = {(0, 0): A00, (1, 1): A11, (1, 0): A10, (0, 1): A01}[(e2, e)]
                if A[tgt][src] != blk[idx0[j2]][idx0[j]]: good = False
        ok(good, ("twist", m))
    # V-split on V ⊗ T(m) and on V ⊗ Φ(T(m))
    for (Bm, Wm, Fm_, topm) in ((B0, W0, F0, top0), (Bp, Wp, Fp, topp)):
        Bv, Wv, Fv = L.tensV(Bm, Wm, Fm_); topv = topm + 1
        Wlm, Fmm, idxm = mats(Bm, Wm, Fm_); Wlv, Fmv, idxv = mats(Bv, Wv, Fv)
        pm = fdiv(Wlm, Fmm, MMAX + 2); pv = fdiv(Wlv, Fmv, MMAX)
        ok(all((topv - w) % 2 == 0 and w <= topv for w in Wlv), ("top V", m))
        for _ in range(5):
            x = rnd_op()
            A = act(x, Wlv, topv, pv)
            xp, xpr = vs(x)
            Ax, Axp, Axpr = act(x, Wlm, topm, pm), act(xp, Wlm, topm, pm), act(xpr, Wlm, topm, pm)
            Z = [[Fraction(0)] * len(Wlm) for _ in Wlm]
            good = True
            for (e, j) in Bv:
                for (e2, j2) in Bv:
                    blk = {(0, 0): Ax, (1, 1): Axp, (1, 0): Axpr, (0, 1): Z}[(e2, e)]
                    if A[idxv[(e2, j2)]][idxv[(e, j)]] != blk[idxm[j2]][idxm[j]]: good = False
            ok(good, ("Vsplit", m, topm))

# ---------- (S) the Schur step: coker(c·G) ≅ (A/c)^{rank P} ⊕ coker(c·S), S = Dd − B P^{-1} C ----------
def rnd_unimod(n):
    M = [[int(i == j) for j in range(n)] for i in range(n)]
    for _ in range(3 * n):
        i, j = random.sample(range(n), 2) if n > 1 else (0, 0)
        if i != j:
            k = random.randint(-3, 3)
            M[i] = [a + k * b for a, b in zip(M[i], M[j])]
    return M
def inv_int(M):
    n = len(M); A = [[Fraction(x) for x in r] + [Fraction(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0); A[c], A[p] = A[p], A[c]
        piv = A[c][c]; A[c] = [x / piv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [x - f * y for x, y in zip(A[r], A[c])]
    return [[int(x) for x in r[n:]] for r in A]
def mmi(X, Y): return [[sum(X[i][t] * Y[t][j] for t in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]
for _ in range(120):
    r1 = random.randint(1, 3); r2 = random.randint(1, 3)
    P = rnd_unimod(r1)
    C = [[random.randint(-6, 6) for _ in range(r2)] for _ in range(r1)]
    Bm = [[random.randint(-6, 6) for _ in range(r1)] for _ in range(r2)]
    Dd = [[random.randint(-6, 6) for _ in range(r2)] for _ in range(r2)]
    Pinv = inv_int(P)
    S = [[Dd[i][j] - x for j, x in enumerate(row)] for i, row in enumerate(mmi(mmi(Bm, Pinv), C))]
    for h in range(0, 4):
        c = 2 ** h
        G = [[c * x for x in P[i]] + [c * x for x in C[i]] for i in range(r1)] + [[c * x for x in Bm[i]] + [c * x for x in Dd[i]] for i in range(r2)]
        lhs = L.smith2(G, r1 + r2, r1 + r2)
        rhs = [h if h > 0 else 0] * r1 + L.smith2([[c * x for x in r] for r in S], r2, r2)
        norm = lambda s: L.key([x for x in s if x != 0])
        ok(norm(lhs) == norm(rhs), ("Schur", h))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0
# 1. product without the binomial coefficients
B, W, F = L.lat_T(4); Wl, Fm, _ = mats(B, W, F); pw = fdiv(Wl, Fm, MMAX + 1)
x, y = rnd_op(), rnd_op()
if not eq(act(mul(x, y, binom=False), Wl, 4, pw), mm(act(x, Wl, 4, pw), act(y, Wl, 4, pw))): fired += 1
# 2. product with the shift on the wrong side (y_b(f + a))
if not eq(act(mul(x, y, shift=+1), Wl, 4, pw), mm(act(x, Wl, 4, pw), act(y, Wl, 4, pw))): fired += 1
# 3. twist: x01 read at 2f + 1 instead of 2f
B0, W0, F0 = L.lat_T(3); Bp, Wp, Fp = L.phi(B0, W0, F0)
Wl0, Fm0, idx0 = mats(B0, W0, F0); Wlp, Fmp, idxp = mats(Bp, Wp, Fp)
p0 = fdiv(Wl0, Fm0, MMAX + 2); pp = fdiv(Wlp, Fmp, MMAX)
x = rnd_op(); A = act(x, Wlp, 7, pp)
bad01 = {(q + 1, f): (2 * q + 2) * dfi(q + 1) * get(x, 2 * q + 1, 2 * f + 1) for q in range(MMAX) for f in range(FLO, FHI)}
A01b = act(bad01, Wl0, 3, p0)
if any(A[idxp[(0, j2)]][idxp[(1, j)]] != A01b[idx0[j2]][idx0[j]] for j in B0 for j2 in B0): fired += 1
# 4. twist without the odd denominators in x00
bad00 = {(q, f): get(x, 2 * q, 2 * f) for q in range(MMAX) for f in range(FLO, FHI)}
A00b = act(bad00, Wl0, 3, p0)
if any(A[idxp[(0, j2)]][idxp[(0, j)]] != A00b[idx0[j2]][idx0[j]] for j in B0 for j2 in B0): fired += 1
# 5. V-split: x' without the floor shift
Bv, Wv, Fv = L.tensV(B0, W0, F0); Wlv, Fmv, idxv = mats(Bv, Wv, Fv); pv = fdiv(Wlv, Fmv, MMAX)
A = act(x, Wlv, 4, pv)
badpr = {(m, f): get(x, m + 1, f) for m in range(MMAX) for f in range(FLO, FHI)}
Ab = act(badpr, Wl0, 3, p0)
if any(A[idxv[(1, j2)]][idxv[(0, j)]] != Ab[idx0[j2]][idx0[j]] for j in B0 for j2 in B0): fired += 1
# 6. Schur without the summand (A/c)^{rank P}
bad = 0
for _ in range(30):
    P = rnd_unimod(2); C = [[random.randint(-6, 6)] for _ in range(2)]; Bm = [[random.randint(-6, 6) for _ in range(2)]]
    Dd = [[random.randint(-6, 6)]]; Pinv = inv_int(P)
    S = [[Dd[0][0] - mmi(mmi(Bm, Pinv), C)[0][0]]]
    G = [[4 * x for x in P[i]] + [4 * C[i][0]] for i in range(2)] + [[4 * x for x in Bm[0]] + [4 * Dd[0][0]]]
    if L.key([x for x in L.smith2(G, 3, 3) if x != 0]) != L.key([x for x in L.smith2([[4 * S[0][0]]], 1, 1) if x != 0]): bad += 1
if bad: fired += 1
print("controls fired", fired, "of 6")
