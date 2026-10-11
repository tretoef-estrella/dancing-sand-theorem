#!/usr/bin/env python3
"""Brute force for Lean piece C39b (paper v8 §10.2, the cube side: parts (b) of Lemmas 10.4 and
10.5). Grepy Escribano, 9 Oct 2026. Independent lattice model of T(λ) (chk_lattice_lib), exact
rationals, 2-adic Smith forms. N = T(l); odd families λ = 2l+1 = Φ(N); even λ = 2l+2 = V ⊗ Φ(N)."""
import sys
sys.path.insert(0, '.')
from fractions import Fraction
import chk_lattice_lib as L

checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)

def eye(n): return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
def add(X, Y): return [[X[i][j] + Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def sub(X, Y): return [[X[i][j] - Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def sc(c, X): return [[c * x for x in r] for r in X]
def mm(X, Y): return L.matmul(X, Y)
def diag(v): return [[Fraction(v[i]) if i == j else Fraction(0) for j in range(len(v))] for i in range(len(v))]
def dfact(k):
    p = 1
    while k > 1: p *= k; k -= 2
    return p
def smith(M):
    Mi = L.to_int(M); return None if Mi is None else L.smith2(Mi, len(M), len(M[0]))
def two(sm):   # 2·G for G = ⊕ Z/2^e ⊕ Z_2^r: every exponent minus one
    return sorted([None if x is None else x - 1 for x in sm if x is None or x > 1], key=lambda x: (x is None, x))

def mat_of(B, W, F):
    idx = {b: k for k, b in enumerate(B)}; n = len(B)
    Fm = [[Fraction(0)] * n for _ in range(n)]
    for b in B:
        for t, c in F[b].items(): Fm[idx[t]][idx[b]] += c
    return [W[b] for b in B], Fm

def ops(l):
    _, W, Fm = L.lat(l); n = len(W)
    I = eye(n); P = I; pows = [I]; fact = 1
    for r in range(1, l + 3):
        P = mm(P, Fm); fact *= r; pows.append(sc(Fraction(1, fact), P))
    Ch = I; Sh = I
    for s in range(1, len(pows)):
        Ch = add(Ch, sc(Fraction(1, dfact(2 * s - 1)), pows[s]))
        Sh = add(Sh, sc(Fraction(1, dfact(2 * s + 1)), pows[s]))
    Nil = sub(Sh, I); Shi = I; T = I
    for _ in range(n + 1):
        T = sc(-1, mm(T, Nil)); Shi = add(Shi, T)
    H = diag(W)
    return W, Fm, Ch, Sh, Shi, H, n

def Sop(W, d): return diag([(-1) ** abs(d - w) for w in W])
def Psi(l, d):
    W, Fm, Ch, Sh, Shi, H, n = ops(l)
    return add(sub(sc(2 * d, eye(n)), sc(2, H)), mm(sub(Ch, Sop(W, d)), Shi))
def Gp(l, d, two_factor=True):            # F − 2 J (J + 1), J = d − H
    W, Fm, *_ = ops(l)
    J = diag([d - w for w in W]); n = len(W)
    return sub(Fm, sc(2, mm(J, add(J, eye(n))))) if two_factor else None
def Sig(l, e):                            # F + 2e − 2H
    W, Fm, *_ = ops(l)
    return add(Fm, diag([2 * e - 2 * w for w in W]))
def tau(W, Fm, c): return add(Fm, diag([c - w for w in W]))
def glue(X, Y, Z):
    n = len(X)
    return [X[i] + [Fraction(0)] * n for i in range(n)] + [Z[i] + Y[i] for i in range(n)]

LMAX = 6
# ---------- (O0) weights of T(l): w ≤ l and l − w even ----------
for l in range(0, 9):
    _, W, _ = L.lat(l)
    ok(all(w <= l and (l - w) % 2 == 0 for w in W), ("weights parity", l))

# ---------- (O1) coker τ on Φ(N) at 2d+1 ≅ coker 2·Gp on N (any d) ----------
for l in range(0, LMAX + 1):
    _, Wl, Fl = L.lat(2 * l + 1)
    for d in range(-2, l + 6):
        ok(smith(tau(Wl, Fl, 2 * d + 1)) == smith(sc(2, Gp(l, d))), ("O1", l, d))

# ---------- (O3) coker Gp(d) ≅ coker Σ(e), e = d (d − l even) or d + 1 (d − l odd) ----------
for l in range(0, LMAX + 1):
    for d in range(-2, l + 6):
        e = d if (d - l) % 2 == 0 else d + 1
        ok(smith(Gp(l, d)) == smith(Sig(l, e)), ("O3", l, d))

# ---------- (O4) Lemma 10.4(b): 2X(2l+1, j) ≅ coker Σ_c on T(l), c = ⌈j/2⌉ ----------
for l in range(0, LMAX + 1):
    for j in range(0, 6):
        c = (j + 1) // 2
        ok(two(L.xfam(2 * l + 1, j)) == smith(Sig(l, l + 2 * c)), ("10.4b", l, j))

# ---------- (V1) coker τ on V⊗M at c+1 ≅ coker τ_M(τ_M + 2), any M = T(m), any c ----------
for m in range(0, 9):
    B, W, F = L.lat_T(m); W0, F0 = mat_of(B, W, F); n = len(W0)
    Bv, Wv, Fv = L.tensV(B, W, F); W1, F1 = mat_of(Bv, Wv, Fv)
    for c in range(-3, m + 5):
        tM = tau(W0, F0, c)
        ok(smith(tau(W1, F1, c + 1)) == smith(mm(tM, add(tM, sc(2, eye(n))))), ("V1", m, c))

# ---------- (V2) on Φ(N) at odd c: τ(τ+2) = 2θ, θ = F^(2) + F(J + 2) + J(J + 2)/2 ----------
for l in range(0, LMAX + 1):
    _, Wl, Fl = L.lat(2 * l + 1); n = len(Wl)
    F2 = sc(Fraction(1, 2), mm(Fl, Fl))
    for d in range(-2, l + 5):
        c = 2 * d + 1
        J = diag([c - w for w in Wl])
        th = add(add(F2, mm(Fl, add(J, sc(2, eye(n))))), diag([Fraction((c - w) * (c - w + 2), 2) for w in Wl]))
        ok(all((c - w) % 2 == 0 for w in Wl), ("V2 parity", l, d))
        tM = tau(Wl, Fl, c)
        ok(sc(2, th) == mm(tM, add(tM, sc(2, eye(n)))), ("V2", l, d))
        ok(L.to_int(th) is not None, ("theta integral", l, d))

# ---------- (V4) θ circulant in β, X_θ, Y_θ integral, and the two identities ----------
def PQ(l, d):
    W, Fm, Ch, Sh, Shi, H, n = ops(l)
    P = add(sub(sc(2 * d, eye(n)), sc(2, H)), mm(Ch, Shi))
    Q = sc(-1, mm(Sop(W, d), Shi))
    return P, Q, n
def XY(l, d):
    P, Q, n = PQ(l, d)
    X = sc(Fraction(1, 2), add(add(mm(P, P), mm(Q, Q)), sc(2, P)))
    Y = sc(Fraction(1, 2), add(add(mm(P, Q), mm(Q, P)), sc(2, Q)))
    return X, Y, n
for l in range(0, LMAX):
    _, Wl, Fl = L.lat(2 * l + 1); m = len(Wl)
    for d in range(l, l + 4):
        c = 2 * d + 1
        E, _ = L.expF(2 * l + 1, 2 * l + 4)
        a = [[(-1) ** abs((c - Wl[i]) // 2) * E[i][j] for j in range(m)] for i in range(m)]
        X, Y, n = XY(l, d)
        b0 = [[Fraction(int(i == j)) for j in range(n)] for i in range(m)]
        beta = [b0[i] + mm(a, b0)[i] for i in range(m)]
        F2 = sc(Fraction(1, 2), mm(Fl, Fl)); J = diag([c - w for w in Wl])
        th = add(add(F2, mm(Fl, add(J, sc(2, eye(m))))), diag([Fraction((c - w) * (c - w + 2), 2) for w in Wl]))
        circ = [X[i] + Y[i] for i in range(n)] + [Y[i] + X[i] for i in range(n)]
        ok(mm(th, beta) == mm(beta, circ), ("theta circulant", l, d))
        ok(L.to_int(X) is not None and L.to_int(Y) is not None, ("X Y integral", l, d))
        Pd, Pd1 = Psi(l, d), Psi(l, d + 1)
        ok(sc(2, add(X, Y)) == mm(Pd, add(Pd, sc(2, eye(n)))), ("2(X+Y)", l, d))
        ok(sc(2, sub(X, Y)) == mm(sub(Pd1, sc(2, eye(n))), Pd1), ("2(X-Y)", l, d))
        P, Q, _ = PQ(l, d)
        ok(sub(P, Q) == sub(Pd1, sc(2, eye(n))), ("P-Q", l, d))

# ---------- (V7) Lemma 10.5(b): 2X(2l+2, i) ≅ coker glue(X−Y, X+Y, Y) on T(l) ⊕ T(l), d = l+i ----------
for l in range(0, LMAX):
    for i in range(0, 5):
        X, Y, n = XY(l, l + i)
        ok(two(L.xfam(2 * l + 2, i)) == smith(glue(sub(X, Y), add(X, Y), Y)), ("10.5b", l, i))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0
# 1. Σ with e = d always (wrong for odd j)
if any(two(L.xfam(2 * l + 1, j)) != smith(Sig(l, l + j)) for l in range(1, 5) for j in range(1, 5, 2)): fired += 1
# 2. glue without the lower-left block Y
if any(two(L.xfam(2 * l + 2, i)) != smith(glue(sub(*XY(l, l + i)[:2]), add(*XY(l, l + i)[:2]), sc(0, XY(l, l + i)[1]))) for l in range(0, 4) for i in range(3)): fired += 1
# 3. the even family at the wrong d (l + i + 1)
# (two earlier candidates could not fire: the two arms exchanged, and the arm Psi_d(Psi_d + 2)/2
#  replaced by Psi_d(Psi_d - 2)/2 -- same Smith form in every cell tried; so is the arm Psi_d alone)
if any(two(L.xfam(2 * l + 2, i)) != smith(glue(sub(*XY(l, l + i + 1)[:2]), add(*XY(l, l + i + 1)[:2]), XY(l, l + i + 1)[1])) for l in range(0, 4) for i in range(3)): fired += 1
# 4. (O1) without the factor 2
if any(smith(tau(L.lat(2 * l + 1)[1], L.lat(2 * l + 1)[2], 2 * d + 1)) != smith(Gp(l, d)) for l in range(1, 4) for d in range(l, l + 3)): fired += 1
print("controls fired", fired, "of 4")
