#!/usr/bin/env python3
"""Brute force for Lean piece C39 (paper v8 §10.2, the fold side: Ch, Sh, Ψ, the coinvariant
reduction of Lemma 10.4(a), the glue of Lemma 10.5(a)). Grepy Escribano, 8 Oct 2026.
Independent lattice model of T(λ) from chk_lattice_lib (= chkC38b), exact rationals, 2-adic
Smith forms. N = T(l); odd families λ = 2l+1 = Φ(N); even families λ = 2l+2 = V ⊗ Φ(N)."""
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
def iszero(X): return all(x == 0 for r in X for x in r)
def dfact(k):  # k!! for odd k ≥ −1
    p = 1
    while k > 1: p *= k; k -= 2
    return p

def ops(l):
    """on N = T(l): weights W, F, divided powers, Ch, Sh, Sh^{-1}, H"""
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
    H = [[Fraction(W[i]) if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    return W, Fm, pows, Ch, Sh, Shi, H, n

def Sop(W, d): return [[Fraction((-1) ** abs(d - W[i])) if i == j else Fraction(0) for j in range(len(W))] for i in range(len(W))]

def Psi(l, d, sign_shift=0, dropH=False):
    W, Fm, pows, Ch, Sh, Shi, H, n = ops(l)
    S = Sop(W, d + sign_shift)
    base = sc(2 * d, eye(n)) if dropH else sub(sc(2 * d, eye(n)), sc(2, H))
    return add(base, mm(sub(Ch, S), Shi))

def Zop(l, d):
    W, Fm, pows, Ch, Sh, Shi, H, n = ops(l)
    return sub(sc(-1, eye(n)), mm(Sop(W, d), Shi))

def smith_sq(M):
    Mi = L.to_int(M); return None if Mi is None else L.smith2(Mi, len(M), len(M[0]))

def glue(X, Y, Z):
    n = len(X)
    top = [X[i] + [Fraction(0)] * n for i in range(n)]
    bot = [Z[i] + Y[i] for i in range(n)]
    return top + bot

LMAX = 6
# ---------- (S) Ch, Sh, Sh^{-1} 2-adically integral, Sh unipotent, Sh·Sh^{-1} = 1 ----------
for l in range(0, LMAX + 1):
    W, Fm, pows, Ch, Sh, Shi, H, n = ops(l)
    ok(all(iszero(P) for P in pows[l + 1:]), ("F^(s)=0 for s>l", l))
    ok(mm(Sh, Shi) == eye(n) and mm(Shi, Sh) == eye(n), ("Sh inverse", l))
    ok(L.to_int(Ch) is not None and L.to_int(Sh) is not None and L.to_int(Shi) is not None, ("integral", l))
    ok(all(-l <= w <= l for w in W), ("weights in [-l,l]", l))
    for d in range(-1, 6):
        S = Sop(W, d)
        ok(mm(S, Ch) == mm(Ch, S) and mm(S, Sh) == mm(Sh, S) and mm(S, S) == eye(n), ("S commutes", l, d))
        ok(L.to_int(Psi(l, d)) is not None, ("Psi integral", l, d))
        # (G) 2·Z = Ψ(d) − Ψ(d+1)
        ok(sc(2, Zop(l, d)) == sub(Psi(l, d), Psi(l, d + 1)), ("2Z = Psi d - Psi d+1", l, d))

# ---------- a² = 1 and aτ = τa on T(λ) (all centres), λ ≤ 12 ----------
for lam in range(0, 13):
    _, W, Fm = L.lat(lam); n = len(W)
    for c in range(-2, lam + 6):
        E, _ = L.expF(lam, lam + 3)
        a = [[(-1) ** abs((c - W[i]) // 2) * E[i][j] for j in range(n)] for i in range(n)]
        tau = [[Fm[i][j] + (c - W[i] if i == j else 0) for j in range(n)] for i in range(n)]
        ok(mm(a, a) == eye(n), ("a^2=1", lam, c))
        ok(mm(a, tau) == mm(tau, a), ("a tau = tau a", lam, c))

# ---------- (F) freeness and the circulant matrix on Φ(N), odd centres 2d+1 ----------
for l in range(0, LMAX):
    W, Fm, pows, Ch, Sh, Shi, H, n = ops(l)
    lam = 2 * l + 1
    _, Wl, Fl = L.lat(lam); m = len(Wl)
    for d in range(l, l + 4):
        c = 2 * d + 1
        E, _ = L.expF(lam, lam + 3)
        a = [[(-1) ** abs((c - Wl[i]) // 2) * E[i][j] for j in range(m)] for i in range(m)]
        tau = [[Fl[i][j] + (c - Wl[i] if i == j else 0) for j in range(m)] for i in range(m)]
        b0 = [[Fraction(int(i == j)) for j in range(n)] for i in range(m)]   # bvec 0 : N → Φ(N)
        beta = [b0[i] + mm(a, b0)[i] for i in range(m)]                     # (x, y) ↦ b0 x + a b0 y
        Bi = L.to_int(beta)
        ok(Bi is not None and L.smith2(Bi, m, m) == [], ("beta invertible over Z_2", l, d))
        P = add(sub(sc(2 * d, eye(n)), sc(2, H)), mm(Ch, Shi))
        Q = sc(-1, mm(Sop(W, d), Shi))
        circ = [P[i] + Q[i] for i in range(n)] + [Q[i] + P[i] for i in range(n)]
        ok(mm(tau, beta) == mm(beta, circ), ("tau circulant", l, d))
        ok(add(P, Q) == Psi(l, d), ("P+Q = Psi", l, d))

# ---------- Lemma 10.4(a): X̄(2l+1, j) ≅ coker Ψ(l+j) on T(l) ----------
for l in range(0, LMAX + 1):
    for j in range(0, 5):
        lam = 2 * l + 1; c = lam + 2 * j
        ok(L.xbar(lam, c, lam + 2 * j + 1) == smith_sq(Psi(l, l + j)), ("10.4a", l, j))
        ok(L.xbar(lam, c, 2 * l + 2) == smith_sq(Psi(l, l + j)), ("10.4a minimal B", l, j))

# ---------- Lemma 10.5(a): X̄(2l+2, i) ≅ coker glue(Ψ(d+1), Ψ(d), Z(d)), d = l+i ----------
for l in range(0, LMAX):
    for i in range(0, 5):
        lam = 2 * l + 2; c = lam + 2 * i; d = l + i
        G = glue(Psi(l, d + 1), Psi(l, d), Zop(l, d))
        ok(L.xbar(lam, c, lam + 2 * i + 1) == smith_sq(G), ("10.5a", l, i))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0
# 1. wrong sign in Ψ (sign of d+1)
if any(L.xbar(2 * l + 1, 2 * l + 1 + 2 * j, 2 * l + 2 * j + 2) != smith_sq(Psi(l, l + j, sign_shift=1)) for l in range(1, 5) for j in range(3)): fired += 1
# 2. Ψ without the −2H term
if any(L.xbar(2 * l + 1, 2 * l + 1 + 2 * j, 2 * l + 2 * j + 2) != smith_sq(Psi(l, l + j, dropH=True)) for l in range(1, 5) for j in range(3)): fired += 1
# 3. glue with the lower-left block dropped
if any(L.xbar(2 * l + 2, 2 * l + 2 + 2 * i, 2 * l + 2 * i + 3) != smith_sq(glue(Psi(l, l + i + 1), Psi(l, l + i), sc(0, Zop(l, l + i)))) for l in range(0, 4) for i in range(3)): fired += 1
# 4. odd family at the wrong d (l + j + 1)
if any(L.xbar(2 * l + 1, 2 * l + 1 + 2 * j, 2 * l + 2 * j + 2) != smith_sq(Psi(l, l + j + 1)) for l in range(1, 5) for j in range(3)): fired += 1
print("controls fired", fired, "of 4")
