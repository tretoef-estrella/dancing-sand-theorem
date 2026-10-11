#!/usr/bin/env python3
"""Brute force for piece C35 (the podium arithmetic, paper v8 §9.2). Grepy Escribano, 8 Oct 2026.
Written from §9.2 and the Rulers definitions of C3 only:
  family (k, I), I ⊆ [0,k); K = 2^k; λ + 1 = K + o_I; next(t) = min{u ∈ I ∪ {k} : u > t}, h_t = next(t) − t;
  ψ(E) = Σ_{t∈E}(h_t − 2^t); P_l = the l smallest elements of I (0 ≤ l ≤ s = |I|); Y_l = K + o(I ∖ P_l);
  φ(x) = x + v2(x); κ(a, b) = s2(a) + s2(b) − s2(a + b); clear(N, q) = 2^q ⌊N/2^q⌋;
  clock (C3): u_i(D) = φ(ξ) + κ(i + o_D − 1, ξ) + h(D), ξ = λ + 1 − 2 o_D (truncated subtraction as in Lean).
Checks:
  (a) φ(λ+1) + ψ(P_l) = φ(Y_l); v2(Y_l) = t_{l+1} (t_{s+1} = k).
  (b) for 1 ≤ y ≤ N there is q with clear(N,q) ≥ 1 and φ(y) ≤ φ(clear(N,q)); clearings ≤ N.
  (c) {Y_l : l ≤ s} = {clear(λ+1, q) : clear ≥ 1}; Y_1 ≥ Y_l for l ≥ 1; and the clearings of Y_1 that are ≥ 1
      are exactly {Y_l : 1 ≤ l ≤ s}.
  (K9.5) for a ≥ 0, B ≥ 1, q ≥ 0 there is y in [1, 2^q(a+B)] with φ(2^q B) + κ(a,B) ≤ φ(y).
  (M1) for i ≥ 1, m = i − 1, D ⊆ I: u_i(D) = φ(λ+1) + 2ψ(D) + κ(m, K + o(I∖D)) − κ(m, o_D).
  (M2) Σ_{D ⊆ P_l} u_i(D) = Σ_{D ⊆ P_l} [φ(Y_l) + κ(m, Y_l + o_D) − κ(m, o_D)].
  (M3) for 2^q | Y, o < 2^q: κ(m, Y + o) − κ(m, o) = κ(⌊m/2^q⌋ + [m mod 2^q + o ≥ 2^q], Y/2^q).
  (K) for l ≤ s, D ⊆ P_l: φ(Y_l) + κ(m, Y_l + o_D) − κ(m, o_D) ≤ φ(y) for some y in [1, λ + 1 + m].
Controls (each must fire): (a) with φ(λ) in place of φ(λ+1); (b) «the maximum is at N itself»; (M1) without the factor 2 on ψ; (K) with the range [1, λ + m]."""
import itertools, random
checks = 0; fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)
def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def s2(x): return bin(x).count("1")
def kap(a, b): return s2(a) + s2(b) - s2(a + b)
def phi(x): return x + v2(x)
def clear(N, q): return (N >> q) << q
def oE(E): return sum(2 ** t for t in E)

def fam(k, I):
    I = sorted(I)
    nxt = lambda t: min([u for u in I + [k] if u > t])
    h = {t: nxt(t) - t for t in I}
    lam1 = 2 ** k + oE(I)
    psi = lambda E: sum(h[t] - 2 ** t for t in E)
    P = [I[:l] for l in range(len(I) + 1)]
    Y = [2 ** k + oE([t for t in I if t not in P[l]]) for l in range(len(I) + 1)]
    return I, h, lam1, psi, P, Y
def clock(k, I, h, lam1, i, D):
    xi = max(lam1 - 2 * oE(D), 0)
    a = max(i + oE(D) - 1, 0)
    return phi(xi) + kap(a, xi) + sum(h[t] for t in D)

ctrl = {"a": 0, "b": 0, "M1": 0, "K": 0}
for k in range(1, 8):
    for r in range(k + 1):
        for I in itertools.combinations(range(k), r):
            I, h, lam1, psi, P, Y = fam(k, I)
            s = len(I); ts = I + [k]
            for l in range(s + 1):
                ok(phi(lam1) + psi(P[l]) == phi(Y[l]), ("a", k, I, l))
                ok(v2(Y[l]) == ts[l], ("v2Y", k, I, l))
                if lam1 - 1 >= 1 and phi(lam1 - 1) + psi(P[l]) != phi(Y[l]): ctrl["a"] = 1
            clr = {clear(lam1, q) for q in range(lam1.bit_length() + 1) if clear(lam1, q) >= 1}
            ok(clr == set(Y), ("c", k, I))
            if s >= 1:
                ok(all(Y[1] >= Y[l] for l in range(1, s + 1)), ("Y1max", k, I))
                c1 = {clear(Y[1], q) for q in range(Y[1].bit_length() + 1) if clear(Y[1], q) >= 1}
                ok(c1 == set(Y[1:]), ("c1", k, I))
            for i in range(1, 9):
                m = i - 1
                for rr in range(s + 1):
                    for D in itertools.combinations(I, rr):
                        E = [t for t in I if t not in D]
                        u = clock(k, I, h, lam1, i, D)
                        rhs = phi(lam1) + 2 * psi(D) + kap(m, 2 ** k + oE(E)) - kap(m, oE(D))
                        ok(u == rhs, ("M1", k, I, i, D))
                        if u != phi(lam1) + psi(D) + kap(m, 2 ** k + oE(E)) - kap(m, oE(D)): ctrl["M1"] = 1
                for l in range(s + 1):
                    subs = [D for rr in range(l + 1) for D in itertools.combinations(P[l], rr)]
                    L = sum(clock(k, I, h, lam1, i, D) for D in subs)
                    R = sum(phi(Y[l]) + kap(m, Y[l] + oE(D)) - kap(m, oE(D)) for D in subs)
                    ok(L == R, ("M2", k, I, i, l))
                    for D in subs:
                        val = phi(Y[l]) + kap(m, Y[l] + oE(D)) - kap(m, oE(D))
                        best = max(phi(y) for y in range(1, lam1 + m + 1))
                        ok(val <= best, ("K", k, I, i, l, D))
                        if lam1 + m - 1 >= 1 and val > max(phi(y) for y in range(1, lam1 + m)): ctrl["K"] = 1
for N in range(1, 600):
    cl = [clear(N, q) for q in range(N.bit_length() + 1) if clear(N, q) >= 1]
    ok(all(c <= N for c in cl), ("clear<=N", N))
    for y in range(1, N + 1):
        ok(any(phi(y) <= phi(c) for c in cl), ("b", N, y))
        if phi(y) > phi(N): ctrl["b"] = 1
for Y in range(1, 200):
    for q in range(0, 6):
        if Y % (2 ** q): continue
        for o in range(2 ** q):
            for m in range(0, 300, 7):
                L = kap(m, Y + o) - kap(m, o)
                R = kap(m // 2 ** q + (1 if m % 2 ** q + o >= 2 ** q else 0), Y // 2 ** q)
                ok(L == R, ("M3", Y, q, o, m))
for a in range(0, 70):
    for B in range(1, 70):
        for q in range(0, 4):
            ok(any(phi(2 ** q * B) + kap(a, B) <= phi(y) for y in range(1, 2 ** q * (a + B) + 1)), ("L95", a, B, q))
print("checks", checks, "fails", fails)
print("controls fired", sum(ctrl.values()), "of", len(ctrl), ctrl)
