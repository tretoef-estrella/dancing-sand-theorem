#!/usr/bin/env python3
"""Brute force for piece C35b (Propositions 9.3, 9.4, 9.6 of paper v8). Grepy Escribano, 8 Oct 2026.
Pooled big clocks as in chkC33 (§1.2): raw u_i(D) = φ(ξ) + κ(i + o_D − 1, ξ) + h(D), ξ = λ + 1 − 2 o_D,
dancers in o-order (dancer of rank p = bits of p placed on I), integer PAVA fit; shift 0: dancers 1..N−1.
Y_l = λ + 1 − o_{P_l}, P_l = l smallest of I.
Checks:
 (9.3a) yPool(λ, 1)[0] = max_{0≤l≤s} φ(Y_l);  (9.3b) yPool(λ,1)[p] ≤ max_{1≤l≤s} φ(Y_l) for p ≥ 1 (s ≥ 1);
 (9.3c) 0 ∈ I ⟹ yPool(λ,1)[1] = max_{1≤l≤s} φ(Y_l)  (dancer of rank 1 = {t_1} = {0});
 (9.4a) s ≥ 1: yPool0(λ)[0] (dancer {t_1}) = max(φ(Y_1) − 2^{t_1}, max_{2≤l≤s} φ(Y_l));
 (9.4b) s ≥ 2: yPool0(λ)[q] ≤ max_{2≤l≤s} φ(Y_l) for q ≥ 1;
 (9.6) i ≥ 1: yPool(λ, i)[p] ≤ max_{1≤y≤λ+i} φ(y) for every p;
 (H) i ≥ 1: the first level set of the real fit is {D : D ⊆ P_l} for some l, i.e. positions 0..2^l − 1,
     and the first pooled value equals the mean of u_i over D ⊆ P_l.
Controls: (9.3a) with max over l ≥ 1; (9.4a) without the −2^{t_1}; (9.6) with the range [1, λ + i − 1];
(H) «the first level set is always a single dancer»."""
from fractions import Fraction
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
def family(lam):
    x = lam + 1; k = x.bit_length() - 1
    return k, [t for t in range(k) if (x >> t) & 1]
def dancers(I): return [[I[j] for j in range(len(I)) if (p >> j) & 1] for p in range(2 ** len(I))]
def raw(lam, i, D, I, k):
    nxt = lambda t: min([u for u in I + [k] if u > t])
    o = sum(2 ** t for t in D); xi = lam + 1 - 2 * o
    return phi(xi) + kap(max(i + o - 1, 0), xi) + sum(nxt(t) - t for t in D)
def pava(xs):
    blocks = []
    for x in xs:
        blocks.append([x, 1])
        while len(blocks) > 1 and Fraction(blocks[-2][0], blocks[-2][1]) <= Fraction(blocks[-1][0], blocks[-1][1]):
            s, c = blocks.pop(); blocks[-1][0] += s; blocks[-1][1] += c
    return blocks
def pint(blocks):
    out = []
    for s, p in blocks:
        q, r = divmod(s, p); out += [q + 1] * r + [q] * (p - r)
    return out
ctrl = {"a": 0, "4a": 0, "6": 0, "H": 0}
NEG = float("-inf")
for lam in range(1, 1100):
    k, I = family(lam); s = len(I)
    P = [I[:l] for l in range(s + 1)]
    Y = [lam + 1 - sum(2 ** t for t in P[l]) for l in range(s + 1)]
    Ds = dancers(I)
    for i in range(1, 9):
        u = [raw(lam, i, D, I, k) for D in Ds]
        bl = pava(u); e = pint(bl)
        if i == 1:
            ok(e[0] == max(phi(y) for y in Y), ("9.3a", lam))
            if s >= 1:
                M1 = max(phi(y) for y in Y[1:])
                ok(all(e[p] <= M1 for p in range(1, len(e))), ("9.3b", lam))
                if e[0] != M1: ctrl["a"] = 1
                if 0 in I: ok(e[1] == M1, ("9.3c", lam))
        best = max(phi(y) for y in range(1, lam + i + 1))
        ok(all(x <= best for x in e), ("9.6", lam, i))
        if lam + i - 1 >= 1 and any(x > max(phi(y) for y in range(1, lam + i)) for x in e): ctrl["6"] = 1
        c = bl[0][1]
        ok(c & (c - 1) == 0 and c <= 2 ** s and Fraction(bl[0][0], c) == Fraction(sum(u[:c]), c), ("H", lam, i))
        if c > 1: ctrl["H"] = 1
    if s >= 1:
        u0 = [raw(lam, 0, D, I, k) for D in Ds[1:]]
        e0 = pint(pava(u0))
        t1 = I[0]
        A = max([phi(y) for y in Y[2:]], default=NEG)
        ok(e0[0] == max(phi(Y[1]) - 2 ** t1, A), ("9.4a", lam))
        if e0[0] != max(phi(Y[1]), A): ctrl["4a"] = 1
        if s >= 2: ok(all(x <= A for x in e0[1:]), ("9.4b", lam))
print("checks", checks, "fails", fails)
print("controls fired", sum(ctrl.values()), "of", len(ctrl), ctrl)
