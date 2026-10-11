#!/usr/bin/env python3
"""Brute force for Lean piece C50b (paper v8 §10.7, Lemma 10.18: the dance modulo 2).
Grepy Escribano, 10 Oct 2026. Coefficient functions Γ(Δ, m, y) of covariant systems (C47/C48),
exact rationals with odd denominators. Claims:
 (K1) a K-function y ↦ a + 2 p(2y)/q(2y) (p(0) = 0, q(0) odd) is constant modulo 4;
 (K2) prodFun modulo 4 is the product of RA(Z/4) (values at 0, shifts invisible);
 (R2) in RA(Z/4), (β*β)(Δ,q) is even except at (∅,0);
 (M2) Good Γ, Good Γ'', Γ ≡ Γ'' mod 2 ⇒ schurG h Γ ≡ schurG h Γ'' mod 4 (so the next levels are ≡ mod 2);
 (DANCE) along every word of length ≤ 3 (twists and V-splits), the two dances stay ≡ mod 2.
Controls must fire."""
import random, itertools
from fractions import Fraction as Fr
from math import comb
random.seed(50102)
cnt = {}; fails = []; ctrl = {}
def ok(name, cond, info=None):
    cnt[name] = cnt.get(name, 0) + 1
    if not cond: fails.append((name, info))
def fire(name, cond):
    ctrl[name] = ctrl.get(name, 0) + (1 if cond else 0)
def dfact2(n):
    r = 1
    while n > 1: r *= n; n -= 2
    return r
def dfi(s): return Fr(1, dfact2(2 * s - 1)) if s > 0 else Fr(1)
def oS(D): return sum(2 ** t for t in D)
def ev2(x): return x.denominator % 2 == 1
def mod(x, M):   # x a 2-adic integer (odd denominator): residue mod M
    assert ev2(x); return (x.numerator * pow(x.denominator, -1, M)) % M
def divisible(x, M): return ev2(x) and mod(x, M) == 0

class KF:   # a + 2 p(2y)/q(2y)
    def __init__(s, a, p, q): s.a, s.p, s.q = Fr(a), [Fr(c) for c in p], [Fr(c) for c in q]
    def __call__(s, y):
        x = 2 * Fr(y); P = sum(c * x ** i for i, c in enumerate(s.p)); Q = sum(c * x ** i for i, c in enumerate(s.q))
        return s.a + 2 * P / Q
def rK(a=None, unit=False, mult=1):
    a = random.randint(-6, 6) if a is None else a
    if unit and a % 2 == 0: a += 1
    p = [0] + [random.randint(-3, 3) for _ in range(random.randint(0, 2))]
    q = [random.choice([1, -1, 3, 5])] + [random.randint(-3, 3) for _ in range(random.randint(0, 2))]
    f = KF(a, p, q)
    return (lambda y, f=f, mult=mult: mult * f(y))

def subsets(S):
    S = sorted(S); return [frozenset(c) for r in range(len(S) + 1) for c in itertools.combinations(S, r)]

class Sys:
    """coefficient functions Γ(Δ, m, y), with a memo."""
    def __init__(s, f): s.f = f; s.memo = {}
    def __call__(s, D, m, y):
        k = (D, m, y)
        if k not in s.memo: s.memo[k] = s.f(D, m, y)
        return s.memo[k]
def prodFun(k, G, H):
    def f(D, m, y):
        tot = Fr(0)
        for D1 in subsets(D):
            for a in range(m + 1):
                tot += comb(m, a) * G(D1, a, y) * H(D - D1, m - a, y - a * 2 ** k - oS(D1))
        return tot
    return Sys(f)
def rinv(k, G):
    S = Sys(None)
    def f(D, m, y):
        tot = Fr(1 if (not D and m == 0) else 0)
        for D1 in subsets(D):
            for a in range(m + 1):
                if not D1 and a == 0: continue
                tot -= comb(m, a) * G(D1, a, y) * S(D - D1, m - a, y - a * 2 ** k - oS(D1))
        return tot / G(frozenset(), 0, y)
    S.f = f; return S
def GB(G): return Sys(lambda D, q, y: dfi(q) * G(D, 2 * q, y))
def GC(h, G): return Sys(lambda D, q, y: dfi(q) * G(D, 2 * q, y + 2 ** h))
def GP(h, G): return Sys(lambda D, q, y: dfi(q + 1) * G(D, 2 * q + 1, y + 2 ** h))
def GD(G): return Sys(lambda D, q, y: Fr(0) if q == 0 else (2 * (q - 1) + 2) * dfi(q) * G(D, 2 * (q - 1) + 1, y))
def schurG(h, G):
    Q = rinv(h + 1, GP(h, G)); T = prodFun(h + 1, prodFun(h + 1, GB(G), Q), GC(h, G)); Dd = GD(G)
    return Sys(lambda D, m, y: Dd(D, m, y) - T(D, m, y))
def half(S): return Sys(lambda D, m, y: S(D, m, y) / 2)
def vsplitG(h, G): return Sys(lambda D, m, y: G(D - {h}, m + 1, y) if h in D else G(D, m, y))

def randGood(P, Mmax, payment_mult=4):
    tab = {}
    for D in subsets(P):
        for m in range(Mmax + 1):
            if not D and m == 0: tab[(D, m)] = rK(mult=payment_mult)
            elif not D and m == 1: tab[(D, m)] = rK(unit=True)
            else: tab[(D, m)] = rK()
    return tab
def toSys(tab): return Sys(lambda D, m, y: tab[(D, m)](y))
def partner(tab, P, Mmax, step=2):
    """Γ'' = Γ + step·E with E a K-function; at (∅,0) E is 2·K so the payment stays ≡ 0 mod 4."""
    t2 = {}
    for (D, m), f in tab.items():
        E = rK(mult=(2 if (not D and m == 0) else 1))
        st = 2 if (not D and m in (0, 1)) else step   # keep Good: payment ≡ 0 mod 4, F-coefficient a unit
        t2[(D, m)] = (lambda y, f=f, E=E, st=st: f(y) + st * E(y))
    return t2

YS = range(-3, 4)
# (K1), (K2)
for trial in range(60):
    f = rK(); ok("K1", all(mod(f(y) - f(0), 4) == 0 for y in YS))
    P = [0, 1]; G = toSys(randGood(P, 4)); H = toSys(randGood(P, 4)); k = random.randint(0, 2)
    PF = prodFun(k, G, H)
    for D in subsets(P):
        for m in range(4):
            ring = sum(comb(m, a) * mod(G(D1, a, 0), 4) * mod(H(D - D1, m - a, 0), 4)
                       for D1 in subsets(D) for a in range(m + 1)) % 4
            ok("K2", all(mod(PF(D, m, y), 4) == ring for y in (-2, 0, 3)))
# (R2) in RA(Z/4)
for trial in range(200):
    P = [0, 1, 2]; beta = {(D, q): random.randrange(4) for D in subsets(P) for q in range(6)}
    for D in subsets(P):
        for q in range(6):
            sq = sum(comb(q, a) * beta[(D1, a)] * beta[(D - D1, q - a)] for D1 in subsets(D) for a in range(q + 1)) % 4
            exp = (beta[(frozenset(), 0)] ** 2) % 4 if (not D and q == 0) else 0
            ok("R2", (sq - exp) % 2 == 0)
# (M2) and the dance
def dance_check(word, P0, Mmax, mode="good", levels=99):
    """returns (all congruences mod 2 hold, schur mod 4 holds) along the word."""
    payment = 4 if mode != "oddpay" else 1
    tab = randGood(P0, Mmax, payment_mult=payment)
    tab2 = partner(tab, P0, Mmax, step=(1 if mode == "notcong" else 2))
    if mode == "nonK":
        tab = dict(tab); key = (frozenset(), 2)
        tab[key] = (lambda y: Fr(2) * y + 1)          # values not constant mod 4
    G, H = toSys(tab), toSys(tab2); P = set(P0); h = 0; Mcur = Mmax; good = True
    for d in word:
        if d:
            G, H = vsplitG(h, G), vsplitG(h, H); P = P | {h}; Mcur -= 1
        SG, SH = schurG(h, G), schurG(h, H)
        Mcur = (Mcur - 1) // 2
        if Mcur < 0: break
        for D in subsets(P):
            for m in range(Mcur + 1):
                for y in (-1, 0, 2):
                    a, b = SG(D, m, y), SH(D, m, y)
                    if mode == "good": cnt["M2-entries"] = cnt.get("M2-entries", 0) + 1
                    if not (divisible(a - b, 4)): good = False
        G, H = half(SG), half(SH); h += 1
        levels -= 1
        if levels == 0: break
    return good

for word in [(False,), (True,), (False, False), (False, True), (True, False), (True, True), (False, True, False)]:
    for trial in range(4):
        ok("M2-dance", dance_check(word, [], 11), word)
        fire("ctl-notcong", not dance_check(word, [], 9, mode="notcong", levels=1))
        fire("ctl-oddpay", not dance_check(word, [], 9, mode="oddpay", levels=1))
        fire("ctl-nonK", not dance_check(word, [], 9, mode="nonK", levels=1))
# Good is kept: payment of the next level ≡ 0 mod 8 (W5), coefficient of F a unit (sanity of the generator)
for trial in range(20):
    G = toSys(randGood([], 9)); S = schurG(0, G)
    ok("W5-sanity", all(divisible(S(frozenset(), 0, y), 16) and ev2(S(frozenset(), 1, y) / 2) and mod(S(frozenset(), 1, y) / 2, 2) == 1 for y in YS))

tot = sum(cnt.values())
print("COUNTS", cnt)
print("TOTAL", tot, "FAILURES", len(fails), fails[:5])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
