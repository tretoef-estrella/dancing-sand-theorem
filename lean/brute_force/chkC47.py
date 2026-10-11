#!/usr/bin/env python3
"""Brute force for Lean piece C47 (paper v8 §10.5: Lemmas 10.13 and 10.14), in the rational form of
the ring 𝒦 used by the piece: functions y ↦ a + 2·p(2y)/q(2y), p(0) = 0, q(0) odd.
Elements of ℤ_2 are exact rationals with odd denominators. Grepy Escribano, 9 Oct 2026."""
import random, itertools
from fractions import Fraction as Fr
random.seed(4701)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)
fired = {}
def fire(name, c): fired[name] = fired.get(name, False) or c
def v2(x):
    x = Fr(x)
    if x == 0: return 10 ** 9
    n, d = abs(x.numerator), x.denominator; v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
def rz():  # random 2-adic integer
    return Fr(random.randint(-9, 9), random.choice([1, 3, 5, 7]))
def rodd(): return Fr(random.choice([1, 3, 5, -1, -3, 7]), random.choice([1, 3, 5]))
# polynomials: lists of Fractions, low degree first
def padd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pneg(p): return [-x for x in p]
def pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1) if p and q else [Fr(0)]
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i + j] += x * y
    return r
def pc(c): return [Fr(c)]
def pev(p, x): return sum(c * Fr(x) ** i for i, c in enumerate(p))
def pcomp_shift(p, s):  # p(X + s)
    r = [Fr(0)]
    for i, c in enumerate(p):
        term = [Fr(1)]
        for _ in range(i): term = pmul(term, [Fr(s), Fr(1)])
        r = padd(r, [c * t for t in term])
    return r
# representations (a, p, q)
def rrep():
    p = [Fr(0)] + [rz() for _ in range(random.randint(0, 3))]
    q = [rodd()] + [rz() for _ in range(random.randint(0, 2))]
    return (rz(), p, q)
def ev(r, y):
    a, p, q = r; qq = pev(q, 2 * Fr(y)); assert v2(qq) == 0
    return a + 2 * pev(p, 2 * Fr(y)) / qq
def r_add(r, s):
    (a, p, q), (b, pp, qq) = r, s
    return (a + b, padd(pmul(p, qq), pmul(pp, q)), pmul(q, qq))
def r_mul(r, s):
    (a, p, q), (b, pp, qq) = r, s
    num = padd(padd([a * x for x in pmul(pp, q)], [b * x for x in pmul(p, qq)]), [2 * x for x in pmul(p, pp)])
    return (a * b, num, pmul(q, qq))
def r_shift(r, e):  # y ↦ ϑ(y − e)
    a, p, q = r
    pe, qe = pev(p, -2 * Fr(e)), pev(q, -2 * Fr(e))
    ps, qs = pcomp_shift(p, -2 * Fr(e)), pcomp_shift(q, -2 * Fr(e))
    return (a + 2 * pe / qe, padd([qe * x for x in ps], [-pe * x for x in qs]), [qe * x for x in qs])
def r_inv(r):
    a, p, q = r
    return (1 / a, pneg(p), [a * x for x in padd([a * x for x in q], [2 * x for x in p])])
def is_rep(r):
    a, p, q = r
    return all(v2(x) >= 0 for x in [a] + p + q) and p[0] == 0 and v2(q[0]) == 0
# Θ: (ā, p̄·q̄⁻¹ mod X^D) with coefficients in F_2
DT = 8
def red(x):
    assert v2(x) >= 0; return (Fr(x).numerator * pow(Fr(x).denominator, -1, 2)) % 2
def ser_inv2(q):
    q = [red(x) for x in q] + [0] * DT; assert q[0] == 1
    inv = [0] * DT; inv[0] = 1
    for n in range(1, DT):
        inv[n] = sum(q[k] * inv[n - k] for k in range(1, n + 1)) % 2
    return inv
def ser_mul2(s, t): return [sum(s[k] * t[n - k] for k in range(n + 1)) % 2 for n in range(DT)]
def theta(r):
    a, p, q = r
    pr = [red(x) for x in p] + [0] * DT
    return (red(a), tuple(ser_mul2(pr[:DT], ser_inv2(q))))
def s_mul(x, y): return ((x[0] * y[0]) % 2, tuple((x[0] * b + y[0] * c) % 2 for b, c in zip(y[1], x[1])))
def s_add(x, y): return ((x[0] + y[0]) % 2, tuple((b + c) % 2 for b, c in zip(x[1], y[1])))
S0 = (0, tuple([0] * DT)); S1 = (1, tuple([0] * DT))
ys = [Fr(random.randint(-20, 20), random.choice([1, 3, 5, 7])) for _ in range(6)]
# ---------- Part K, S ----------
for trial in range(300):
    r, s = rrep(), rrep(); e = rz()
    for name, t, f in (("add", r_add(r, s), lambda y: ev(r, y) + ev(s, y)),
                       ("mul", r_mul(r, s), lambda y: ev(r, y) * ev(s, y)),
                       ("shift", r_shift(r, e), lambda y: ev(r, y - e))):
        ok(is_rep(t), ("K rep", name, trial))
        ok(all(ev(t, y) == f(y) for y in ys), ("K value", name, trial))
    if v2(r[0]) == 0:
        t = r_inv(r); ok(is_rep(t) and all(ev(t, y) * ev(r, y) == 1 for y in ys), ("K5 inverse", trial))
        ok(s_mul(theta(t), theta(r)) == S1, ("S theta of inverse", trial))
    ok(all(v2(ev(r, y) - r[0]) >= 2 for y in ys), ("K6 values = a mod 4", trial))
    ok(theta(r_mul(r, s)) == s_mul(theta(r), theta(s)), ("S1 theta multiplicative", trial))
    ok(theta(r_add(r, s)) == s_add(theta(r), theta(s)), ("S1 theta additive", trial))
    ok(theta(r_shift(r, e)) == theta(r), ("S1 theta shift-invariant", trial))
    # well defined: another representation of the same function
    u = [rodd()] + [rz() for _ in range(2)]
    r2 = (r[0], pmul(r[1], u), pmul(r[2], u))
    ok(all(ev(r2, y) == ev(r, y) for y in ys) and theta(r2) == theta(r), ("S0 theta well defined", trial))
    # kernel: a even and p even => ϑ/2 in the class
    rk = (2 * r[0], [2 * x for x in r[1]], r[2])
    ok(theta(rk) == S0 and is_rep((rk[0] / 2, [x / 2 for x in rk[1]], rk[2])), ("S kernel", trial))
    # controls
    rb = (r[0], [Fr(1)] + r[1][1:], r[2])  # p(0) = 1: not in the class
    fire("p(0) != 0 breaks the mod-4 property", not all(v2(ev(rb, y) - rb[0]) >= 2 for y in ys))
    thbad = lambda rr: (red(rr[0]), tuple(([red(x) for x in rr[1]] + [0] * DT)[:DT]))
    fire("Θ without q̄⁻¹ is not multiplicative", thbad(r_mul(r, s)) != s_mul(thbad(r), thbad(s)))
# ---------- Part R: R_S and β² = β₀² ----------
P = [0, 1, 3]
subsets = [frozenset(c) for k in range(len(P) + 1) for c in itertools.combinations(P, k)]
QM = 5
from math import comb
def rs_rand():
    return {(D, q): (random.randint(0, 1), tuple(random.randint(0, 1) for _ in range(DT))) for D in subsets for q in range(QM)}
def rs_mul(b, g, ch=2, disjoint=True):
    out = {}
    for D in subsets:
        for q in range(QM):
            acc = S0
            for D1 in subsets:
                if not D1 <= D: continue
                D2 = D - D1
                for a in range(q + 1):
                    c = comb(q, a) % 2
                    if c: acc = s_add(acc, s_mul(b[(D1, a)], g[(D2, q - a)]))
            out[(D, q)] = acc
    return out
for trial in range(40):
    b = rs_rand(); g = rs_rand(); h_ = rs_rand()
    ok(rs_mul(b, g) == rs_mul(g, b), ("R1 commutative", trial))
    ok(rs_mul(rs_mul(b, g), h_) == rs_mul(b, rs_mul(g, h_)), ("R1 associative", trial))
    sq = rs_mul(b, b)
    ok(all(sq[(D, q)] == (s_mul(b[(frozenset(), 0)], b[(frozenset(), 0)]) if (not D and q == 0) else S0)
           for D in subsets for q in range(QM)), ("R2 beta^2 = beta_0^2", trial))
# control: allow overlapping Δ1, Δ2 (no E_t² = 0): β² ≠ β₀² for some β
def rs_mul_overlap(b, g):
    out = {}
    for D in subsets:
        for q in range(QM):
            acc = S0
            for D1 in subsets:
                for D2 in subsets:
                    if D1 | D2 != D: continue
                    for a in range(q + 1):
                        if comb(q, a) % 2: acc = s_add(acc, s_mul(b[(D1, a)], g[(D2, q - a)]))
            out[(D, q)] = acc
    return out
for trial in range(10):
    b = rs_rand(); sq = rs_mul_overlap(b, b)
    fire("without E_t^2 = 0 the square is not beta_0^2", any(sq[(D, q)] != S0 for D in subsets for q in range(QM) if D or q))
# ---------- Part T: covariant systems ----------
def o(D): return sum(2 ** t for t in D)
FL = range(-3, 9); MM = 4
def cov(Gam, h, c, Ps):
    sub = [frozenset(x) for k in range(len(Ps) + 1) for x in itertools.combinations(Ps, k)]
    return {(D, D2, m, f): (ev(Gam[(D - D2, m)], 2 ** h * f + o(D) + c) if D2 <= D else Fr(0))
            for D in sub for D2 in sub for m in range(MM) for f in FL}, sub
for trial in range(25):
    Ps = random.choice([[0], [0, 1], [1, 2], [0, 2]]); h = random.choice([0, 1, 2, 3]); c = rz()
    sub = [frozenset(x) for k in range(len(Ps) + 1) for x in itertools.combinations(Ps, k)]
    G1 = {(D, m): rrep() for D in sub for m in range(MM)}
    G2 = {(D, m): rrep() for D in sub for m in range(MM)}
    A1, _ = cov(G1, h, c, Ps); A2, _ = cov(G2, h, c, Ps)
    # product in Bf, entry (D, D'), coefficient m at floor f (floors f - a must stay in FL)
    for D in sub:
        for D2 in sub:
            for m in range(MM):
                for f in range(0, 6):
                    lhs = sum(comb(m, a) * A1[(D, D1, a, f)] * A2[(D1, D2, m - a, f - a)]
                              for D1 in sub for a in range(m + 1))
                    if D2 <= D:
                        y = 2 ** h * f + o(D) + c; Dl = D - D2
                        rhs = sum(comb(m, a) * ev(G1[(Dl1, a)], y) * ev(G2[(Dl - Dl1, m - a)], y - a * 2 ** h - o(Dl1))
                                  for Dl1 in [frozenset(x) for k in range(len(Dl) + 1) for x in itertools.combinations(sorted(Dl), k)]
                                  for a in range(m + 1))
                        ok(lhs == rhs, ("T1 product formula", trial, D, D2, m, f))
                        bad = sum(comb(m, a) * ev(G1[(Dl1, a)], y) * ev(G2[(Dl - Dl1, m - a)], y - a * 2 ** h)
                                  for Dl1 in [frozenset(x) for k in range(len(Dl) + 1) for x in itertools.combinations(sorted(Dl), k)]
                                  for a in range(m + 1))
                        fire("position without -o(Δ1)", bad != lhs)
                    else:
                        ok(lhs == 0, ("T1 covariance", trial, D, D2, m, f))
    # Θ_h multiplicative: the product's functions as representations, then Θ
    prod = {}
    for Dl in sub:
        for m in range(MM):
            acc = (Fr(0), [Fr(0)], [Fr(1)])
            for Dl1 in [frozenset(x) for k in range(len(Dl) + 1) for x in itertools.combinations(sorted(Dl), k)]:
                for a in range(m + 1):
                    t = r_mul(G1[(Dl1, a)], r_shift(G2[(Dl - Dl1, m - a)], a * 2 ** h + o(Dl1)))
                    t = (comb(m, a) * t[0], [comb(m, a) * x for x in t[1]], t[2])
                    acc = r_add(acc, t)
            prod[(Dl, m)] = acc
            ok(is_rep(acc), ("T1 class closed", trial))
    for Dl in sub:
        for m in range(MM):
            acc = S0
            for Dl1 in [frozenset(x) for k in range(len(Dl) + 1) for x in itertools.combinations(sorted(Dl), k)]:
                for a in range(m + 1):
                    if comb(m, a) % 2: acc = s_add(acc, s_mul(theta(G1[(Dl1, a)]), theta(G2[(Dl - Dl1, m - a)])))
            ok(theta(prod[(Dl, m)]) == acc, ("T2 Theta_h multiplicative", trial, Dl, m))
print("checks", checks, "failures", fails)
print("controls fired", sum(fired.values()), "of", len(fired), fired)
