#!/usr/bin/env python3
"""Brute force for Lean piece C50c (paper v8 §10.7, Theorem 10.22: the arms of the even families).
Grepy Escribano, 10 Oct 2026. Exact rationals; a 2-adic integer is a rational with odd denominator.
Claims:
 (P2) PsiF i and PsiF (i+1) are the systems GPsi 0 i, GPsi (eI i) (i+1) at the positions c = (i+1)/2;
 (A1) the arms are congruent modulo 2;
 (H)  for a good system G and eps = +-1, prodFun h G (G + 2 eps u) is even; its half has payment = 0 mod 4,
      odd coefficient of F, and is constant modulo 4 in y (as a K-function must be);
 (C1) the halves U (from G1 with -2) and U' (from G0 with +2) are congruent modulo 2 when G1 = G0 (mod 2).
Controls must fire."""
import random, itertools, math
from fractions import Fraction as Fr
random.seed(5030)
cnt = {}; fails = []; ctrl = {}
def ok(name, cond, info=None):
    cnt[name] = cnt.get(name, 0) + 1
    if not cond: fails.append((name, info))
def fire(name, cond):
    ctrl[name] = ctrl.get(name, 0) + (1 if cond else 0)
def isint(x): return Fr(x).denominator % 2 == 1
def even(x): x = Fr(x); return isint(x) and isint(x / 2)
def mod4(x):
    x = Fr(x); assert isint(x)
    return (x.numerator * pow(x.denominator, -1, 4)) % 4

# ---- C49 coefficients
def dfi(m): return Fr(1, math.prod(range(1, 2 * m, 2)) if m > 0 else 1)
def chC(m): return dfi(m)
def shC(m): return dfi(m + 1)
shI = {0: Fr(1)}
def shInvC(m):
    if m not in shI:
        shI[m] = -sum(math.comb(m, b) * shC(m - b) * shInvC(b) for b in range(m))
    return shI[m]
def kJ(j, m):  # (KF j).coef m = sum_a C(m,a) (chC a - [a=0](-1)^j) shInvC(m-a)
    return sum(math.comb(m, a) * (chC(a) - (Fr((-1) ** j) if a == 0 else 0)) * shInvC(m - a) for a in range(m + 1))
def psiCoef(j, m, f):  # PsiF j = dg(4f + 2j) + KF j
    return (Fr(4 * f + 2 * j) if m == 0 else 0) + kJ(j, m)
def eI(i): return (i + 2) // 2 - (i + 1) // 2
def GPsi(e, j):
    def G(D, m, y):
        if D: return Fr(0)
        return Fr(4) * (y + e) if m == 0 else kJ(j, m)
    return G
def covEmpty(c, G, m, f): return G(frozenset(), m, Fr(f) + c)   # covSys ∅ 0 c G at (∅,∅)

for i in range(0, 12):
    c = (i + 1) // 2
    for m in range(0, 10):
        for f in (-3, 0, 2, 5):
            ok("P2-i", covEmpty(c, GPsi(0, i), m, f) == psiCoef(i, m, f), (i, m, f))
            ok("P2-i+1", covEmpty(c, GPsi(eI(i), i + 1), m, f) == psiCoef(i + 1, m, f), (i, m, f))
    fire("ctl-shift-wrong", covEmpty(c, GPsi(1 - eI(i), i + 1), 0, 0) != psiCoef(i + 1, 0, 0))
    ok("F-unit", not even(kJ(i, 1)) and isint(kJ(i, 1)))
    for m in range(0, 14):
        for y in (Fr(-2), Fr(0), Fr(3)):
            ok("A1", even(GPsi(eI(i), i + 1)(frozenset(), m, y) - GPsi(0, i)(frozenset(), m, y)), (i, m))
            ok("kJ-int", isint(kJ(i, m)))

# ---- systems
def oS(D): return sum(2 ** t for t in D)
def subsets(D):
    D = sorted(D)
    for r in range(len(D) + 1):
        for s in itertools.combinations(D, r): yield frozenset(s)
def prodFun(h, G, G2):
    def P(D, m, y):
        return sum(math.comb(m, a) * G(D1, a, y) * G2(D - D1, m - a, y - a * 2 ** h - oS(D1))
                   for D1 in subsets(D) for a in range(m + 1))
    return P
def u(D, m, y): return Fr(1) if (not D and m == 0) else Fr(0)
def addc(G, k):  # G + k • u
    return lambda D, m, y: G(D, m, y) + k * u(D, m, y)
def randK(a=None):
    if a is None: a = random.randint(-4, 4)
    p = [0] + [random.randint(-2, 2) for _ in range(2)]
    q = [random.choice([1, 3, -1, 5])] + [random.randint(-2, 2) for _ in range(2)]
    ev = lambda P, x: sum(cf * x ** k for k, cf in enumerate(P))
    return lambda y: Fr(a) + 2 * ev(p, 2 * y) / ev(q, 2 * y)
def randGood(payodd=False, nonK=False):
    tab = {}
    def G(D, m, y):
        key = (D, m)
        if key not in tab:
            if not D and m == 0: tab[key] = randK(4 * random.randint(-2, 2) + (1 if payodd else 0))
            elif not D and m == 1:
                tab[key] = (lambda y: 2 * y + 1) if nonK else randK(2 * random.randint(-2, 2) + 1)
            else: tab[key] = randK()
        return tab[key](y)
    return G
def randE():
    tab = {}
    def E(D, m, y):
        if (D, m) not in tab: tab[(D, m)] = randK()
        return tab[(D, m)](y)
    return E
Ds = [frozenset(), frozenset({0}), frozenset({1}), frozenset({0, 1})]
Ys = [Fr(-2), Fr(0), Fr(1), Fr(3)]

def checkH(G, h, eps, tag, record=True):
    rec = ok if record else (lambda *a, **k: None)
    P = prodFun(h, G, addc(G, 2 * eps)); good = True; konst = True
    for D in Ds:
        for m in range(0, 4):
            vals = [P(D, m, y) for y in Ys]
            if not all(even(v) for v in vals): good = False
            rec("H-even" + tag, all(even(v) for v in vals))
            halves = [v / 2 for v in vals]
            if all(isint(x) for x in halves):
                c4 = len({mod4(x) for x in halves}) == 1
                if not c4: konst = False
                rec("H-half-K-mod4" + tag, c4)
    rec("H-pay" + tag, all(even(P(frozenset(), 0, y) / 2) and mod4(P(frozenset(), 0, y) / 2) == 0 for y in Ys))
    rec("H-coefB" + tag, all(isint(P(frozenset(), 1, y) / 2) and not even(P(frozenset(), 1, y) / 2) for y in Ys))
    return good, konst

for trial in range(25):
    for h in (0, 1, 2):
        for eps in (1, -1):
            checkH(randGood(), h, eps, "")
for i in range(0, 6):
    for eps in (1, -1):
        checkH(GPsi(eI(i), i + 1), 0, eps, "-psi"); checkH(GPsi(0, i), 0, eps, "-psi")
for trial in range(12):
    fire("ctl-odd-payment", not checkH(randGood(payodd=True), 0, 1, "", record=False)[0])
    fire("ctl-nonK-half", not checkH(randGood(nonK=True), 0, 1, "", record=False)[1])

def checkC1(G0, G1, h, tag):
    P1 = prodFun(h, G1, addc(G1, -2)); P0 = prodFun(h, G0, addc(G0, 2)); allok = True
    for D in Ds:
        for m in range(0, 4):
            for y in Ys:
                d = (P1(D, m, y) - P0(D, m, y)) / 2   # = U - U'
                good = even(d)
                if not good: allok = False
                if tag is not None: ok("C1" + tag, good, (D, m))
    return allok
for trial in range(20):
    G0 = randGood(); E = randE()
    G1 = lambda D, m, y, G0=G0, E=E: G0(D, m, y) + 2 * E(D, m, y)
    for h in (0, 1):
        checkC1(G0, G1, h, "")
for i in range(0, 8):
    checkC1(GPsi(0, i), GPsi(eI(i), i + 1), 0, "-psi")
for trial in range(12):
    G0 = randGood(); E = randE()
    G1 = lambda D, m, y, G0=G0, E=E: G0(D, m, y) + E(D, m, y) + (0 if (not D and m < 2) else 0)
    # not congruent mod 2 (off (∅,0), (∅,1) only, so both stay good)
    G1b = lambda D, m, y, G0=G0, E=E: G0(D, m, y) + (E(D, m, y) if (D or m >= 2) else 2 * E(D, m, y))
    fire("ctl-not-congruent", not checkC1(G0, G1b, 0, None))
tot = sum(cnt.values())
print("COUNTS", cnt)
print("TOTAL", tot, "FAILURES", len(fails), fails[:5])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
