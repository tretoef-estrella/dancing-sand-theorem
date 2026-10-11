#!/usr/bin/env python3
"""Brute force for Lean piece C50d (paper v8 §10.7, Lemma 10.20: the bend). Grepy Escribano, 10 Oct 2026.
Reuses the definitions of chkC43.py (independent lattice model of T(l), exact rationals).
Claims:
 (Y1) Y = (Psi + t)^{-1}, Psi = XiOp(alpha, c, eta, zeta), ||t|| = 1/2, alpha >= 2, any c >= 0:
      v2(Y_L(f)) >= v2(L!) - (L + 1) for every L and f >= L.
 (W)  for nested final slots D' subset of D: oE(D \\ D') <= 2^k - 1.
 (B1) M_w(Psi) * N_t has every entry with v2 >= 1, N_t = 2^k O (Psi + t)^{-1} I, every l, alpha >= 2, c >= 1.
Controls must fire: alpha = 1; t = +-4; the bound v2 >= 2 in (B1); (Y1) with L instead of L + 1."""
import random, sys, math
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)
c43 = open('chkC43.py').read()
exec(c43[c43.index('def lattice_inverse_final'):c43.index('for l in range(0, 8):\n    for alpha in (2, 3):')])
random.seed(5040)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)
def vfact(n): return v2(math.factorial(n))

# ---------- (Y1) the bound on the inverse of Psi + t ----------
TS = [Fraction(2), Fraction(-2), Fraction(6), Fraction(2, 3), Fraction(-10, 7)]
for alpha in (2, 3, 4):
    for c in (0, 1, 2, 3, 6):
        for t in TS:
            for kind in ('const', 'var'):
                eta = random.choice([Fraction(1), Fraction(-1), Fraction(3), Fraction(1, 3), Fraction(-5, 3)])
                zc = {m: Fraction(random.randint(-6, 6), random.choice([1, 3, 5])) for m in range(2, 12)}
                zv = {(m, f): Fraction(random.randint(-6, 6), random.choice([1, 3])) for m in range(2, 12) for f in range(0, 30)}
                zeta = (lambda m, f, zc=zc: zc[m]) if kind == 'const' else (lambda m, f, zv=zv: zv[(m, f)])
                pi = lambda d, alpha=alpha, c=c, t=t: Fraction(2 ** alpha * (d + c)) + t
                Y = inverse_coefs(pi, eta, zeta, 9, 26)
                for LL in range(10):
                    for f in range(LL, 27):
                        ok(v2(Y[(LL, f)]) >= vfact(LL) - (LL + 1), ("Y1", alpha, c, t, kind, LL, f))

# ---------- (W) the window bound oE(D \ D') <= 2^k - 1 on nested slots ----------
for l in range(0, 64):
    ds = digits(l); k = len(ds); I = {t for t, d in enumerate(ds) if d}; m = len(I)
    Ds = [frozenset(dancers(ds, s)) for s in range(2 ** m)]
    for D in Ds:
        for D2 in Ds:
            if D2 <= D: ok(oE(D - D2) <= 2 ** k - 1, ("W", l, sorted(D), sorted(D2)))

# ---------- (B1) Lemma 10.20 on T(l) ----------
def mk_shift(pi0, t, eta, zeta):
    x = mk_op(pi0, eta, zeta)
    for f in range(FLO, FH):
        if f >= 0: x[(0, f)] += t
    return x
def minval(Mt):
    return min(v2(Mt[a][b]) for a in range(len(Mt)) for b in range(len(Mt)))
nontriv = 0; attained_one = 0; seen_l = set()
for l in range(0, 8):
    for alpha in (2, 3):
        for c in (1, 2, 3, 4):
            pi = lambda d, alpha=alpha, c=c: 2 ** alpha * (d + c)
            eta = random.choice([Fraction(1), Fraction(-1), Fraction(3), Fraction(1, 3)])
            for kind in ('const', 'var', 'zero'):
                zc = {m: random.randint(-6, 6) for m in range(2, MMAX)}
                zv = {(m, f): random.randint(-6, 6) for m in range(2, MMAX) for f in range(0, FH)}
                zeta = {'const': (lambda m, f, zc=zc: zc[m]), 'var': (lambda m, f, zv=zv: zv[(m, f)]),
                        'zero': (lambda m, f: 0)}[kind]
                Psi = mk_op(pi, eta, zeta)
                Mi, nf = lattice_inverse_final(l, Psi); MP = inv(Mi)
                for t in (Fraction(2), Fraction(-2), Fraction(6), Fraction(2, 3)):
                    Nt, _ = lattice_inverse_final(l, mk_shift(pi, t, eta, zeta))
                    Pr = mm(MP, Nt)
                    mv = minval(Pr)
                    ok(mv >= 1, ("B1", l, alpha, c, kind, t, mv))
                    if mv == 1: attained_one += 1
                    if any(Pr[a][b] != 0 for a in range(nf) for b in range(nf) if a != b): nontriv += 1
                    seen_l.add(l)
ok(attained_one > 0, ("B1: the bound 1 is attained", attained_one))
ok(nontriv > 0, ("B1: off-diagonal entries occur", nontriv))
ok(seen_l == set(range(8)), ("B1: every l tested", sorted(seen_l)))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = 0; tried = 0
def ctl(cond, name):
    global fired, tried
    tried += 1
    if cond: fired += 1
    else: print("control did not fire:", name)
# 1. alpha = 1: (B1) fails somewhere
bad = False
for l in range(1, 8):
    for c in (1, 2, 3):
        pi = lambda d, c=c: 2 * (d + c)
        Psi = mk_op(pi, 1, lambda m, f: 0)
        Mi, nf = lattice_inverse_final(l, Psi); MP = inv(Mi)
        Nt, _ = lattice_inverse_final(l, mk_shift(pi, Fraction(2), 1, lambda m, f: 0))
        if minval(mm(MP, Nt)) < 1: bad = True
ctl(bad, "alpha = 1")
# 2. t = +-4: (B1) fails somewhere
bad = False
for l in range(1, 8):
    for c in (1, 2, 3, 4):
        if c == 1: continue   # Psi - 4 has the payment 4(d + c - 1), zero at d = 0 when c = 1: not invertible
        pi = lambda d, c=c: 4 * (d + c)
        Psi = mk_op(pi, 1, lambda m, f: 0)
        Mi, nf = lattice_inverse_final(l, Psi); MP = inv(Mi)
        for t in (Fraction(4), Fraction(-4)):
            Nt, _ = lattice_inverse_final(l, mk_shift(pi, t, 1, lambda m, f: 0))
            if minval(mm(MP, Nt)) < 1: bad = True
ctl(bad, "t = +-4")
# 3. the bound v2 >= 2 in (B1): fails (attained 1)
ctl(attained_one > 0, "B1 bound 2")
# 4. (Y1) with L instead of L + 1: fails somewhere
bad = False
pi = lambda d: Fraction(4 * (d + 1)) + 2
Y = inverse_coefs(pi, Fraction(1), lambda m, f: Fraction(0), 9, 26)
for LL in range(10):
    for f in range(LL, 27):
        if v2(Y[(LL, f)]) < vfact(LL) - LL: bad = True
ctl(bad, "Y1 with L")
print("controls fired", fired, "of", tried)
