#!/usr/bin/env python3
"""Brute force for Lean piece C48b (paper v8 §10.5: Theorem 10.16 for c >= 1, and for l = 0 every c).
Grepy Escribano, 9 Oct 2026. The dance of Xi = 2^alpha (D + c) + eta F + sum_{m>=2} z_m F^(m) (constants z_m,
eta a unit) is run on the lattice T(l) itself: at every move the matrix is split by the twist/split
indexing of chkC43.lift, the pivot must be invertible over Z_2, and the Schur complement must be
2 * (integral). Then the Smith form of Xi on T(l) must equal that of sigma = 2^alpha (D + c) + F.
Reuses the lattice model of chkC43.py (as chkC46.py does)."""
import random, sys
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)
c43 = open('chkC43.py').read()
exec(c43[c43.index('def lattice_inverse_final'):c43.index('for l in range(0, 8):\n    for alpha in (2, 3):')])
random.seed(4802)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)
def vq(q):
    q = Fraction(q)
    if q == 0: return None
    n, d = abs(q.numerator), q.denominator; v = 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
def integral(M): return all(vq(x) is None or vq(x) >= 0 for r in M for x in r)
def smith_exps(Mat):
    A = [[Fraction(x) for x in row] for row in Mat]; n = len(A); ex = []
    rows = list(range(n)); cols = list(range(n))
    while rows:
        best = None
        for r in rows:
            for c in cols:
                if A[r][c] != 0:
                    v = vq(A[r][c])
                    if best is None or v < best[0]: best = (v, r, c)
        if best is None:
            ex += [None] * len(rows); break
        v, r, c = best; ex.append(v)
        for r2 in rows:
            if r2 != r and A[r2][c] != 0:
                t = A[r2][c] / A[r][c]
                A[r2] = [a - t * b for a, b in zip(A[r2], A[r])]
        rows.remove(r); cols.remove(c)
    return sorted(ex, key=lambda e: (e is None, e))
def dance_lattice(l, big, R):
    """runs the dance on the lattice matrix big (R slots on T(l)); returns (clean, final, moves)"""
    if l == 0: return True, big, 0
    if l % 2 == 1: lp = (l - 1) // 2; slots = R
    else: lp = (l - 2) // 2; slots = 2 * R
    n1 = T(lp).n
    e0 = [sl * 2 * n1 + jj for sl in range(slots) for jj in range(n1)]
    e1 = [sl * 2 * n1 + n1 + jj for sl in range(slots) for jj in range(n1)]
    P = sub_(big, e1, e0); C = sub_(big, e1, e1); Bb = sub_(big, e0, e0); Dd = sub_(big, e0, e1)
    Pi = inv(P)
    if Pi is None or not integral(Pi): return False, None, 0
    S = [[a - b for a, b in zip(ra, rb)] for ra, rb in zip(Dd, mm(mm(Bb, Pi), C))]
    if not all(vq(x) is None or vq(x) >= 1 for r in S for x in r): return False, None, 0
    good, fin, k = dance_lattice(lp, [[x / 2 for x in r] for r in S], slots)
    return good, fin, k + 1
fired = {}
def fire(name, c): fired[name] = fired.get(name, False) or c
def xi(alpha, c, eta, z):
    return mk_op(lambda d: 2 ** alpha * (d + c), eta, lambda m_, f: z[m_])
cells = 0
for l in range(0, 10):
    Tl = T(l)
    for alpha in (2, 3):
        for c in (1, 2, 3):
            sig = xi(alpha, c, 1, {m_: 0 for m_ in range(MMAX)})
            Msig = act(sig, Tl, l + 1)
            Esig = smith_exps(Msig)
            okS, finS, kS = dance_lattice(l, Msig, 1)
            ok(okS, ("sigma dance clean", l, alpha, c))
            for trial in range(4):
                eta = Fraction(random.choice([1, -1, 3, -3, 5, 7]), random.choice([1, 3, 5]))
                z = {m_: Fraction(random.randint(-7, 7), random.choice([1, 3, 5, 7])) for m_ in range(MMAX)}
                X = xi(alpha, c, eta, z)
                MX = act(X, Tl, l + 1)
                cells += 1
                # the dance of Xi is clean at every move (Theorem 10.15 transported along the dance)
                okX, finX, kX = dance_lattice(l, MX, 1)
                ok(okX, ("Xi dance clean", l, alpha, c, trial))
                ok(kX == len(digits(l)), ("number of moves = length of ds", l, kX))
                # the final matrix: same Smith form as sigma's final matrix
                if okX and okS:
                    ok(integral(finX), ("final matrix integral", l, alpha, c))
                    ok(smith_exps(finX) == smith_exps(finS), ("final Smith", l, alpha, c, trial))
                # Theorem 10.16 (c >= 1): coker(Xi on T(l)) has the Smith exponents of coker(sigma on T(l))
                ok(smith_exps(MX) == Esig, ("coker Xi = coker sigma", l, alpha, c, trial))
                if l == 0:
                    ok(MX == [[Fraction(2 ** alpha * c)]], ("l = 0: Xi on T(0) is 2^alpha c", alpha, c))
            # controls (each must fire somewhere)
            z = {m_: Fraction(random.randint(-7, 7)) for m_ in range(MMAX)}
            Mbad = act(xi(alpha, c, 2, z), Tl, l + 1)          # eta not a unit
            okb, _, _ = dance_lattice(l, Mbad, 1)
            fire("eta = 2", (not okb) or smith_exps(Mbad) != Esig)
            Mshift = act(xi(alpha, c + 1, 1, z), Tl, l + 1)    # compared with the wrong shift
            fire("shift c + 1", smith_exps(Mshift) != Esig)
            Mone = act(xi(1, c, 1, z), Tl, l + 1)              # alpha = 1 (payment only 2 mod 4)
            ok1, _, _ = dance_lattice(l, Mone, 1)
            fire("alpha = 1", (not ok1) or smith_exps(Mone) != smith_exps(act(xi(1, c, 1, {m_: 0 for m_ in range(MMAX)}), Tl, l + 1)))
# l = 0, c = 0: coker(Xi on T(0)) = Z_2 (the zero map), as X([], alpha, 0)
for alpha in (2, 3):
    MX0 = act(xi(alpha, 0, 3, {m_: 1 for m_ in range(MMAX)}), T(0), 1)
    ok(MX0 == [[Fraction(0)]], ("l = 0, c = 0: zero map", alpha))
print("cells", cells, "checks", checks, "failures", fails)
print("controls fired", sum(fired.values()), "of", len(fired), fired)
