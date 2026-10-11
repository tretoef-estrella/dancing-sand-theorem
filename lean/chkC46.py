#!/usr/bin/env python3
"""Brute force for Lean piece C46 (paper v8 §10.4: Theorem 10.12, second half). Grepy Escribano, 9 Oct 2026.
Same Smith form at 2 for M_w(Xi), M_w(Sigma_eta) and the dance matrix of sigma (eta = 1, zeta = 0);
the general Smith statement «same support and same entry valuations as the dance matrix => same Smith
exponents» (Part G); and the truncation lemma (Part Z). Reuses the lattice model of chkC43.py."""
import random, sys
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)
c43 = open('chkC43.py').read()
exec(c43[c43.index('def lattice_inverse_final'):c43.index('for l in range(0, 8):\n    for alpha in (2, 3):')])
random.seed(4601)
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
                f = A[r2][c] / A[r][c]
                for c2 in cols: A[r2][c2] -= f * A[r][c2]
        for c2 in cols:
            if c2 != c and A[r][c2] != 0:
                f = A[r][c2] / A[r][c]
                for r2 in rows: A[r2][c2] -= f * A[r2][c]
        rows.remove(r); cols.remove(c)
    return sorted(ex, key=lambda v: (v is None, v))
def appr(q, N):
    """the integer in [0, 2^N) congruent to q (q a 2-adic integer given as a Fraction with odd denominator)"""
    q = Fraction(q); assert vq(q) is None or vq(q) >= 0
    M = 2 ** N
    return (q.numerator * pow(q.denominator, -1, M)) % M
def odd_unit():
    return Fraction(random.choice([1, 3, 5, 7, -1, -3, 9, 11]), random.choice([1, 3, 5, 7]))
fired = {}
def fire(name, c): fired[name] = fired.get(name, False) or c
cells = 0
for l in range(1, 8):
    ds = digits(l)
    if len(ds) < 1: continue
    for alpha in (2, 3):
        for c in (1, 3):
            pi = lambda d, alpha=alpha, c=c: 2 ** alpha * (d + c)
            S1 = mk_op(pi, 1, lambda m_, f: 0)
            Mi, _ = lattice_inverse_final(l, S1); MS1 = inv(Mi)
            n = len(MS1)
            ok(all(vq(x) is None or vq(x) >= 0 for r in MS1 for x in r), ("sigma dance matrix integral", l, alpha, c))
            E0 = smith_exps(MS1)
            ok(None not in E0, ("det != 0 for c >= 1", l, alpha, c))
            for eta in (Fraction(3), Fraction(-1), Fraction(5, 3), Fraction(-7, 5)):
                zt = {(m_, f): odd_unit() * random.randint(-4, 4) for m_ in range(2, MMAX) for f in range(0, FH)}
                Xe = mk_op(pi, eta, lambda m_, f, zt=zt: zt[(m_, f)])
                Se = mk_op(pi, eta, lambda m_, f: 0)
                MX = inv(lattice_inverse_final(l, Xe)[0]); MS = inv(lattice_inverse_final(l, Se)[0])
                cells += 1
                # (R0) integrality of M_w(Xi) over Z_2 (odd denominators only)
                ok(all(vq(x) is None or vq(x) >= 0 for r in MX for x in r), ("M_Xi integral", l, alpha, c, eta))
                # same support and same valuations as the sigma matrix (T2eta + F1eta with |eta| = 1)
                ok(all((MX[a][b] == 0) == (MS1[a][b] == 0) and vq(MX[a][b]) == vq(MS1[a][b])
                       for a in range(n) for b in range(n)), ("support and valuations", l, alpha, c, eta))
                # (R2) the Smith exponents agree
                ok(smith_exps(MX) == E0, ("Smith M_Xi = Smith M_sigma", l, alpha, c, eta))
                ok(smith_exps(MS) == E0, ("Smith M_Sigma_eta = Smith M_sigma", l, alpha, c, eta))
                # (Z) truncation at N above every entry valuation and every exponent
                vmax = max(vq(x) for r in MX for x in r if x != 0)
                N = 1 + max(vmax, max(E0))
                Y = [[Fraction(appr(x, N)) for x in r] for r in MX]
                ok(all((Y[a][b] == 0) == (MX[a][b] == 0) and vq(Y[a][b]) == vq(MX[a][b])
                       for a in range(n) for b in range(n)), ("truncation keeps zeros and valuations", l, alpha, c, eta))
                ok(smith_exps(Y) == E0, ("Smith of the truncation", l, alpha, c, eta))
                R = [[Fraction(random.randint(-9, 9), random.choice([1, 3, 5])) for _ in range(n)] for _ in range(n)]
                ok(smith_exps([[Y[a][b] + 2 ** N * R[a][b] for b in range(n)] for a in range(n)]) == E0,
                   ("Z1: any X = Y + 2^N R has the Smith form of Y", l, alpha, c, eta))
                # control: truncation at N = 1 changes something
                Y1 = [[Fraction(appr(x, 1)) for x in r] for r in MX]
                fire("truncation too short", smith_exps(Y1) != E0)
            # (G) every matrix with the support and the entry valuations of M_sigma has its Smith exponents
            for trial in range(6):
                Yg = [[MS1[a][b] * odd_unit() for b in range(n)] for a in range(n)]
                ok(smith_exps(Yg) == E0, ("G: valuations and support decide", l, alpha, c, trial))
                # control: change the valuation of one non-zero entry by one
                a, b = random.choice([(a, b) for a in range(n) for b in range(n) if MS1[a][b] != 0])
                Yc = [row[:] for row in Yg]; Yc[a][b] = Yc[a][b] * random.choice([2, Fraction(1, 2)])
                fire("one valuation changed", smith_exps(Yc) != E0)
                # control: rigidity needs v(E') >= 1: E' = -1 on one nested entry kills it
                Yk = [row[:] for row in Yg]; Yk[a][b] = 0
                fire("one entry killed", smith_exps(Yk) != E0)
            # control: zeta not integral (v = -1) breaks integrality or the Smith form
            Xbad = mk_op(pi, Fraction(3), lambda m_, f: Fraction(1, 2))
            MB = inv(lattice_inverse_final(l, Xbad)[0])
            fire("zeta of valuation -1", not all(vq(x) is None or vq(x) >= 0 for r in MB for x in r) or smith_exps(MB) != E0)
print("cells", cells, "checks", checks, "failures", fails)
print("controls fired", sum(fired.values()), "of", len(fired), fired)
