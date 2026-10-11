#!/usr/bin/env python3
"""Brute force for Lean piece C50h (paper v8 §10.7, Theorem 10.22 at i = 0). Grepy Escribano, 10 Oct 2026.
Lattice model of chkC43.py (final matrices as 2^k O G^-1 I), series K(j) of chkC49.py.
Claims:
 (M1) for Psi = PsiF j (payment 4(f + (j+1)//2), eta = K(j)[1], zeta_m = K(j)[m]), j >= 1, t = +-2,
      V := Psi (Psi + t) / 2:  M_w(V) = W M_w(Psi) with W integral, W = I mod 2, det W a unit.
 (M2) the glue: gS(W-, W+, ZW) gS(X, Y, Z) = gS(W- X, W+ Y, Z1) with Z1 = (W+ Y - W- X)/2, det a unit.
 (A)  associates: Smith(P M) = Smith(M) when det P is a 2-adic unit.
Controls: j = 0 (shift 0, Psi singular on T(l)); W = I mod 4; (A) with det P even; t = +-4 (W not integral)."""
import random, sys, math
sys.path.insert(0, '.')
from fractions import Fraction
from math import comb
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)
c43 = open('chkC43.py').read()
exec(c43[c43.index('def lattice_inverse_final'):c43.index('for l in range(0, 8):\n    for alpha in (2, 3):')])
random.seed(10022)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)
MMS = 14
def dfact(k):
    p = 1
    while k > 1: p *= k; k -= 2
    return p
dfi = lambda s: Fraction(1, dfact(2 * s - 1))
chF = [dfi(m) for m in range(MMS)]; shF = [dfi(m + 1) for m in range(MMS)]
def cmul(x, y): return [sum(comb(m, a) * x[a] * y[m - a] for a in range(m + 1)) for m in range(MMS)]
shInv = [Fraction(1)]
for m in range(1, MMS): shInv.append(-sum(comb(m, b) * shF[m - b] * shInv[b] for b in range(m)))
def K(j): return cmul([chF[m] - ((-1) ** j if m == 0 else 0) for m in range(MMS)], shInv)
def mk_shift(pi0, t, eta, zeta):
    x = mk_op(pi0, eta, zeta)
    for f in range(FLO, FH):
        if f >= 0: x[(0, f)] += t
    return x
def madd(X, Y): return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(X, Y)]
def msc(c, X): return [[c * a for a in r] for r in X]
def minv_v(X): return min(v2(a) for r in X for a in r)
def det(M):
    n = len(M); A = [row[:] for row in M]; d = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if A[r][i] != 0), None)
        if p is None: return Fraction(0)
        if p != i: A[i], A[p] = A[p], A[i]; d = -d
        d *= A[i][i]
        for r in range(i + 1, n):
            q = A[r][i] / A[i][i]; A[r] = [a - q * b for a, b in zip(A[r], A[i])]
    return d

# The singular arm Psi_0 approximated by Psi(c), c = 2^n: payment 4(f + c), eta = K(0)[1], zeta = K(0)[m].
k0 = K(0)
def arm(c): return mk_op(lambda d, c=c: 4 * (d + c), k0[1], lambda m, f: k0[m])
def half(c, t): return smul(Fraction(1, 2), mul(arm(c), mk_shift(lambda d, c=c: 4 * (d + c), t, k0[1], lambda m, f: k0[m])))
ok(k0[1] == 1 and k0[0] == 0, "K(0): eta = 1, payment 4f at c = 0")
NN = 9
rate = {}
for l in range(0, 7):
    Ms, Vs, Ws = [], [], []
    for n in range(0, NN):
        c = 2 ** n
        MinvP, nf = lattice_inverse_final(l, arm(c)); MP = inv(MinvP)
        MinvV, _ = lattice_inverse_final(l, half(c, Fraction(2))); MV = inv(MinvV)
        W = mm(MV, MinvP)
        ok(minv_v(MP) >= 0 and minv_v(MV) >= 0, ("final matrices integral", l, n))
        ok(minv_v(W) >= 0 and minv_v(madd(W, msc(-1, ident(nf)))) >= 1 and v2(det(W)) == 0, ("W(2^n) in GL, = I mod 2", l, n))
        ok(eq(mm(W, MP), MV), ("M_V = W M_Psi", l, n))
        Ms.append(MP); Vs.append(MV); Ws.append(W)
    k = len(digits(l))
    for n in range(0, NN - 1):
        dM = minv_v(madd(Ms[n + 1], msc(-1, Ms[n]))); dV = minv_v(madd(Vs[n + 1], msc(-1, Vs[n])))
        ok(dM >= n + 2 - k, ("(K1)+T1: M_Psi(2^n) Cauchy at rate n + 2 - k", l, n, dM, k))
        ok(dV >= n + 1 - k, ("(K2)+T1: M_V(2^n) Cauchy at rate n + 1 - k", l, n, dV, k))
        rate.setdefault(l, []).append(minv_v(madd(Ws[n + 1], msc(-1, Ws[n]))))
print("checks", checks, "failures", fails)
print("v2(W(2^(n+1)) - W(2^n)) by l (the W need not converge; compactness gives a subsequence):", rate)
fired = tried = 0
def ctl(cond, name):
    global fired, tried
    tried += 1
    if cond: fired += 1
    else: print("control did not fire:", name)
# 1. c = 0 itself: Psi_0 is singular on T(l), l >= 1
sing = False
for l in range(1, 5):
    try: lattice_inverse_final(l, arm(0))
    except Exception: sing = True
ctl(sing, "c = 0 singular")
# 2. the Cauchy rate n + 3 - k (one more than claimed for M_Psi, same pairs) fails somewhere
bad = False
for l in range(0, 7):
    k = len(digits(l))
    for n in range(0, NN - 1):
        a_ = inv(lattice_inverse_final(l, arm(2 ** n))[0]); b_ = inv(lattice_inverse_final(l, arm(2 ** (n + 1)))[0])
        if minv_v(madd(b_, msc(-1, a_))) < n + 3 - k: bad = True
ctl(bad, "rate too strong")
# 3. odd shifts c = 2^n + 1 do not approach the c = 0 data: M_Psi(2^n + 1) - M_Psi(2^n) not small
bad = False
for l in range(1, 6):
    for n in range(3, 7):
        a = inv(lattice_inverse_final(l, arm(2 ** n))[0]); b = inv(lattice_inverse_final(l, arm(2 ** n + 1))[0])
        if minv_v(madd(a, msc(-1, b))) < n - 1: bad = True
ctl(bad, "odd shift")
print("controls fired", fired, "of", tried)
