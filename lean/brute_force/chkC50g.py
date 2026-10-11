#!/usr/bin/env python3
"""Brute force for Lean piece C50g (paper v8 §10.7, Theorem 10.22 for i >= 1). Grepy Escribano, 10 Oct 2026.
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
# (P0) Psi_j: eta unit, zeta integral
for j in range(0, 10):
    k = K(j); ok(v2(k[1]) == 0 and all(v2(k[m]) >= 0 for m in range(MMS)), ("P0", j))
WmI_min = []
for l in range(0, 8):
    for j in range(1, 8):
        k = K(j); c = (j + 1) // 2
        pi = lambda d, c=c: 4 * (d + c)
        Psi = mk_op(pi, k[1], lambda m, f, k=k: k[m])
        MinvP, nf = lattice_inverse_final(l, Psi); MP = inv(MinvP)
        ok(minv_v(MP) >= 0, ("M_w(Psi) integral", l, j))
        for t in (Fraction(2), Fraction(-2)):
            V = smul(Fraction(1, 2), mul(Psi, mk_shift(pi, t, k[1], lambda m, f, k=k: k[m])))
            MinvV, _ = lattice_inverse_final(l, V); MV = inv(MinvV)
            W = mm(MV, MinvP)                       # W = M_w(V) M_w(Psi)^-1
            WmI = madd(W, msc(-1, ident(nf)))
            ok(minv_v(W) >= 0 and minv_v(WmI) >= 1 and v2(det(W)) == 0, ("M1", l, j, t))
            ok(eq(mm(W, MP), MV), ("M1 identity", l, j, t))
            WmI_min.append(minv_v(WmI))
# (M2) the glue and (A) associates on random integer matrices
def gS(X, Y, Z):
    n = len(X); M = zeros(2 * n, 2 * n)
    for i in range(n):
        for j in range(n):
            M[i][j] = X[i][j]; M[n + i][j] = Z[i][j]; M[n + i][n + j] = Y[i][j]
    return M
def rmat(n, lo=-6, hi=6): return [[Fraction(random.randint(lo, hi)) for _ in range(n)] for _ in range(n)]
for trial in range(300):
    n = random.randint(1, 4)
    X = rmat(n); Y = madd(X, msc(2, rmat(n))); Z = msc(Fraction(1, 2), madd(Y, msc(-1, X)))
    Wm = madd(ident(n), msc(2, rmat(n))); Wp = madd(ident(n), msc(2, rmat(n)))
    ZW = msc(Fraction(1, 2), madd(Wp, msc(-1, Wm)))
    Z1 = msc(Fraction(1, 2), madd(mm(Wp, Y), msc(-1, mm(Wm, X))))
    ok(eq(mm(gS(Wm, Wp, ZW), gS(X, Y, Z)), gS(mm(Wm, X), mm(Wp, Y), Z1)), ("M2", n))
    ok(v2(det(gS(Wm, Wp, ZW))) == 0, ("M2 unit", n))
    M = gS(X, Y, Z)
    ok(smith(mm(gS(Wm, Wp, ZW), M)) == smith(M), ("A associates", n))
    ok(smith(msc(4, mm(gS(Wm, Wp, ZW), M))) == smith(msc(4, M)), ("A associates, 2^h", n))
print("checks", checks, "failures", fails)
print("min v2(W - I):", {v: WmI_min.count(v) for v in sorted(set(WmI_min))})
fired = tried = 0
def ctl(cond, name):
    global fired, tried
    tried += 1
    if cond: fired += 1
    else: print("control did not fire:", name)
# 1. j = 0: shift 0, Psi_0 singular on T(l) for l >= 1
sing = False
for l in range(1, 6):
    k = K(0); Psi = mk_op(lambda d: 4 * d, k[1], lambda m, f, k=k: k[m])
    try:
        lattice_inverse_final(l, Psi)
    except Exception:
        sing = True
ctl(sing, "j = 0 singular")
# 2. W = I mod 4 fails somewhere
ctl(any(v < 2 for v in WmI_min), "W = I mod 4")
# 3. (A) with an even determinant: Smith differs somewhere
bad = False
for trial in range(50):
    n = 3; M = rmat(n); P = madd(ident(n), msc(2, rmat(n))); P[0] = [2 * a for a in P[0]]
    if det(M) != 0 and smith(mm(P, M)) != smith(M): bad = True
ctl(bad, "A with even det")
# 4. t = +-4: W not integral or not = I mod 2 somewhere
bad = False
for l in range(1, 6):
    for j in (2, 3, 4):
        k = K(j); c = (j + 1) // 2; pi = lambda d, c=c: 4 * (d + c)
        Psi = mk_op(pi, k[1], lambda m, f, k=k: k[m]); MinvP, nf = lattice_inverse_final(l, Psi)
        for t in (Fraction(4), Fraction(-4)):
            if t == -4 and c == 1: continue
            V = smul(Fraction(1, 2), mul(Psi, mk_shift(pi, t, k[1], lambda m, f, k=k: k[m])))
            W = mm(inv(lattice_inverse_final(l, V)[0]), MinvP)
            if minv_v(W) < 0 or minv_v(madd(W, msc(-1, ident(nf)))) < 1: bad = True
ctl(bad, "t = +-4")
print("controls fired", fired, "of", tried)
