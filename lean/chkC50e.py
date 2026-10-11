#!/usr/bin/env python3
"""Brute force for Lean piece C50e (paper v8 §10.7, Corollary 10.21). Grepy Escribano, 10 Oct 2026.
Reuses chkC43.py (independent lattice model of T(l), exact rationals).
Claims, for Psi = XiOp(alpha, c, eta, zeta), t with ||t|| = 1/2, U_t := (1/2) Psi (Psi + t):
 (A1) (2/t)(Y - Y_t) is a two-sided inverse of U_t (Agree sense), Y = Psi^-1, Y_t = (Psi + t)^-1.
 (N)  Nmat(Y) = M_w(Psi)^-1 (sanity of the model of Nmat), Nmat linear.
 (F1) M_w(U_t)^-1 = (2/t)(M_w(Psi)^-1 - N_t).
 (F2) M_w(U_t) = W_t M_w(Psi), W_t = (t/2)(I - M_w(Psi) N_t)^-1.
 (W)  W_t integral, W_t = I mod 2, det W_t a unit (alpha >= 2, c >= 1).
 (W1) any E with every entry in 2Z_(2): (I - E)^-1 = I mod 2, det(I - E) a unit.
 (G)  gS(X,Y,Z) = [[X,0],[Z,Y]]: product rule, det rule, and the paper's glue identity.
Controls must fire: U without the 1/2; the inverse with the wrong sign; W = I mod 4; alpha = 1;
(W1) with an odd entry; (G) lower-left block in the wrong order."""
import random, sys, math
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)
c43 = open('chkC43.py').read()
exec(c43[c43.index('def lattice_inverse_final'):c43.index('for l in range(0, 8):\n    for alpha in (2, 3):')])
random.seed(10021)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)
def mk_shift(pi0, t, eta, zeta):
    x = mk_op(pi0, eta, zeta)
    for f in range(FLO, FH):
        if f >= 0: x[(0, f)] += t
    return x
def agrees_one(x):
    return all(get(x, m, f) == Fraction(int(m == 0)) for m in range(MMAX) for f in range(0, FH) if m <= f)
def nmat(l, Yop):
    p0, k0 = [lambda f: 1], [[lambda f: 0]]
    G, Lm, Im, Om, pf, kf, nf, K, good = lift(l, p0, k0)
    return [[Fraction(2 ** K) * v for v in row] for row in mm(mm(Om, act(Yop, T(l), MMAX)), Im)], nf
def madd(X, Y): return [[a + b for a, b in zip(ra, rb)] for ra, rb in zip(X, Y)]
def msc(c, X): return [[c * a for a in r] for r in X]
def minv_v(X):
    return min(v2(a) for r in X for a in r)
def det(M):
    n = len(M); A = [row[:] for row in M]; d = Fraction(1)
    for i in range(n):
        p = next((r for r in range(i, n) if A[r][i] != 0), None)
        if p is None: return Fraction(0)
        if p != i: A[i], A[p] = A[p], A[i]; d = -d
        d *= A[i][i]
        for r in range(i + 1, n):
            q = A[r][i] / A[i][i]
            A[r] = [a - q * b for a, b in zip(A[r], A[i])]
    return d
def opdict(Y): return {k: v for k, v in Y.items()}
TS = [Fraction(2), Fraction(-2), Fraction(6), Fraction(2, 3), Fraction(-10, 7)]
W_min_minus_I = []; seen = set(); odd_t2 = 0
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
                Yc = inverse_coefs(lambda d: Fraction(pi(d)), eta, lambda m, f: Fraction(zeta(m, f)), MMAX - 1, FH - 1)
                Y = opdict(Yc)
                MinvP, nf = lattice_inverse_final(l, Psi); MP = inv(MinvP)
                NY, _ = nmat(l, Y)
                ok(eq(NY, MinvP), ("N: Nmat(Y) = M^-1", l, alpha, c, kind))
                for t in TS:
                    Pt = mk_shift(pi, t, eta, zeta)
                    Ytc = inverse_coefs(lambda d, t=t: Fraction(pi(d)) + t, eta, lambda m, f: Fraction(zeta(m, f)), MMAX - 1, FH - 1)
                    Yt = opdict(Ytc)
                    U = smul(Fraction(1, 2), mul(Psi, Pt))
                    YU = smul(2 / t, sub(Y, Yt))
                    ok(agrees_one(mul(U, YU)) and agrees_one(mul(YU, U)), ("A1", l, alpha, c, kind, t))
                    Nt, _ = nmat(l, Yt)
                    Nt2, _ = lattice_inverse_final(l, Pt)
                    ok(eq(Nt, Nt2), ("N: Nmat(Y_t) two ways", l, t))
                    NYU, _ = nmat(l, YU)
                    ok(eq(NYU, msc(2 / t, madd(NY, msc(-1, Nt)))), ("A2 linearity", l, t))
                    MinvU, _ = lattice_inverse_final(l, U)
                    ok(eq(MinvU, msc(2 / t, madd(MinvP, msc(-1, Nt)))), ("F1", l, alpha, c, kind, t))
                    E = mm(MP, Nt)
                    W = msc(t / 2, inv(madd(ident(nf), msc(-1, E))))
                    ok(eq(inv(MinvU), mm(W, MP)), ("F2", l, alpha, c, kind, t))
                    WmI = madd(W, msc(-1, ident(nf)))
                    ok(minv_v(W) >= 0 and minv_v(WmI) >= 1 and v2(det(W)) == 0, ("W", l, alpha, c, kind, t))
                    W_min_minus_I.append(minv_v(WmI)); seen.add(l)
                    if t in (2, -2) and minv_v(WmI) == 1: odd_t2 += 1
ok(seen == set(range(8)), ("every l", sorted(seen)))
# (W1) random E with even entries
for trial in range(400):
    n = random.randint(1, 6)
    E = [[Fraction(2 * random.randint(-9, 9), random.choice([1, 3, 5, 7])) for _ in range(n)] for _ in range(n)]
    IE = madd(ident(n), msc(-1, E))
    ok(v2(det(IE)) == 0, ("W1 det", n))
    Wi = inv(IE)
    ok(minv_v(madd(Wi, msc(-1, ident(n)))) >= 1 and minv_v(Wi) >= 0, ("W1 inv", n))
# (G) the scalar glue
def gS(X, Y, Z):
    n = len(X); M = zeros(2 * n, 2 * n)
    for i in range(n):
        for j in range(n):
            M[i][j] = X[i][j]; M[n + i][j] = Z[i][j]; M[n + i][n + j] = Y[i][j]
    return M
def rmat(n, lo=-5, hi=5): return [[Fraction(random.randint(lo, hi)) for _ in range(n)] for _ in range(n)]
for trial in range(300):
    n = random.randint(1, 4)
    X, Y, Z, X2, Y2, Z2 = (rmat(n) for _ in range(6))
    ok(eq(mm(gS(X, Y, Z), gS(X2, Y2, Z2)), gS(mm(X, X2), mm(Y, Y2), madd(mm(Z, X2), mm(Y, Z2)))), ("G1", n))
    ok(det(gS(X, Y, Z)) == det(X) * det(Y), ("G2", n))
    # paper's glue: Z = (Y - X)/2 with Y = X mod 2, and W+ = I, W- = -I mod 2
    Xe = X; Ye = madd(X, msc(2, rmat(n))); Zxy = msc(Fraction(1, 2), madd(Ye, msc(-1, Xe)))
    Wm = madd(msc(-1, ident(n)), msc(2, rmat(n))); Wp = madd(ident(n), msc(2, rmat(n)))
    Zw = msc(Fraction(1, 2), madd(Wp, msc(-1, Wm)))
    ok(all(a.denominator == 1 for r in Zw for a in r), ("G4 integral", n))
    P = mm(gS(Wm, Wp, Zw), gS(Xe, Ye, Zxy))
    ZZ = [row[:n] for row in P[n:]]
    ok(eq(msc(2, ZZ), madd(mm(Wp, Ye), msc(-1, mm(Wm, Xe)))), ("G4", n))
    if det(Wm) != 0 and det(Wp) != 0:
        ok(v2(det(gS(Wm, Wp, Zw))) == v2(det(Wm)) + v2(det(Wp)), ("G3", n))
print("checks", checks, "failures", fails)
print("min v2(W - I) distribution:", {v: W_min_minus_I.count(v) for v in sorted(set(W_min_minus_I))}, "t=+-2 with v2 = 1:", odd_t2)

# ---------- controls (each must fire) ----------
fired = 0; tried = 0
def ctl(cond, name):
    global fired, tried
    tried += 1
    if cond: fired += 1
    else: print("control did not fire:", name)
pi = lambda d: 4 * (d + 2); Psi = mk_op(pi, 1, lambda m, f: 0)
Y = opdict(inverse_coefs(lambda d: Fraction(pi(d)), 1, lambda m, f: Fraction(0), MMAX - 1, FH - 1))
bad1 = bad2 = bad3 = False
for l in range(1, 8):
    MinvP, nf = lattice_inverse_final(l, Psi); MP = inv(MinvP)
    for t in (Fraction(2), Fraction(-2)):
        Pt = mk_shift(pi, t, 1, lambda m, f: 0)
        Nt, _ = lattice_inverse_final(l, Pt)
        # 1. U without the 1/2
        MinvU0, _ = lattice_inverse_final(l, mul(Psi, Pt))
        if not eq(MinvU0, msc(2 / t, madd(MinvP, msc(-1, Nt)))): bad1 = True
        # 2. the inverse with the wrong sign
        MinvU, _ = lattice_inverse_final(l, smul(Fraction(1, 2), mul(Psi, Pt)))
        if not eq(MinvU, msc(2 / t, madd(Nt, msc(-1, MinvP)))): bad2 = True
        # 3. W = I mod 4
        W = msc(t / 2, inv(madd(ident(nf), msc(-1, mm(MP, Nt)))))
        if minv_v(madd(W, msc(-1, ident(nf)))) < 2: bad3 = True
ctl(bad1, "U without 1/2"); ctl(bad2, "wrong sign"); ctl(bad3, "W = I mod 4")
# 4. alpha = 1: W not = I mod 2, or not integral
bad = False
for l in range(1, 8):
    for c in (1, 2, 3):
        pi = lambda d, c=c: 2 * (d + c); Psi = mk_op(pi, 1, lambda m, f: 0)
        MinvP, nf = lattice_inverse_final(l, Psi); MP = inv(MinvP)
        Nt, _ = lattice_inverse_final(l, mk_shift(pi, Fraction(2), 1, lambda m, f: 0))
        W = inv(madd(ident(nf), msc(-1, mm(MP, Nt))))
        if minv_v(W) < 0 or minv_v(madd(W, msc(-1, ident(nf)))) < 1: bad = True
ctl(bad, "alpha = 1")
# 5. (W1) with an odd entry
bad = False
for trial in range(50):
    n = 3
    E = [[Fraction(2 * random.randint(-9, 9)) for _ in range(n)] for _ in range(n)]
    E[0][1] = Fraction(1)
    Wi = inv(madd(ident(n), msc(-1, E))) if det(madd(ident(n), msc(-1, E))) != 0 else None
    if Wi is None or minv_v(madd(Wi, msc(-1, ident(n)))) < 1: bad = True
ctl(bad, "W1 odd entry")
# 6. (G4) with the product in the wrong order
bad = False
for trial in range(20):
    n = 2
    X = rmat(n); Ye = madd(X, msc(2, rmat(n))); Zxy = msc(Fraction(1, 2), madd(Ye, msc(-1, X)))
    Wm = madd(msc(-1, ident(n)), msc(2, rmat(n))); Wp = madd(ident(n), msc(2, rmat(n)))
    Zw = msc(Fraction(1, 2), madd(Wp, msc(-1, Wm)))
    P = mm(gS(Wm, Wp, Zw), gS(X, Ye, Zxy)); ZZ = [row[:n] for row in P[n:]]
    if not eq(msc(2, ZZ), madd(mm(Ye, Wp), msc(-1, mm(X, Wm)))): bad = True
ctl(bad, "G4 wrong order")
print("controls fired", fired, "of", tried)
