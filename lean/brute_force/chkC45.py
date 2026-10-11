#!/usr/bin/env python3
"""Brute force for Lean piece C45 (paper v8 §10.4: Theorem 10.12, first half, for a general unit eta;
conjugation by eta^D; invertibility of formal operators). Grepy Escribano, 9 Oct 2026.
Reuses the definitions of chkC43.py (independent lattice model, exact rationals) and chkC44.py (Deficit a_k)."""
import random, sys, math
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)
c43 = open('chkC43.py').read()
exec(c43[c43.index('def lattice_inverse_final'):c43.index('for l in range(0, 8):\n    for alpha in (2, 3):')])
random.seed(4501)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)

def cj(u, x):
    """conjugation by dg(u^f): coef m f -> u^m * coef m f"""
    return {(m, f): Fraction(u) ** m * v for (m, f), v in x.items()}
def eqop(x, y, mmax=MMAX - 1, lo=0, hi=FH - 2):
    return all(get(x, m, f) == get(y, m, f) for m in range(mmax) for f in range(max(lo, m), hi))
def rnd_full(lo=-4, hi=4):
    return {(m, f): Fraction(random.randint(lo, hi), random.choice([1, 3, 5])) for m in range(MMAX) for f in range(FLO, FH)}

# ---------- Part C: cj is a ring automorphism and is equivariant for the twist map and the V-split ----------
for trial in range(25):
    u = Fraction(random.choice([3, -1, 5, -3]), random.choice([1, 3, 5, 7]))
    x, y = rnd_full(), rnd_full()
    ok(eqop(cj(u, mul(x, y)), mul(cj(u, x), cj(u, y))), ("C1 multiplicative", trial))
    ok(eqop(cj(u, add(x, y)), add(cj(u, x), cj(u, y))), ("C1 additive", trial))
    ok(eqop(cj(u, cj(1 / u, x)), x), ("C1 inverse", trial))
    t00, t11, t10, t01 = tw(x); c00, c11, c10, c01 = tw(cj(u, x))
    u2 = u * u; half = FH // 2 - 1
    ok(eqop(c10, smul(u, cj(u2, t10)), MMAX - 1, 0, half), ("C2 tw10 = u cj_{u^2}", trial))
    ok(eqop(c11, cj(u2, t11), MMAX - 1, 0, half), ("C2 tw11", trial))
    ok(eqop(c00, cj(u2, t00), MMAX - 1, 0, half), ("C2 tw00", trial))
    ok(eqop(c01, smul(1 / u, cj(u2, t01)), MMAX - 1, 0, half), ("C2 tw01 = u^-1 cj_{u^2}", trial))
    ok(eqop(vplus(cj(u, x)), cj(u, vplus(x)), MMAX - 1, 0, FH - 3), ("C2 vplus", trial))
    ok(eqop(vprime(cj(u, x)), smul(u, cj(u, vprime(x))), MMAX - 2, 0, FH - 3), ("C2 vprime = u cj", trial))

# ---------- Part I: invertibility: coef 0 non-zero at f >= 0 gives a two-sided inverse (Agree) ----------
for trial in range(25):
    x = rnd_full(-3, 3)
    for f in range(0, FH): x[(0, f)] = Fraction(random.choice([1, 2, -3, 4, 6]), random.choice([1, 5]))
    Y = {}
    for LL in range(MMAX):
        for f in range(LL, FH):
            s = sum(comb(LL, a) * get(x, a, f) * Y.get((LL - a, f - a), Fraction(0)) for a in range(1, LL + 1))
            Y[(LL, f)] = (Fraction(int(LL == 0)) - s) / x[(0, f)]
    R1 = mul(x, Y); R2 = mul(Y, x)
    one = {(0, f): Fraction(1) for f in range(FLO, FH)}
    ok(eqop(R1, one, MMAX, 0, FH), ("I right inverse", trial))
    ok(eqop(R2, one, MMAX, 0, FH), ("I left inverse", trial))

# ---------- Part X: XiOp eta = cj eta (XiOp 1 zeta'), zeta'_m = eta^{-m} zeta_m ----------
for trial in range(10):
    eta = Fraction(random.choice([3, -1, 5, 1, -7]), random.choice([1, 3]))
    pi = lambda d: 4 * (d + 2)
    zt = {(m, f): random.randint(-6, 6) for m in range(2, MMAX) for f in range(0, FH)}
    Xe = mk_op(pi, eta, lambda m, f: zt[(m, f)])
    X1 = mk_op(pi, 1, lambda m, f: Fraction(zt[(m, f)]) / eta ** m)
    ok(eqop(Xe, cj(eta, X1), MMAX, 0, FH), ("X: XiOp eta = cj eta (XiOp 1 zeta')", trial))

# ---------- Part F and T: final matrices on T(l) ----------
def setting(l):
    ds = digits(l); k = len(ds); I = {t for t, d in enumerate(ds) if d}; m = len(I)
    Ds = [frozenset(dancers(ds, s)) for s in range(2 ** m)]
    return ds, k, I, m, Ds
def hadamard_rel(MX, MS, s_min):
    good = True; mn = 10 ** 9
    for a in range(len(MS)):
        for b in range(len(MS)):
            if MS[a][b] == 0:
                if MX[a][b] != 0: good = False
            else:
                e = MX[a][b] / MS[a][b] - 1; mn = min(mn, v2(e))
                if v2(e) < s_min: good = False
    return good, mn
attained = set(); scaled_nontriv = 0
for l in range(1, 8):
    ds, k, I, m, Ds = setting(l); N = len(Ds); K = 2 ** k
    for alpha in (2, 3):
        for c in (1, 3):
            pi = lambda d, alpha=alpha, c=c: 2 ** alpha * (d + c)
            for eta in (Fraction(3), Fraction(-1), Fraction(1, 3), Fraction(-5, 3)):
                zt = {(m_, f): random.randint(-6, 6) for m_ in range(2, MMAX) for f in range(0, FH)}
                Xe = mk_op(pi, eta, lambda m_, f, zt=zt: zt[(m_, f)])
                X1 = mk_op(pi, 1, lambda m_, f, zt=zt, eta=eta: Fraction(zt[(m_, f)]) / eta ** m_)
                Se = mk_op(pi, eta, lambda m_, f: 0); S1 = mk_op(pi, 1, lambda m_, f: 0)
                Ms = {}
                for nm, op in (('Xe', Xe), ('X1', X1), ('Se', Se), ('S1', S1)):
                    Mi, nf = lattice_inverse_final(l, op); Ms[nm] = inv(Mi)
                # (C3) the scaling law: M(eta)_{s s'} = eta^{o(D_s) - o(D_s') - (K - 1)} M(1)_{s s'}
                for a in range(N):
                    for b in range(N):
                        e = oE(Ds[a]) - oE(Ds[b]) - (K - 1)
                        ok(Ms['Xe'][a][b] == eta ** e * Ms['X1'][a][b], ("C3 Xi scaling", l, alpha, c, eta, a, b))
                        ok(Ms['Se'][a][b] == eta ** e * Ms['S1'][a][b], ("C3 Sigma scaling", l, alpha, c, eta, a, b))
                        if eta != 1 and e != 0 and Ms['Se'][a][b] != 0: scaled_nontriv += 1
                # (T1eta) rigidity for a general unit eta
                good, mn = hadamard_rel(Ms['Xe'], Ms['Se'], alpha - 1)
                ok(good, ("T1 eta general", l, alpha, c, eta, mn))
                if mn == alpha - 1: attained.add(alpha)
ok(attained == {2, 3}, ("T1: bound alpha - 1 attained", sorted(attained)))
ok(scaled_nontriv > 0, ("C3: the scaling is not trivial", scaled_nontriv))
print("checks", checks, "failures", fails)

# ---------- controls ----------
fired = tried = 0
# 1. the exponent without the -(K - 1): fails
tried += 1; hit = False
ds, k, I, m, Ds = setting(5); K = 2 ** k; pi = lambda d: 4 * (d + 1); eta = Fraction(3)
MiE, _ = lattice_inverse_final(5, mk_op(pi, eta, lambda m_, f: 0)); Me = inv(MiE)
Mi1, _ = lattice_inverse_final(5, mk_op(pi, 1, lambda m_, f: 0)); M1 = inv(Mi1)
for a in range(len(Ds)):
    for b in range(len(Ds)):
        if Me[a][b] != eta ** (oE(Ds[a]) - oE(Ds[b])) * M1[a][b]: hit = True
fired += hit
if not hit: print("control did not fire: exponent without K - 1")
# 2. the exponent with the opposite sign: fails
tried += 1; hit = any(Me[a][b] != eta ** (-(oE(Ds[a]) - oE(Ds[b]) - (K - 1))) * M1[a][b] for a in range(len(Ds)) for b in range(len(Ds)))
fired += hit
if not hit: print("control did not fire: sign")
# 3. zeta' = zeta (without eta^{-m}): the X identity fails
tried += 1
zt = {(m_, f): random.randint(1, 6) for m_ in range(2, MMAX) for f in range(0, FH)}
Xe = mk_op(pi, eta, lambda m_, f: zt[(m_, f)]); Xbad = mk_op(pi, 1, lambda m_, f: zt[(m_, f)])
if not eqop(Xe, cj(eta, Xbad), MMAX, 0, FH): fired += 1
else: print("control did not fire: zeta' without eta^-m")
# 4. tw01 claimed equal to cj_{u^2} without the factor u^{-1}: fails
tried += 1
x = rnd_full(); u = Fraction(3)
if not eqop(tw(cj(u, x))[3], cj(u * u, tw(x)[3]), MMAX - 1, 0, FH // 2 - 1): fired += 1
else: print("control did not fire: tw01 factor")
print("controls fired", fired, "of", tried)
