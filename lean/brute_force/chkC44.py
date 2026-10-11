#!/usr/bin/env python3
"""Brute force for Lean piece C44 (paper v8 §10.4: Lemma 10.11 stability, the factorization M_w(Sigma) = d1 A d2,
and Theorem 10.12 first half, entrywise rigidity, for eta = 1). Grepy Escribano, 9 Oct 2026.
Reuses the definitions of chkC43.py (independent lattice model of T(l), exact rationals) by executing its
definition part only (everything before the C43 checks)."""
import random, sys, math
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC43.py').read().split('# (P1) exact for Sigma')[0]
exec(src)          # defines lift, lattice_inverse_final, mk_op, inv, mm, v2, digits, dancers, oE, T, act, ...
def lattice_inverse_final(l, x):
    """2^k O (act x on T(l))^{-1} I, with I, O of the word (C41, C42) taken from lift() of any payment system"""
    p0, k0 = [lambda f: 1], [[lambda f: 0]]
    G, Lm, Im, Om, pf, kf, nf, K, good = lift(l, p0, k0)
    Gx = act(x, T(l), MMAX)
    Gi = inv(Gx)
    return [[Fraction(2 ** K) * v for v in row] for row in mm(mm(Om, Gi), Im)], nf
def mk_op(pi, eta, zeta):
    x = {}
    for f in range(FLO, FH):
        x[(0, f)] = Fraction(pi(f)) if f >= 0 else Fraction(1)
        x[(1, f)] = Fraction(eta)
        for m in range(2, MMAX): x[(m, f)] = Fraction(zeta(m, f)) if f >= 0 else Fraction(0)
    return x

random.seed(4401)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)

# ---------- C10: the polynomials q_t on coefficient functions of finite sets ----------
def subsets(S):
    S = sorted(S); out = []
    for b in range(2 ** len(S)): out.append(frozenset(S[i] for i in range(len(S)) if (b >> i) & 1))
    return out
_AMEMO = {}
def a_coef(I, t, D):
    """Deficit.a I t D (exact integers), by the recursion of C10"""
    memo = _AMEMO.setdefault(frozenset(I), {})
    def a(t, D):
        if (t, D) in memo: return memo[(t, D)]
        if t == 0: v = -1 if not D else 0
        else:
            v = sum(a(t - 1, D1) * a(t - 1, D - D1) for D1 in subsets(D))
            if (t - 1) in I and (t - 1) in D: v -= a(t - 1, D - {t - 1})
        memo[(t, D)] = v; return v
    return a(t, frozenset(D))
def delta(k, D):
    return 0 if not D else k - len(D) - min(D)

def setting(l):
    ds = digits(l); k = len(ds); I = {t for t, d in enumerate(ds) if d}; m = len(I)
    Ds = [frozenset(dancers(ds, s)) for s in range(2 ** m)]
    return ds, k, I, m, Ds

# ---------- Part A: the matrix A and its inverse ----------
for l in range(1, 64):
    ds, k, I, m, Ds = setting(l); N = len(Ds)
    ok(len(set(Ds)) == N, ("Dset injective", l))
    A = [[Fraction(a_coef(I, k, Ds[s] - Ds[t])) if Ds[t] <= Ds[s] else Fraction(0) for t in range(N)] for s in range(N)]
    for s in range(N):
        ok(A[s][s] == 1, ("A diagonal 1", l, s))
        for t in range(N):
            if Ds[t] <= Ds[s]:
                ok(A[s][t] != 0 and v2(A[s][t]) == delta(k, Ds[s] - Ds[t]), ("A exact valuation delta", l, s, t))
    B = inv(A)
    for s in range(N):
        for t in range(N):
            if Ds[t] <= Ds[s]: ok(v2(B[s][t]) >= delta(k, Ds[s] - Ds[t]), ("A^-1 bound", l, s, t))
            else: ok(B[s][t] == 0, ("A^-1 support", l, s, t))
    # subadditivity on nested triples, and nu(s, s) = 0
    for s in range(N):
        for u in range(N):
            if not Ds[u] <= Ds[s]: continue
            for t in range(N):
                if Ds[t] <= Ds[u]:
                    ok(delta(k, Ds[s] - Ds[t]) <= delta(k, Ds[s] - Ds[u]) + delta(k, Ds[u] - Ds[t]), ("subadd", l, s, u, t))

# ---------- Part F and Part T: on T(l), eta = 1 ----------
def hadamard_rel(MX, MS, s_min):
    """MX = MS o (1 + E'), v2(E') >= s_min, same support; returns (ok, min v2 of E' over the support)"""
    good = True; mn = 10 ** 9
    for a in range(len(MS)):
        for b in range(len(MS)):
            if MS[a][b] == 0:
                if MX[a][b] != 0: good = False
            else:
                e = MX[a][b] / MS[a][b] - 1; mn = min(mn, v2(e))
                if v2(e) < s_min: good = False
    return good, mn
attained = set(); nontrivial = 0
for l in range(1, 8):
    ds, k, I, m, Ds = setting(l); N = len(Ds); K = 2 ** k
    for alpha in (2, 3):
        for c in (1, 2, 3):
            pi0 = lambda d, alpha=alpha, c=c: Fraction(2 ** alpha * (c + d))
            for trial in range(3):
                zt = {(mm_, f): random.randint(-6, 6) for mm_ in range(2, MMAX) for f in range(0, FH)}
                Sig = mk_op(pi0, 1, lambda m_, f: 0)
                Xi = mk_op(pi0, 1, lambda m_, f, zt=zt: zt[(m_, f)])
                MSi, nf = lattice_inverse_final(l, Sig); MXi, _ = lattice_inverse_final(l, Xi)
                MS = inv(MSi); MX = inv(MXi)
                ok(nf == N and MS is not None and MX is not None, ("sizes / invertible", l))
                # Part F: M_w(Sigma) = Mc entrywise, and = d1 A d2
                for s in range(N):
                    for t in range(N):
                        if Ds[t] <= Ds[s]:
                            D, Dp = Ds[s], Ds[t]
                            prod = Fraction(1)
                            for d in range(oE(D), oE(Dp) + K): prod *= pi0(d)
                            mc = -Fraction(2) ** (1 - K + oE(D - Dp)) * a_coef(I, k, D - Dp) * prod
                            ok(MS[s][t] == mc, ("F: M_Sigma = Mc", l, alpha, c, s, t))
                            p1 = Fraction(1)
                            for d in range(0, oE(D)): p1 *= pi0(d)
                            p2 = Fraction(1)
                            for d in range(0, oE(Dp) + K): p2 *= pi0(d)
                            d1 = -Fraction(2) ** (1 - K) * Fraction(2) ** oE(D) / p1
                            d2 = Fraction(2) ** (-oE(Dp)) * p2
                            ok(MS[s][t] == d1 * a_coef(I, k, D - Dp) * d2, ("F: d1 A d2", l, s, t))
                        else:
                            ok(MS[s][t] == 0, ("F: support", l, s, t))
                # Part T: M_w(Xi) = M_w(Sigma) o (1 + E'), v2(E') >= alpha - 1
                good, mn = hadamard_rel(MX, MS, alpha - 1)
                ok(good, ("T rigidity", l, alpha, c, trial, mn))
                if mn == alpha - 1: attained.add(alpha)
                if any(MX[a][b] != MS[a][b] for a in range(N) for b in range(N)): nontrivial += 1
ok(attained == {2, 3}, ("T: the bound alpha - 1 is attained", sorted(attained)))
ok(nontrivial > 0, ("T: Xi and Sigma final matrices differ somewhere", nontrivial))

# ---------- Part S: the abstract stability lemma, random weighted matrices ----------
for trial in range(300):
    kk = random.randint(1, 4); I = set(random.sample(range(kk), random.randint(0, kk)))
    Ds = subsets(I); N = len(Ds)
    nu = lambda s, t: delta(kk, Ds[s] - Ds[t])
    S = lambda s, t: Ds[t] <= Ds[s]
    # A = 1 + N, N strictly nested, exact valuation nu on nested pairs (unit times 2^nu)
    A = [[Fraction(0)] * N for _ in range(N)]
    for s in range(N):
        for t in range(N):
            if S(s, t):
                A[s][t] = Fraction(1) if s == t else Fraction(2 ** nu(s, t) * random.choice([1, -1, 3, 5, -7]))
    B = inv(A)
    okB = all((B[s][t] == 0) if not S(s, t) else v2(B[s][t]) >= nu(s, t) for s in range(N) for t in range(N))
    ok(okB, ("S: B in W", trial))
    sm = random.randint(1, 3)
    E = [[Fraction(2 ** sm * random.randint(-5, 5), random.choice([1, 3, 5])) for _ in range(N)] for _ in range(N)]
    H = [[B[s][t] * (1 + E[s][t]) for t in range(N)] for s in range(N)]
    Hi = inv(H)
    ok(Hi is not None, ("S: invertible", trial))
    good, mn = hadamard_rel(Hi, A, sm)
    ok(good, ("S: stability, v2(E') >= s", trial, sm, mn))
    # diagonal scaling (S2): M = diag(x) A diag(y)
    x = [Fraction(random.choice([1, 2, 4, 3, 6]), random.choice([1, 2, 5])) for _ in range(N)]
    y = [Fraction(random.choice([1, 8, 3]), random.choice([1, 4, 7])) for _ in range(N)]
    M = [[x[s] * A[s][t] * y[t] for t in range(N)] for s in range(N)]
    Mi = inv(M)
    H2 = [[Mi[s][t] * (1 + E[s][t]) for t in range(N)] for s in range(N)]
    good2, _ = hadamard_rel(inv(H2), M, sm)
    ok(good2, ("S2: with diagonal scalings", trial))
print("checks", checks, "failures", fails)

# ---------- controls (each must fire) ----------
fired = tried = 0
# 1. E with v2 = 0 allowed: stability fails somewhere
tried += 1; hit = False
for trial in range(200):
    kk = 3; I = {0, 1, 2}; Ds = subsets(I); N = len(Ds)
    A = [[Fraction(1) if s == t else (Fraction(2 ** delta(kk, Ds[s] - Ds[t]) * 3) if Ds[t] <= Ds[s] else Fraction(0)) for t in range(N)] for s in range(N)]
    B = inv(A); E = [[Fraction(random.randint(-3, 3)) for _ in range(N)] for _ in range(N)]
    H = [[B[s][t] * (1 + E[s][t]) for t in range(N)] for s in range(N)]
    Hi = inv(H)
    if Hi is None or not hadamard_rel(Hi, A, 1)[0]: hit = True; break
if hit: fired += 1
else: print("control did not fire: E with v2 = 0")
# 2. d1 without the factor 2^{o_D}: the factorization fails
tried += 1; hit = False
ds, k, I, m, Ds = setting(5); K = 2 ** k; pi0 = lambda d: Fraction(4 * (1 + d))
MSi, nf = lattice_inverse_final(5, mk_op(pi0, 1, lambda m_, f: 0)); MS = inv(MSi)
for s in range(len(Ds)):
    for t in range(len(Ds)):
        if Ds[t] <= Ds[s]:
            D, Dp = Ds[s], Ds[t]
            p1 = Fraction(1)
            for d in range(0, oE(D)): p1 *= pi0(d)
            p2 = Fraction(1)
            for d in range(0, oE(Dp) + K): p2 *= pi0(d)
            if MS[s][t] != -Fraction(2) ** (1 - K) / p1 * a_coef(I, k, D - Dp) * Fraction(2) ** (-oE(Dp)) * p2: hit = True
if hit: fired += 1
else: print("control did not fire: d1 without 2^{o_D}")
# 3. the bound alpha instead of alpha - 1 in Part T: fails (attained)
tried += 1
if attained == {2, 3}: fired += 1
else: print("control did not fire: alpha")
# 4. eta = 3: M_w(Sigma) is not Mc with pi0 (the restriction eta = 1 is real)
tried += 1; hit = False
ds, k, I, m, Ds = setting(5); K = 2 ** k
MSi, nf = lattice_inverse_final(5, mk_op(pi0, 3, lambda m_, f: 0)); MS3 = inv(MSi)
if MS3 != MS: hit = True
if hit: fired += 1
else: print("control did not fire: eta = 3")
# 5. the support claimed also for non-nested pairs (B must vanish there; a nonzero 'bound' check would be vacuous):
#    check that A has some non-nested zero pair at all (the support relation is not total)
tried += 1
ds, k, I, m, Ds = setting(6)
if any(not Ds[t] <= Ds[s] for s in range(len(Ds)) for t in range(len(Ds))): fired += 1
else: print("control did not fire: support total")
print("controls fired", fired, "of", tried)
