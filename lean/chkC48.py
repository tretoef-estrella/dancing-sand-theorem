# Brute force for Lean piece C48 (Theorem 10.15 on covariant systems), Grepy Escribano, 9 Oct 2026.
# Exact rationals; elements of Z_2 as fractions with odd denominators.
import random, itertools
from fractions import Fraction as Fr
from functools import lru_cache
from math import comb
random.seed(48)
N = {'ok': 0, 'bad': 0}; fired = {}
def ok(c, msg):
    if c: N['ok'] += 1
    else:
        N['bad'] += 1
        if N['bad'] < 10: print('FAIL', msg)
def fire(name, c): fired[name] = fired.get(name, False) or c
def v2(x):
    x = Fr(x)
    if x == 0: return 99
    n, d, v = x.numerator, x.denominator, 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
def dfact(n):  # n!!
    r = 1
    while n > 1: r *= n; n -= 2
    return r
def dfi(q): return Fr(1, dfact(max(2 * q - 1, 0)))
def o(D): return sum(2 ** t for t in D)
def rz(): return Fr(random.randint(-9, 9), random.choice([1, 3, 5]))
# a rep (a, p, q): value a + 2 p(2y)/q(2y), p(0)=0, q(0) odd
def rrep(amod=None, aodd=None):
    a = rz()
    if amod == 4: a = 4 * Fr(random.randint(-3, 3), random.choice([1, 3]))
    if amod == 2: a = 4 * Fr(random.randint(-3, 3), random.choice([1, 3])) + 2
    if aodd: a = Fr(random.choice([1, 3, -1, 5]), random.choice([1, 3]))
    if aodd is False: a = 2 * Fr(random.randint(-3, 3), random.choice([1, 3]))
    p = [Fr(0)] + [Fr(random.randint(-2, 2)) for _ in range(2)]
    q = [Fr(random.choice([1, 3, -1]))] + [Fr(random.randint(-2, 2)) for _ in range(1)]
    return (a, tuple(p), tuple(q))
def pev(p, x): return sum(c * Fr(x) ** i for i, c in enumerate(p))
def ev(r, y):
    a, p, q = r; return a + 2 * pev(p, 2 * y) / pev(q, 2 * y)
SUBS = lambda P: [frozenset(s) for k in range(len(P) + 1) for s in itertools.combinations(sorted(P), k)]
def randGamma(P, M, ctrl_a=False, ctrl_b=False):
    reps = {}
    for D in SUBS(P):
        for m in range(2 * M + 3):
            if D == frozenset() and m == 0:
                reps[(D, m)] = rrep(aodd=True) if ctrl_a == 'odd' else rrep(amod=2 if ctrl_a else 4)
            elif D == frozenset() and m == 1: reps[(D, m)] = rrep(aodd=not ctrl_b) if not ctrl_b else rrep(aodd=False)
            else: reps[(D, m)] = rrep()
    return lambda D, m, y: ev(reps[(frozenset(D), m)], y) if (frozenset(D), m) in reps else Fr(0)
def G1(D, m, y): return Fr(1) if (len(D) == 0 and m == 0) else Fr(0)
def prodFun(h, Ga, Gb):
    def f(D, m, y):
        D = frozenset(D); s = Fr(0)
        for D1 in SUBS(D):
            for a in range(m + 1):
                s += comb(m, a) * Ga(D1, a, y) * Gb(D - D1, m - a, y - a * 2 ** h - o(D1))
        return s
    return f
# covSys entry as a Bf coefficient function
def cov(P, h, c, Ga):
    def ent(D, Dp, m, f):
        return Ga(D - Dp, m, 2 ** h * f + o(D) + c) if Dp <= D else Fr(0)
    return ent
# twist pieces of a Bf coefficient function x(m, f)
def tw00(x): return lambda q, f: dfi(q) * x(2 * q, 2 * f)
def tw11(x): return lambda q, f: dfi(q) * x(2 * q, 2 * f + 1)
def tw10(x): return lambda q, f: dfi(q + 1) * x(2 * q + 1, 2 * f + 1)
def tw01(x): return lambda m, f: Fr(0) if m == 0 else (2 * (m - 1) + 2) * dfi(m) * x(2 * (m - 1) + 1, 2 * f)
def vplus(x): return lambda m, g: x(m, g + 1)
def vprime(x): return lambda m, g: x(m + 1, g + 1)
# the data of C48
def GB(Ga): return lambda D, q, y: dfi(q) * Ga(D, 2 * q, y)
def GC(h, Ga, shift=True): return lambda D, q, y: dfi(q) * Ga(D, 2 * q, y + (2 ** h if shift else 0))
def GP(h, Ga): return lambda D, q, y: dfi(q + 1) * Ga(D, 2 * q + 1, y + 2 ** h)
def GD(Ga): return lambda D, m, y: Fr(0) if m == 0 else (2 * (m - 1) + 2) * dfi(m) * Ga(D, 2 * (m - 1) + 1, y)
def Qinv(h1, Gp):  # right inverse by recursion: prodFun_{h1} Gp GQ = G1
    memo = {}
    def GQ(D, m, y):
        D = frozenset(D); key = (D, m, y)
        if key in memo: return memo[key]
        s = G1(D, m, y)
        for D1 in SUBS(D):
            for a in range(m + 1):
                if len(D1) == 0 and a == 0: continue
                s -= comb(m, a) * Gp(D1, a, y) * GQ(D - D1, m - a, y - a * 2 ** h1 - o(D1))
        r = s / Gp(frozenset(), 0, y); memo[key] = r; return r
    return GQ
def vsplitG(h, Ga): return lambda D, m, y: Ga(frozenset(D) - {h}, m + 1, y) if h in D else Ga(D, m, y)
def matmul(ents, idx, M):  # product of Bf matrices given as coef functions ent(D, D', m, f)
    def prod2(X, Y):
        def ent(D, Dp, m, f):
            return sum(comb(m, a) * X(D, E, a, f) * Y(E, Dp, m - a, f - a) for E in idx for a in range(m + 1))
        return ent
    out = ents[0]
    for Y in ents[1:]: out = prod2(out, Y)
    return out
MM = 3; FL = range(-2, 5)
def checks(P, h, c, ctrl=None):
    M = MM
    Ga = randGamma(P, M + 1, ctrl_a=('odd' if ctrl == 'aodd' else ctrl == 'a'), ctrl_b=(ctrl == 'b'))
    idx = SUBS(P); h1 = h + 1
    G = cov(P, h, c, Ga)
    # (W1)
    for D in idx:
        for Dp in idx:
            x = lambda m, f, D=D, Dp=Dp: G(D, Dp, m, f)
            for q in range(M):
                for f in FL:
                    ok(tw00(x)(q, f) == cov(P, h1, c, GB(Ga))(D, Dp, q, f), 'W1 B')
                    ok(tw10(x)(q, f) == cov(P, h1, c, GP(h, Ga))(D, Dp, q, f), 'W1 P')
                    ok(tw01(x)(q, f) == cov(P, h1, c, GD(Ga))(D, Dp, q, f), 'W1 D')
                    okC = tw11(x)(q, f) == cov(P, h1, c, GC(h, Ga))(D, Dp, q, f)
                    ok(okC, 'W1 C')
                    bad = tw11(x)(q, f) != cov(P, h1, c, GC(h, Ga, shift=False))(D, Dp, q, f)
                    fire('C2 unshifted C', bad)
    Gp = GP(h, Ga); GQ = Qinv(h1, Gp)
    ys = [c + rz() * 2 for _ in range(3)] + [c, c + 1]
    # (W3) inverse identities, integrality
    for D in idx:
        for m in range(M):
            for y in ys:
                val = prodFun(h1, Gp, GQ)(D, m, y)
                ok(val == G1(D, m, y), 'W3 right')
                if ctrl == 'b': fire('C4 even F-coefficient', v2(GQ(D, m, y)) < 0)
                elif True: ok(v2(GQ(D, m, y)) >= 0, 'W3 integral')
    if ctrl == 'b': return
    # matrix level: P*Q = 1 and Q*P = 1 on Dn P
    Pm = cov(P, h1, c, Gp); Qm = cov(P, h1, c, GQ)
    PQ = matmul([Pm, Qm], idx, M); QP = matmul([Qm, Pm], idx, M)
    for D in idx:
        for Dp in idx:
            for m in range(M):
                for f in range(0, 3):
                    one = Fr(1) if (D == Dp and m == 0) else Fr(0)
                    ok(PQ(D, Dp, m, f) == one, 'W3 PQ')
                    ok(QP(D, Dp, m, f) == one, 'W3 QP')
    # (W4) Schur complement
    GS0 = prodFun(h1, prodFun(h1, GB(Ga), GQ), GC(h, Ga))
    GS = lambda D, m, y: GD(Ga)(D, m, y) - GS0(D, m, y)
    for D in idx:
        for m in range(M):
            for y in ys:
                s = GS(D, m, y)
                if ctrl == 'aodd': fire('C1a odd payment: not clean', v2(s) < 1)
                else: ok(v2(s) >= 1, 'W4 even (payments even suffice)')
    if ctrl == 'aodd': return
    E = frozenset()
    if ctrl == 'a':
        for y in ys:
            fire('C1b payment 2 mod 4: (a) or (b) lost at next level',
                 v2(GS(E, 1, y) / 2) != 0 or v2(GS(E, 0, y) / 2) < 2)
        return
    for y in ys:
        g0 = GS(E, 0, y) / 2; g1 = GS(E, 1, y) / 2
        ok(2 * g0 == -Ga(E, 0, y) * (1 / Ga(E, 1, y + 2 ** h)) * Ga(E, 0, y + 2 ** h), 'W5 formula')
        ok(v2(g0) >= 3, 'W5 mod 8'); ok(v2(g1) == 0, 'W5 unit')
    # matrix level CleanStep identity
    Bm = cov(P, h1, c, GB(Ga)); Cm = cov(P, h1, c, GC(h, Ga)); Dm = cov(P, h1, c, GD(Ga))
    BQC = matmul([Bm, Qm, Cm], idx, M)
    Sm = cov(P, h1, c, GS)
    for D in idx:
        for Dp in idx:
            for m in range(2):
                for f in range(0, 2):
                    ok(Dm(D, Dp, m, f) - BQC(D, Dp, m, f) == Sm(D, Dp, m, f), 'W4 matrix')
    # (V1) the V-split, h not in P
    if h not in P:
        P2 = sorted(set(P) | {h}); idx2 = SUBS(P2); Gv = vsplitG(h, Ga)
        Gn = cov(P2, h, c, Gv)
        def emb(D, v): return D | {h} if v == 1 else D
        for D in idx:
            for Dp in idx:
                x = lambda m, f, D=D, Dp=Dp: G(D, Dp, m, f)
                for v, vp in itertools.product([0, 1], repeat=2):
                    for m in range(M):
                        for g in FL:
                            if (v, vp) == (0, 0): lhs = x(m, g)
                            elif (v, vp) == (1, 0): lhs = vprime(x)(m, g)
                            elif (v, vp) == (1, 1): lhs = vplus(x)(m, g)
                            else: lhs = Fr(0)
                            ok(lhs == Gn(emb(D, v), emb(Dp, vp), m, g), 'V1')
                            # control: position without the 2^h of the new dancer
                            if (v, vp) == (1, 1):
                                Dn = emb(D, v); Dpn = emb(Dp, vp)
                                wrong = Gv(Dn - Dpn, m, 2 ** h * g + o(D) + c) if Dpn <= Dn else Fr(0)
                                fire('C3 split offset', lhs != wrong)
        # (V2) conditions preserved
        for y in ys:
            ok(v2(Gv(E, 0, y)) >= 2 and v2(Gv(E, 1, y)) == 0, 'V2')
            ok(Gv(frozenset({h}), 0, y) == Ga(E, 1, y), 'V2 coupling')
for P, h in [([], 0), ([0], 1), ([], 1), ([0], 2), ([0, 1], 2), ([1], 2), ([0, 2], 3)]:
    for _ in range(2):
        checks(P, h, rz())
for P, h in [([], 0), ([0], 1)]:
    checks(P, h, rz(), ctrl='b'); checks(P, h, rz(), ctrl='aodd')
    for _ in range(6): checks(P, h, rz(), ctrl='a')
# (O) level 0: XiOpZ = covSys over Dn ∅ at h = 0
for alpha in [2, 3]:
    eta = Fr(random.choice([1, 3, -1])); z = {m: rz() for m in range(2, 6)}
    for cc in range(0, 4):
        G0 = lambda D, m, y: (2 ** alpha * y if m == 0 else eta if m == 1 else z[m]) if len(D) == 0 else Fr(0)
        for m in range(5):
            for f in FL:
                xi = 2 ** alpha * (f + cc) if m == 0 else eta if m == 1 else z[m]
                ok(xi == cov([], 0, cc, G0)(frozenset(), frozenset(), m, f), 'O2')
        ok(all(v2(G0(frozenset(), 0, y)) >= 2 for y in [Fr(1), Fr(3), Fr(1, 3), Fr(6)]), 'O1 a')
print('checks', N['ok'], 'failures', N['bad'])
print('controls', {k: v for k, v in fired.items()})
print('FIN')
