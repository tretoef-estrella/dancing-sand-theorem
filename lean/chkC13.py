# Brute force for C13 (Proposition 4.3, the dance), over Z.
# v2: the control "relabel (s,j) -> s + r j" of v1 could not fail (that relabelling respects the
# order on every pair where kappa'' is non-zero); replaced by the reversed slot order.
import random, itertools
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import invariant_factors

def inv(M):
    n = len(M)
    v = [abs(int(x)) for x in invariant_factors(Matrix(M), domain=ZZ)]
    v += [0] * (n - len(v))
    return sorted(x for x in v if x != 1)

cnt = {}; fails = []
ctrl = {"digits-from-top": 0, "relabel-reversed": 0, "clocks-exp-a+1": 0, "final-2^(k-1)": 0}
def ok(name, c, info):
    cnt[name] = cnt.get(name, 0) + 1
    if not c: fails.append((name, info))

def tower(ds):
    """T(ds): (dim, floors, F) with F[j][idx] = coefficient of basis j in F(basis idx)."""
    if not ds:
        return 1, [0], [[0]]
    d, fl, F = tower(ds[1:])
    if ds[0] is False:
        D = 2 * d; flN = [0] * D; FN = [[0] * D for _ in range(D)]
        for i in range(d):
            flN[2 * i] = 2 * fl[i]; flN[2 * i + 1] = 2 * fl[i] + 1
            FN[2 * i + 1][2 * i] += 1
            for j in range(d): FN[2 * j][2 * i + 1] += 2 * F[j][i]
        return D, flN, FN
    D = 4 * d; flN = [0] * D; FN = [[0] * D for _ in range(D)]
    for i in range(d):
        for jj, add in enumerate([0, 1, 1, 2]): flN[4 * i + jj] = 2 * fl[i] + add
        FN[4 * i + 1][4 * i] += 1; FN[4 * i + 2][4 * i] += 2          # F A = B + 2C
        for j in range(d): FN[4 * j + 0][4 * i + 1] += 2 * F[j][i]   # F B = 2 A_{Fx}
        FN[4 * i + 3][4 * i + 2] += 1                                # F C = Dd
        for j in range(d): FN[4 * j + 2][4 * i + 3] += 2 * F[j][i]   # F Dd = 2 C_{Fx}
    return D, flN, FN

def paysys(r, dim, flr, F, p, kap):
    n = r * dim; G = [[0] * n for _ in range(n)]
    for s1 in range(r):
        for idx in range(dim):
            col = s1 * dim + idx; f = flr[idx]
            for j in range(dim): G[s1 * dim + j][col] += F[j][idx]
            G[col][col] += 2 * p(s1, f)
            for s in range(s1 + 1, r): G[s * dim + idx][col] += 2 * kap(s, s1, f)
    return G

def pT(p): return lambda s, f: -p(s, 2 * f) * p(s, 2 * f + 1)
def kT(p, k, r):
    def g(u, s1, f):
        mid = sum(k(s, s1, 2 * f + 1) * k(u, s, 2 * f) for s in range(s1 + 1, u))
        return -(p(s1, 2 * f + 1) * k(u, s1, 2 * f) + k(u, s1, 2 * f + 1) * p(u, 2 * f) + mid)
    return g

def split(p, k, r, mode):
    # lex slot (s, X), X = 0 (A) / 1 (C); relabel to Fin (r*2)
    if mode == "relabel-reversed":
        dec = lambda t: (r - 1 - t // 2, t % 2)
    else:
        dec = lambda t: (t // 2, t % 2)
    def p2(t, f):
        s, X = dec(t)
        return -p(s, 2 * f) * p(s, 2 * f + 1) if X == 0 else -p(s, 2 * f + 1) * p(s, 2 * f + 2)
    def k2(t2, t1, f):   # coupling from slot t1 to slot t2 (t2 > t1 in Fin order)
        u, X2 = dec(t2); s1, X1 = dec(t1)
        if X1 == 0 and X2 == 0:
            if s1 < u:
                mid = sum(k(s, s1, 2 * f + 1) * k(u, s, 2 * f) for s in range(s1 + 1, u))
                return -(p(s1, 2 * f + 1) * k(u, s1, 2 * f) + k(u, s1, 2 * f + 1) * p(u, 2 * f) + mid)
            return 0
        if X1 == 1 and X2 == 1:
            if s1 < u:
                mid = sum(k(s, s1, 2 * f + 2) * k(u, s, 2 * f + 1) for s in range(s1 + 1, u))
                return -(p(s1, 2 * f + 2) * k(u, s1, 2 * f + 1) + k(u, s1, 2 * f + 2) * p(u, 2 * f + 1) + mid)
            return 0
        if X1 == 0 and X2 == 1:
            if u == s1: return -p(s1, 2 * f + 1)
            if s1 < u: return -k(u, s1, 2 * f + 1)
            return 0
        return 0
    return p2, k2

def memo(fn):
    cache = {}
    def g(*a):
        if a not in cache: cache[a] = fn(*a)
        return cache[a]
    return g

def dance(ds, r, p, k, mode="ok"):
    seq = list(ds) if mode != "digits-from-top" else list(reversed(ds))
    for d in seq:
        if d is False:
            p, k = memo(pT(p)), memo(kT(p, k, r))
        else:
            p, k = split(p, k, r, mode); p, k = memo(p), memo(k); r = r * 2
    return r, p, k

def Mfin(R, p, k):
    return [[(2 * p(s, 0) if s == s1 else (2 * k(s, s1, 0) if s1 < s else 0)) for s1 in range(R)] for s in range(R)]

def clocks(n, m, r, h, shift=0):
    out = []
    for j in range(n):
        e = h + j + shift
        if e > 0: out += [2 ** e] * (r * 2 ** (n + m - 1 - j))
    return out

# closed form of C10 / Theorem 4.4 (cross-check)
def qpoly(I, k):
    q = {frozenset(): -1}
    for t in range(k):
        sq = {}
        for a, x in q.items():
            for b, y in q.items():
                if not (a & b): sq[a | b] = sq.get(a | b, 0) + x * y
        if t in I:
            for a, x in q.items():
                if t not in a: sq[a | {t}] = sq.get(a | {t}, 0) - x
        q = {a: x for a, x in sq.items() if x != 0}
    return q
def Mclosed(ds, alpha, i):
    k = len(ds); K = 2 ** k; I = [t for t in range(k) if ds[t]]
    q = qpoly(set(I), k)
    dancers = [frozenset(c) for L in range(len(I) + 1) for c in itertools.combinations(I, L)]
    o = lambda D: sum(2 ** t for t in D)
    from fractions import Fraction
    M = []
    for D in dancers:
        row = []
        for D1 in dancers:
            if not D1 <= D: row.append(0); continue
            Dl = D - D1; prod = 1
            for d in range(o(D), o(D1) + K): prod *= 2 ** alpha * (i + d)
            v = -Fraction(2) ** (1 - K + o(Dl)) * q.get(Dl, 0) * prod
            assert v.denominator == 1; row.append(int(v))
        M.append(row)
    return M

lists = [tuple(x) for n in range(1, 5) for x in itertools.product([False, True], repeat=n) if n + sum(x) <= 5]
# Proposition 4.3 for sigma
for ds in lists:
    n = len(ds); m = sum(ds)
    dim, fl, F = tower(ds)
    for alpha in (1, 2):
        for i in range(4):
            psig = lambda s, f, a=alpha, i=i: 2 ** (a - 1) * (i + f)
            ksig = lambda u, s, f: 0
            lhs = inv(paysys(1, dim, fl, F, psig, ksig))
            R, pk, kk = dance(ds, 1, psig, ksig)
            M = Mfin(R, pk, kk)
            rhs = sorted(clocks(n, m, 1, 0) + inv([[2 ** n * x for x in row] for row in M]))
            ok("prop43", lhs == rhs, (ds, alpha, i))
            ok("D4-triangular-even", all(M[s][s1] == 0 for s in range(R) for s1 in range(R) if s < s1) and all(x % 2 == 0 for row in M for x in row), (ds, alpha, i))
            ok("cross-closed-form", inv(M) == inv(Mclosed(ds, alpha, i)), (ds, alpha, i))
            # controls
            if len(set(ds)) > 1 or n > 1:
                R2, p2, k2 = dance(ds, 1, psig, ksig, "digits-from-top")
                if R2 == R and sorted(clocks(n, m, 1, 0) + inv([[2 ** n * x for x in row] for row in Mfin(R2, p2, k2)])) != lhs:
                    ctrl["digits-from-top"] += 1
            if sorted(clocks(n, m, 1, 0, 1) + inv([[2 ** n * x for x in row] for row in M])) != lhs: ctrl["clocks-exp-a+1"] += 1
            if sorted(clocks(n, m, 1, 0) + inv([[2 ** (n - 1) * x for x in row] for row in M])) != lhs: ctrl["final-2^(k-1)"] += 1
# (D1) with r = 2, random data, h in {0, 1}
for trial in range(60):
    rnd = random.Random(trial)
    ds = rnd.choice([d for d in lists if len(d) + sum(d) <= 4])
    n = len(ds); m = sum(ds); r = 2
    dim, fl, F = tower(ds)
    L = 2 ** (n + 3) + 10
    P = [[rnd.randint(-3, 3) for _ in range(L)] for _ in range(r)]
    Kp = [[[rnd.randint(-3, 3) for _ in range(L)] for _ in range(r)] for _ in range(r)]
    p0 = lambda s, f: P[s][f]; k0 = lambda u, s, f: Kp[u][s][f]
    for h in (0, 1):
        lhs = inv([[2 ** h * x for x in row] for row in paysys(r, dim, fl, F, p0, k0)])
        R, pk, kk = dance(ds, r, p0, k0)
        rhs = sorted(clocks(n, m, r, h) + inv([[2 ** (h + n) * x for x in row] for row in Mfin(R, pk, kk)]))
        ok("D1-random-r2", lhs == rhs, (trial, ds, h))
        if any(ds):
            R3, p3, k3 = dance(ds, r, p0, k0, "relabel-reversed")
            if sorted(clocks(n, m, r, h) + inv([[2 ** (h + n) * x for x in row] for row in Mfin(R3, p3, k3)])) != lhs:
                ctrl["relabel-reversed"] += 1
print("COUNTS", cnt)
print("FAILURES", len(fails), fails[:10])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
