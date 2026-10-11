# Brute force for C14 (Theorem 4.4, the windows, and Theorem D), exact rationals.
# Every claim of C14 is tested on the dance of C13 (halved data, relabelling (s, j) -> 2s + j).
import itertools
from fractions import Fraction as Fr

cnt = {}; fails = []
ctrl = {}
def ok(name, c, info):
    cnt[name] = cnt.get(name, 0) + 1
    if not c: fails.append((name, info))
def fire(name, c):
    ctrl[name] = ctrl.get(name, 0) + (1 if c else 0)

def memo(fn):
    cache = {}
    def g(*a):
        if a not in cache: cache[a] = fn(*a)
        return cache[a]
    return g

def pT(p): return lambda s, f: -p(s, 2 * f) * p(s, 2 * f + 1)
def kT(p, k):
    def g(u, s1, f):
        mid = sum(k(s, s1, 2 * f + 1) * k(u, s, 2 * f) for s in range(s1 + 1, u))
        return -(p(s1, 2 * f + 1) * k(u, s1, 2 * f) + k(u, s1, 2 * f + 1) * p(u, 2 * f) + mid)
    return g
def split(p, k):
    dec = lambda t: (t // 2, t % 2)
    def p2(t, f):
        s, X = dec(t)
        return -p(s, 2 * f) * p(s, 2 * f + 1) if X == 0 else -p(s, 2 * f + 1) * p(s, 2 * f + 2)
    def k2(t2, t1, f):
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

def dance(ds, p, k):
    r = 1
    for d in ds:
        if not d: p, k = memo(pT(p)), memo(kT(p, k))
        else:
            p, k = split(p, k); p, k = memo(p), memo(k); r *= 2
    return r, p, k

def oE(D): return sum(2 ** t for t in D)
def Iof(ds): return [t for t in range(len(ds)) if ds[t]]
def Dset(ds, s, rev=False):
    I = Iof(ds); m = len(I)
    return frozenset(t for l, t in enumerate(I) if (s >> ((l if rev else m - 1 - l))) & 1)

def starMul(f, g, D):
    return sum(f(frozenset(D1)) * g(D - frozenset(D1)) for L in range(len(D) + 1) for D1 in itertools.combinations(sorted(D), L))
def a_fun(I):
    I = set(I)
    @memo
    def a(t, D):
        if t == 0: return -(1 if not D else 0)
        return starMul(lambda X: a(t - 1, X), lambda X: a(t - 1, X), D) - ((1 if (t - 1) in I else 0) * (1 if (t - 1) in D else 0) * a(t - 1, D - {t - 1}) if (t - 1) in D else 0)
    return a
def c_fun(I):
    I = set(I)
    @memo
    def c(h, D):
        if h == 0: return Fr(1 if not D else 0)
        return Fr(-1, 2) * starMul(lambda X: c(h - 1, X), lambda X: c(h - 1, X), D) - ((1 if (h - 1) in I else 0) * c(h - 1, D - {h - 1}) if (h - 1) in D else 0)
    return c
def pi0(alpha, i, d): return Fr(2) ** alpha * (i + d)
def prod(alpha, i, lo, hi):
    v = Fr(1)
    for d in range(lo, hi): v *= pi0(alpha, i, d)
    return v
def Mc(I, k, alpha, i, D, D1, a):
    De = D - D1
    return -Fr(2) ** (1 - 2 ** k + oE(De)) * a(k, De) * prod(alpha, i, oE(D), oE(D1) + 2 ** k)
def v2(x):
    x = abs(x); v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def delta(k, De):
    return 0 if not De else k - len(De) - min(De)

lists = [tuple(x) for n in range(1, 6) for x in itertools.product([False, True], repeat=n) if n + sum(x) <= 6]
for ds in lists:
    k = len(ds); I = Iof(ds); m = len(I)
    a = a_fun(I); c = c_fun(I)
    for alpha in (1, 2, 3):
        for i in range(4):
            psig = lambda s, f, al=alpha, i=i: Fr(2) ** (al - 1) * (i + f)
            ksig = lambda u, s, f: Fr(0)
            # (W) at every h
            for h in range(k + 1):
                pre = ds[:h]
                R, ph, kh = dance(pre, psig, ksig)
                for f in range(3):
                    for s in range(R):
                        D = Dset(pre, s)
                        want = c(h, frozenset()) / 2 * prod(alpha, i, 2 ** h * f + oE(D), 2 ** h * f + oE(D) + 2 ** h)
                        ok("W-payment", ph(s, f) == want, (ds, alpha, i, h, f, s))
                        fire("W-without-half", ph(s, f) != c(h, frozenset()) * prod(alpha, i, 2 ** h * f + oE(D), 2 ** h * f + oE(D) + 2 ** h))
                        for s1 in range(s):
                            D1 = Dset(pre, s1)
                            if D1 <= D:
                                want = c(h, D - D1) / 2 * prod(alpha, i, 2 ** h * f + oE(D), 2 ** h * f + oE(D1) + 2 ** h)
                            else:
                                want = 0
                            ok("W-coupling", kh(s, s1, f) == want, (ds, alpha, i, h, f, s, s1))
                            if m >= 2 and h == k:
                                Dr, D1r = Dset(pre, s, True), Dset(pre, s1, True)
                                wr = c(h, Dr - D1r) / 2 * prod(alpha, i, 2 ** h * f + oE(Dr), 2 ** h * f + oE(D1r) + 2 ** h) if D1r <= Dr else 0
                                fire("W-bits-reversed", kh(s, s1, f) != wr)
            # Theorem 4.4 and Theorem D
            R, pk, kk = dance(ds, psig, ksig)
            assert R == 2 ** m
            for s in range(R):
                for s1 in range(R):
                    M = 2 * pk(s, 0) if s == s1 else (2 * kk(s, s1, 0) if s1 < s else 0)
                    D, D1 = Dset(ds, s), Dset(ds, s1)
                    want = Mc(I, k, alpha, i, D, D1, a) if D1 <= D else 0
                    ok("thm-4.4", M == want, (ds, alpha, i, s, s1))
                    if s1 < s and not (D1 <= D):
                        fire("thm-4.4-claim-on-non-nested", M != Mc(I, k, alpha, i, D, D1, a))
                    ok("D-ii-integer", M.denominator == 1, (ds, alpha, i, s, s1))
                    if D1 <= D and 0 < i + oE(D):
                        De = D - D1
                        val = 1 - 2 ** k + oE(De) + delta(k, De) + sum(alpha + v2(i + d) for d in range(oE(D), oE(D1) + 2 ** k))
                        ok("D-iii-valuation", M != 0 and v2(M.numerator) == val, (ds, alpha, i, s, s1))
                        fire("D-iii-valuation+1", M != 0 and v2(M.numerator) != val + 1)
                    if D1 <= D and i + oE(D) == 0:
                        ok("D-iii-zero-entry-when-i+oD=0", M == 0, (ds, alpha, i, s, s1))
                    fire("thm-4.4-c-instead-of-a", D1 <= D and M != -Fr(2) ** (1 - 2 ** k + oE(D - D1)) * c(k, D - D1) * prod(alpha, i, oE(D), oE(D1) + 2 ** k))
print("COUNTS", cnt)
print("FAILURES", len(fails), fails[:10])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
