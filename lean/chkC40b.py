#!/usr/bin/env python3
"""Brute force for Lean piece C40b (paper v8 §10.3, Lemma 10.6: the formal dance of payment
systems). Grepy Escribano, 9 Oct 2026. Exact integers/rationals.

Encoding as in C40: a formal operator x is a dict (m, f) -> x_m(f), coefficient of F^(m) at the
TARGET floor f; product (xy)_m(f) = sum_a C(m,a) x_a(f) y_{m-a}(f-a).
A system is an r x r matrix of formal operators, G[s][s'] maps source s' to coordinate s.
paySys(p, kappa): diagonal fd1 + dg(2 p_s), below the diagonal dg(2 kappa_{s s'}), above 0;
dg(q) at a negative floor is 0 (p, kappa live on floors in N).
Twist blocks of G: P = tw10 G, C = tw11 G, B = tw00 G, Dd = tw01 G (entrywise).
V-split of G: index (s, v); [(s,0),(s',0)] = G, [(s,1),(s',0)] = vprime G, [(s,1),(s',1)] = vplus G,
[(s,0),(s',1)] = 0. Next system: S = Dd - B P^{-1} C, G' = S / 2.
Agreement x ~ y: x_m(f) = y_m(f) for every f >= m (the values that act)."""
import random
from fractions import Fraction
from math import comb

random.seed(4002)
checks = fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 30: print("FAIL", msg)

MMAX = 4
FLO = -6

def get(x, m, f): return x.get((m, f), Fraction(0))
def zero(): return {}
def add(x, y): return {k: get(x, *k) + get(y, *k) for k in set(x) | set(y)}
def sub(x, y): return {k: get(x, *k) - get(y, *k) for k in set(x) | set(y)}
def smul(c, x): return {k: c * v for k, v in x.items()}
def mul(x, y, FH):
    z = {}
    for m in range(MMAX):
        for f in range(FLO, FH):
            s = Fraction(0)
            for a in range(m + 1):
                s += comb(m, a) * get(x, a, f) * get(y, m - a, f - a)
            if s: z[(m, f)] = s
    return z
def fd(m, FH): return {(m, f): Fraction(1) for f in range(FLO, FH)}
def dg(q, FH):  # q : N -> value, 0 at negative floors
    return {(0, f): Fraction(q(f)) for f in range(0, FH)}

def dfi(s):
    p = 1
    for k in range(1, 2 * s, 2): p *= k
    return Fraction(1, p)
def tw(x, FH, wrong=None):
    t00, t11, t10, t01 = {}, {}, {}, {}
    for q in range(MMAX):
        for f in range(FLO, FH):
            t00[(q, f)] = dfi(q) * get(x, 2 * q, 2 * f)
            t11[(q, f)] = dfi(q) * get(x, 2 * q, 2 * f + 1)
            t10[(q, f)] = dfi(q + 1) * (get(x, 2 * q, 2 * f + 1) if wrong == "t10" else get(x, 2 * q + 1, 2 * f + 1))
            if q + 1 < MMAX:
                t01[(q + 1, f)] = (2 * q + 2) * dfi(q + 1) * get(x, 2 * q + 1, 2 * f)
    return t00, t11, t10, t01
def vplus(x, FH): return {(m, f): get(x, m, f + 1) for m in range(MMAX) for f in range(FLO, FH)}
def vprime(x, FH): return {(m, f): get(x, m + 1, f + 1) for m in range(MMAX) for f in range(FLO, FH)}

def agree(x, y, FH):
    return all(get(x, m, f) == get(y, m, f) for m in range(MMAX) for f in range(m, FH))
def exact(x, y, FH):   # every floor whose inputs lie inside the computed range (f >= -2: negative floors included)
    return all(get(x, m, f) == get(y, m, f) for m in range(MMAX) for f in range(-2, FH))

# systems
def mmul(X, Y, FH):
    n = len(X)
    return [[ (lambda acc: acc)( __import__('functools').reduce(lambda a, t: add(a, mul(X[i][t], Y[t][j], FH)), range(n), {}) ) for j in range(n)] for i in range(n)]
def msub(X, Y): return [[sub(a, b) for a, b in zip(ra, rb)] for ra, rb in zip(X, Y)]
def mident(n, FH): return [[fd(0, FH) if i == j else {} for j in range(n)] for i in range(n)]
def blocks(G, FH, wrong=None):
    n = len(G); P = [[None] * n for _ in range(n)]; C = [[None] * n for _ in range(n)]
    B = [[None] * n for _ in range(n)]; D = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            t00, t11, t10, t01 = tw(G[i][j], FH, wrong)
            P[i][j], C[i][j], B[i][j], D[i][j] = t10, t11, t00, t01
    return P, C, B, D
def vsplit(G, FH):
    n = len(G); H = [[{} for _ in range(2 * n)] for _ in range(2 * n)]
    for s in range(n):
        for s2 in range(n):
            H[2 * s][2 * s2] = G[s][s2]
            H[2 * s + 1][2 * s2] = vprime(G[s][s2], FH)
            H[2 * s + 1][2 * s2 + 1] = vplus(G[s][s2], FH)
    return H   # index 2s+v = splitIso (s, v)

def paySys(p, kap, n, FH):
    G = [[{} for _ in range(n)] for _ in range(n)]
    for s in range(n):
        for s2 in range(n):
            if s == s2: G[s][s2] = add(fd(1, FH), dg(lambda f: 2 * p[s](f), FH))
            elif s2 < s: G[s][s2] = dg(lambda f, s=s, s2=s2: 2 * kap[s][s2](f), FH)
    return G

# C11/C12 data (halved), exactly as in the Lean files
def pT(p): return [ (lambda f, s=s: -(p[s](2 * f) * p[s](2 * f + 1))) for s in range(len(p))]
def kT(p, k):
    n = len(p)
    return [[ (lambda f, u=u, s2=s2: -(p[s2](2 * f + 1) * k[u][s2](2 * f) + k[u][s2](2 * f + 1) * p[u](2 * f)
              + sum(k[s][s2](2 * f + 1) * k[u][s](2 * f) for s in range(n) if s2 < s < u))) for s2 in range(n)] for u in range(n)]
def pSp(p):   # on Lex (S x Fin 2), relabelled by 2s+v
    n = len(p); out = []
    for s in range(n):
        out.append(lambda f, s=s: -(p[s](2 * f) * p[s](2 * f + 1)))
        out.append(lambda f, s=s: -(p[s](2 * f + 1) * p[s](2 * f + 2)))
    return out
def kSp(p, k):
    n = len(p)
    def val(qp, q, f):
        u, X = divmod(qp, 2); s2, Y = divmod(q, 2)
        if Y == 0 and X == 0:
            if s2 < u:
                return -(p[s2](2 * f + 1) * k[u][s2](2 * f) + k[u][s2](2 * f + 1) * p[u](2 * f)
                         + sum(k[s][s2](2 * f + 1) * k[u][s](2 * f) for s in range(n) if s2 < s < u))
            return 0
        if Y == 1 and X == 1:
            if s2 < u:
                return -(p[s2](2 * f + 2) * k[u][s2](2 * f + 1) + k[u][s2](2 * f + 2) * p[u](2 * f + 1)
                         + sum(k[s][s2](2 * f + 2) * k[u][s](2 * f + 1) for s in range(n) if s2 < s < u))
            return 0
        if Y == 0 and X == 1:
            if u == s2: return -p[s2](2 * f + 1)
            if s2 < u: return -k[u][s2](2 * f + 1)
            return 0
        return 0
    return [[(lambda f, qp=qp, q=q: val(qp, q, f)) for q in range(2 * n)] for qp in range(2 * n)]

def rnd_data(n, lo=-5, hi=5):
    tabp = [[random.randint(lo, hi) for _ in range(800)] for _ in range(n)]
    tabk = [[[random.randint(lo, hi) for _ in range(800)] for _ in range(n)] for _ in range(n)]
    p = [(lambda f, s=s: tabp[s][f]) for s in range(n)]
    k = [[(lambda f, u=u, s=s: tabk[u][s][f]) for s in range(n)] for u in range(n)]
    return p, k

def is_ident(P, FH, exactly=True):
    n = len(P); I = mident(n, FH)
    f = exact if exactly else agree
    return all(f(P[i][j], I[i][j], FH) for i in range(n) for j in range(n))

FH = 14
# ---------- (L1) the twist move of a payment system: P = 1 exactly, S = 2 paySys(pT, kT) exactly ----------
for n in (1, 2, 3):
    for _ in range(5):
        p, k = rnd_data(n)
        G = paySys(p, k, n, 2 * FH + 4)
        P, C, B, D = blocks(G, FH)
        ok(is_ident(P, FH), ("twist P = 1", n))
        S = msub(D, mmul(B, C, FH))
        G2 = paySys(pT(p), kT(p, k), n, FH)
        ok(all(exact(S[i][j], smul(2, G2[i][j]), FH) for i in range(n) for j in range(n)), ("twist S exact", n))

# ---------- (L2) the split move: P = 1 exactly, S ~ 2 paySys(pSp, kSp) (agreement), and exactness fails ----------
exact_fail_seen = False
for n in (1, 2, 3):
    for _ in range(5):
        p, k = rnd_data(n)
        G = paySys(p, k, n, 2 * FH + 8)
        H = vsplit(G, 2 * FH + 6)
        P, C, B, D = blocks(H, FH)
        ok(is_ident(P, FH), ("split P = 1", n))
        S = msub(D, mmul(B, C, FH))
        G2 = paySys(pSp(p), kSp(p, k), 2 * n, FH)
        ok(all(agree(S[i][j], smul(2, G2[i][j]), FH) for i in range(2 * n) for j in range(2 * n)), ("split S agree", n))
        if not all(exact(S[i][j], smul(2, G2[i][j]), FH) for i in range(2 * n) for j in range(2 * n)):
            exact_fail_seen = True
# Sealed expectation (Grepy, before the run): exact equality would FAIL at some negative floor. It did NOT fail
# on any floor f >= -2 tested; recorded as an observation, not claimed in the file (the file states agreement).
print("observation: split S exact on f >= -2 in every sample:", not exact_fail_seen)

# ---------- (L3) agreement is a congruence: product, tw, vplus, vprime ----------
def junk(x, FH):  # change x only at floors f < m
    y = dict(x)
    for m in range(MMAX):
        for f in range(FLO, m):
            y[(m, f)] = get(x, m, f) + random.randint(1, 9)
    return y
def rnd_op(FH): return {(m, f): Fraction(random.randint(-4, 4)) for m in range(MMAX) for f in range(FLO, FH)}
for _ in range(20):
    x, y = rnd_op(2 * FH + 4), rnd_op(2 * FH + 4)
    xj, yj = junk(x, 2 * FH + 4), junk(y, 2 * FH + 4)
    ok(agree(mul(x, y, FH), mul(xj, yj, FH), FH), "congr mul")
    for a, b in zip(tw(x, FH), tw(xj, FH)): ok(agree(a, b, FH), "congr tw")
    ok(agree(vplus(x, FH), vplus(xj, FH), FH), "congr vplus")
    ok(agree(vprime(x, FH), vprime(xj, FH), FH), "congr vprime")

# ---------- (L4) the formal dance of sigma = Mfin(dance ds 1 p_sigma 0) ----------
def dance_data(ds, p, k):
    for d in ds:
        if not d: p, k = pT(p), kT(p, k)
        else: p, k = pSp(p), kSp(p, k)
    return p, k
def Mfin(p, k):
    n = len(p)
    return [[2 * p[s](0) if s == s2 else (2 * k[s][s2](0) if s2 < s else 0) for s2 in range(n)] for s in range(n)]
def formal_dance(ds, G, FH0, scale=1):
    FHc = FH0
    for d in ds:
        H = vsplit(G, 2 * FHc + 6) if d else G
        FHn = FHc // 2 - 2
        P, C, B, D = blocks(H, FHn)
        if not is_ident(P, FHn, exactly=False): return None
        # P = 1 (mod agreement): S = D - B C ; for scale u, P = u * 1, P^{-1} = u^{-1}
        n = len(H)
        Pinv = [[smul(Fraction(1, scale), fd(0, FHn)) if i == j else {} for j in range(n)] for i in range(n)]
        S = msub(D, mmul(mmul(B, Pinv, FHn), C, FHn))
        G = [[smul(Fraction(1, 2), S[i][j]) for j in range(n)] for i in range(n)]
        FHc = FHn
    return [[get(G[i][j], 0, 0) for j in range(len(G))] for i in range(len(G))]

def ds_of(l):
    out = []
    while l > 0:
        if l % 2 == 1: out.append(False); l = (l - 1) // 2
        else: out.append(True); l = (l - 2) // 2
    return out
for l in range(0, 16):
    ds = ds_of(l)
    for alpha in (1, 2, 3):
        for i in (0, 1, 2, 5):
            ps = [lambda f, a=alpha, i=i: 2 ** (a - 1) * (i + f)]
            ks = [[lambda f: 0]]
            FH0 = 2 ** (len(ds) + 2) + 40
            G = paySys(ps, ks, 1, 2 * FH0 + 8)
            M = formal_dance(ds, G, FH0)
            pd, kd = dance_data(ds, ps, ks)
            ok(M is not None and M == Mfin(pd, kd), ("dance sigma", l, alpha, i))
# ---------- (L5) M_w(uG) = u M_w(G) for u = 3, -1 ----------
for l in (1, 2, 5, 6):
    ds = ds_of(l)
    for u in (3, -1):
        p, k = rnd_data(2)
        FH0 = 2 ** (len(ds) + 2) + 40
        G = paySys(p, k, 2, 2 * FH0 + 8)
        M1 = formal_dance(ds, G, FH0)
        Gu = [[smul(u, G[i][j]) for j in range(2)] for i in range(2)]
        # scaled dance: P = u 1, S = u (D - B C)  -> next system u G'
        FHc = FH0; Gc = Gu; scale = u
        for d in ds:
            H = vsplit(Gc, 2 * FHc + 6) if d else Gc
            FHn = FHc // 2 - 2
            P, C, B, D = blocks(H, FHn)
            n = len(H)
            ok(all(agree(P[a][b], smul(u, fd(0, FHn)) if a == b else {}, FHn) for a in range(n) for b in range(n)), "uP")
            Pinv = [[smul(Fraction(1, u), fd(0, FHn)) if a == b else {} for b in range(n)] for a in range(n)]
            S = msub(D, mmul(mmul(B, Pinv, FHn), C, FHn))
            Gc = [[smul(Fraction(1, 2), S[a][b]) for b in range(n)] for a in range(n)]
            FHc = FHn
        Mu = [[get(Gc[a][b], 0, 0) for b in range(len(Gc))] for a in range(len(Gc))]
        ok(Mu == [[u * v for v in row] for row in M1], ("scale", l, u))

# ---------- controls (each must fire) ----------
fired = 0
# C1: kT with the wrong order in the middle sum -> twist S differs
p, k = rnd_data(3); G = paySys(p, k, 3, 2 * FH + 4); P, C, B, D = blocks(G, FH); S = msub(D, mmul(B, C, FH))
def kT_bad(p, k):
    n = len(p)
    return [[ (lambda f, u=u, s2=s2: -(p[s2](2 * f + 1) * k[u][s2](2 * f) + k[u][s2](2 * f + 1) * p[u](2 * f)
              + sum(k[s][s2](2 * f) * k[u][s](2 * f + 1) for s in range(n) if s2 < s < u))) for s2 in range(n)] for u in range(n)]
G2 = paySys(pT(p), kT_bad(p, k), 3, FH)
fired += not all(exact(S[i][j], smul(2, G2[i][j]), FH) for i in range(3) for j in range(3))
# C2: P read as tw11 (the coefficient of F^(2q) instead of F^(2q+1)): P is not the identity
P2, _, _, _ = blocks(paySys(p, k, 3, 2 * FH + 4), FH, wrong="t10")
fired += not is_ident(P2, FH)
# C3: split compared without the shift (pSp's C-slot read at (2f, 2f+1))
def pSp_bad(p):
    out = []
    for s in range(len(p)):
        out.append(lambda f, s=s: -(p[s](2 * f) * p[s](2 * f + 1)))
        out.append(lambda f, s=s: -(p[s](2 * f) * p[s](2 * f + 1)))
    return out
p, k = rnd_data(2); H = vsplit(paySys(p, k, 2, 2 * FH + 8), 2 * FH + 6); P, C, B, D = blocks(H, FH); S = msub(D, mmul(B, C, FH))
G2 = paySys(pSp_bad(p), kSp(p, k), 4, FH)
fired += not all(agree(S[i][j], smul(2, G2[i][j]), FH) for i in range(4) for j in range(4))
# C4: the dance compared with the data dance in which a split step is taken as a twist step
ds = ds_of(6); ps = [lambda f: 2 * f + 1]; ks = [[lambda f: 0]]
FH0 = 2 ** (len(ds) + 2) + 40
M = formal_dance(ds, paySys(ps, ks, 1, 2 * FH0 + 8), FH0)
pd, kd = dance_data([False] * len(ds), ps, ks)
fired += (len(M) != len(pd)) or M != Mfin(pd, kd)
# C5: V-split with vprime and vplus exchanged -> split S does not agree
def vsplit_bad(G, FH):
    n = len(G); Hb = [[{} for _ in range(2 * n)] for _ in range(2 * n)]
    for s in range(n):
        for s2 in range(n):
            Hb[2 * s][2 * s2] = G[s][s2]; Hb[2 * s + 1][2 * s2] = vplus(G[s][s2], FH); Hb[2 * s + 1][2 * s2 + 1] = vprime(G[s][s2], FH)
    return Hb
p, k = rnd_data(2); Hb = vsplit_bad(paySys(p, k, 2, 2 * FH + 8), 2 * FH + 6); P, C, B, D = blocks(Hb, FH)
G2 = paySys(pSp(p), kSp(p, k), 4, FH)
fired += (not is_ident(P, FH)) or not all(agree(msub(D, mmul(B, C, FH))[i][j], smul(2, G2[i][j]), FH) for i in range(4) for j in range(4))
# C6: agreement replaced by agreement only for f >= 0 on m = 0 is NOT a congruence for products? (junk at f<m changes the product at f>=m?)
x, y = rnd_op(2 * FH + 4), rnd_op(2 * FH + 4)
def junk_low(x):  # change x_1 at f = 1 (f >= m): must break agreement of the product
    z = dict(x); z[(1, 1)] = get(x, 1, 1) + 7; return z
fired += not agree(mul(junk_low(x), y, FH), mul(x, y, FH), FH)
print("checks", checks, "failures", fails, "controls fired", fired, "of 6")
