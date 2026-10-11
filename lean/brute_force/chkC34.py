#!/usr/bin/env python3
"""Brute force for piece C34 (Bai's two counts: Lemma 9.1, Corollary 1.5). Grepy Escribano, 8 Oct 2026.
The family machinery (clocks of §1.2, PAVA with rounding, multiplicities, 2-adic Smith form) is copied
verbatim from chkC33.py (written from §1.2 only). New here:
  layers l0 = log2 |G/2G| = #factors, l1 = log2 |2G/4G| = #factors with exponent >= 2 (inf counts in both);
  1. (B1), (B2) from the Smith form of the Laplacian of Q_n, 1 <= n <= 9; n = 2, 3 by hand;
  2. (A1) raw clocks >= 2 for every k <= 7, I ⊆ [0,k), D ⊆ I, i <= 12, (i, D) != (0, ∅)
     (the family λ = 2^k + o_I − 1); (A2) integer fit >= min on random sequences;
  3. (A3), (F1), (F2) for λ <= 200, i <= 12;
  4. (S1) |Idx(ds λ)| = 2^{k+|I|} from the tower recursion; (S2), (S3), (B1), (B2) from the families, n <= 40.
Controls (each must fire): a_n with 2^((n−1)/2); clocks >= 3; l0(Z_2) = 1; the factor a = 0 counted."""
import random
from collections import Counter
from fractions import Fraction
E = 60; MOD = 1 << E
checks = 0; fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def s2(x): return bin(x).count("1")
def kap(a, b): return s2(a) + s2(b) - s2(a + b)

def family(lam):
    x = lam + 1; k = x.bit_length() - 1
    I = [t for t in range(k) if (x >> t) & 1]
    return k, I
def dancers(I):
    """subsets of I in o-order: the dancer of rank p puts the bits of p on I (sorted)."""
    out = []
    for p in range(2 ** len(I)):
        out.append([I[j] for j in range(len(I)) if (p >> j) & 1])
    return out
def raw(lam, i, D, I, k, kshift=0):
    nxt = lambda t: min([u for u in I + [k] if u > t])
    o = sum(2 ** t for t in D); xi = lam + 1 - 2 * o
    h = sum(nxt(t) - t for t in D)
    return xi + v2(xi) + kap(i + o - 1 + kshift, xi) + h

def pava_int(xs):
    blocks = []  # [sum, count]
    for x in xs:
        blocks.append([x, 1])
        while len(blocks) > 1 and Fraction(blocks[-2][0], blocks[-2][1]) <= Fraction(blocks[-1][0], blocks[-1][1]):
            s, c = blocks.pop(); blocks[-1][0] += s; blocks[-1][1] += c
    out = []
    for s, p in blocks:
        q, r = divmod(s, p)
        out += [q + 1] * r + [q] * (p - r)
    return out

def Xfam(lam, i, pool=True, ksh=0, pool_inf=False, a0=False):
    k, I = family(lam)
    ex = []
    for a in range(0 if a0 else 1, k):
        ex += [max(a, 1)] * (2 ** (len(I) + k - 1 - a))
    Ds = dancers(I)
    if i >= 1:
        u = [raw(lam, i, D, I, k, ksh) for D in Ds]
        ex += pava_int(u) if pool else u
    else:
        u = [raw(lam, 0, D, I, k, ksh) for D in Ds[1:]]
        if pool_inf:
            # control: the shift-0 clocks computed with the shift-1 formula
            u = [raw(lam, 1, D, I, k, ksh) for D in Ds[1:]]
        ex += [None] + (pava_int(u) if pool else u)
    return ex

def tdot(l):
    if l == 0: return [1]
    if l % 2 == 1: return [l + 1]
    return [l - 1, l - 1] + [2 * x + 1 for x in tdot((l - 2) // 2)]
def mult(n):
    c = Counter({0: 1})
    for _ in range(n):
        d = Counter()
        for lam, cnt in c.items():
            for mu in tdot(lam): d[mu] += cnt
        c = d
    return c

def smith2(M):
    n = len(M); A = [[x % MOD for x in r] for r in M]
    live_r = set(range(n)); live_c = set(range(n)); out = []
    def val(x):
        if x == 0: return None
        return v2(x)
    while live_r:
        best = None
        for i in live_r:
            row = A[i]
            for j in live_c:
                if row[j]:
                    vv = v2(row[j])
                    if best is None or vv < best[0]:
                        best = (vv, i, j)
                        if vv == 0: break
            if best and best[0] == 0: break
        if best is None: break
        vv, pi, pj = best; out.append(vv)
        inv = pow(A[pi][pj] >> vv, -1, MOD)
        prow = A[pi]
        for i in live_r:
            if i != pi and A[i][pj]:
                c = ((A[i][pj] >> vv) * inv) % MOD
                row = A[i]
                for j in live_c: row[j] = (row[j] - c * prow[j]) % MOD
        live_r.discard(pi); live_c.discard(pj)
    out += [None] * len(live_r)
    return out
def key(e): return (e is None, e if e is not None else 0)
def lap(n):
    N = 1 << n; M = [[0] * N for _ in range(N)]
    for g in range(N):
        M[g][g] = n
        for t in range(n): M[g][g ^ (1 << t)] -= 1
    return M

def rhs(n, **kw):
    ex = []
    for lam, c in mult(n).items():
        for _ in range(c): ex += Xfam(lam, (n - lam) // 2, **kw)
    return sorted(ex, key=key)


def ds(l):
    if l == 0: return []
    if l % 2 == 1: return [False] + ds((l - 1) // 2)
    return [True] + ds((l - 2) // 2)

def layers(ex, inf_l0=1):
    l0 = sum(1 for e in ex if e is None or e >= 1) - (0 if inf_l0 == 1 else ex.count(None))
    l1 = sum(1 for e in ex if e is None or e >= 2)
    return l0, l1
def a_n(n, ctrl=False):
    return 2 ** (n - 2) - 2 ** (((n - 1) if ctrl else (n - 2)) // 2)

# 1. from the Smith form
for n in range(1, 10):
    S = [e for e in smith2(lap(n)) if e is not None and e > 0]   # Syl2 K(Q_n): drop the Z
    l0, l1 = layers(S)
    ok(l0 == 2 ** (n - 1) - 1, ("B1 smith", n, l0))
    if n >= 2: ok(l1 == 2 ** (n - 1) - 1 - a_n(n), ("B2 smith", n, l1))
ok(sorted(e for e in smith2(lap(2)) if e) == [2], "K(Q2)=Z/4")
ok(sorted(e for e in smith2(lap(3)) if e is not None and e > 0) == [1, 3, 3], "K(Q3)")
# 2. (A1), (A2)
for k in range(1, 8):
    for mask in range(2 ** k):
        I = [t for t in range(k) if (mask >> t) & 1]
        lam = 2 ** k + sum(2 ** t for t in I) - 1
        ok(family(lam) == (k, I), ("fam", k, I))
        for D in dancers(I):
            for i in range(0, 13):
                if i == 0 and not D: continue
                ok(raw(lam, i, D, I, k) >= 2, ("A1", k, I, D, i))
random.seed(34)
for _ in range(3000):
    N = random.randint(1, 12); xs = [random.randint(-5, 9) for _ in range(N)]
    ok(min(pava_int(xs)) >= min(xs), ("A2", xs))
# 3. (A3), (F1), (F2)
def c1(lam):
    k, I = family(lam)
    return 2 ** (len(I) + k - 2) if k >= 2 else 0
for lam in range(1, 201):
    k, I = family(lam)
    for i in range(0, 13):
        X = Xfam(lam, i)
        big = X[sum(2 ** (len(I) + k - 1 - a) for a in range(1, k)):]
        ok(all(e is None or e >= 2 for e in big), ("A3", lam, i))
        l0, l1 = layers(X)
        ok(l0 == 2 ** (len(I) + k - 1), ("F1", lam, i))
        ok(l1 == 2 ** (len(I) + k - 1) - c1(lam), ("F2", lam, i))
# 4. (S1)–(S3), (B1), (B2) from the families
def idx_card(l):
    d = ds(l); c = 1
    for b in d: c *= 4 if b else 2
    return c
for lam in range(0, 300):
    k, I = family(lam) if lam else (0, [])
    ok(idx_card(lam) == 2 ** (k + len(I)), ("S1", lam))
for n in range(1, 41):
    c = mult(n)
    ok(sum(cnt * idx_card(l) for l, cnt in c.items()) == 2 ** n, ("S2", n))
    ok(4 * sum(cnt * c1(l) for l, cnt in c.items()) + 2 * c[1] + 4 * c[2] == 2 ** n, ("S3", n))
    ok(all((len(ds(l)) <= 1) == (l in (1, 2)) for l in c if c[l] and l >= 1), ("S3 k<=1", n))
    L0 = sum(cnt * 2 ** (len(family(l)[1]) + family(l)[0] - 1) for l, cnt in c.items())
    L1 = sum(cnt * (2 ** (len(family(l)[1]) + family(l)[0] - 1) - c1(l)) for l, cnt in c.items())
    ok(L0 - 1 == 2 ** (n - 1) - 1, ("B1 fam", n))   # minus the Z_2 of the family λ = n
    if n >= 2: ok(L1 - 1 == 2 ** (n - 1) - 1 - a_n(n), ("B2 fam", n))
print("checks", checks, "fails", fails)

fired = 0
if any(layers([e for e in smith2(lap(n)) if e is not None and e > 0])[1] != 2 ** (n - 1) - 1 - a_n(n, ctrl=True) for n in range(2, 10)): fired += 1
else: print("SILENT a_n")
if any(raw(2 ** k + sum(2 ** t for t in I) - 1, i, D, I, k) < 3 for k in range(1, 6) for mask in range(2 ** k) for I in [[t for t in range(k) if (mask >> t) & 1]] for D in dancers(I) for i in range(13) if not (i == 0 and not D)): fired += 1
else: print("SILENT >=3")
if any(layers(Xfam(n, 0), inf_l0=0)[0] != 2 ** (len(family(n)[1]) + family(n)[0] - 1) for n in range(1, 30)): fired += 1
else: print("SILENT l0 inf")
if any(layers(Xfam(l, 1, a0=True))[0] != 2 ** (len(family(l)[1]) + family(l)[0] - 1) for l in range(1, 60)): fired += 1
else: print("SILENT a0")
print("controls fired", fired, "of 4")
