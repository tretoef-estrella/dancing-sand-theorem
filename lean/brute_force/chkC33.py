#!/usr/bin/env python3
"""Brute force for piece C33 (the Main Theorem). Grepy Escribano, 8 Oct 2026.
Independent of every earlier script (written from §1.2 of paper v8 only):
  family λ: λ + 1 = 2^k + Σ_{t∈I} 2^t; next(t) = min{u ∈ I ∪ {k}, u > t}, h_t = next(t) − t;
  dancers D ⊆ I in o-order (increasing o_D = Σ_{t∈D} 2^t); ξ_D = λ + 1 − 2 o_D;
  u_i(D) = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D), φ(x) = x + v2(x), κ = carries; u_0(∅) = ∞;
  integer antitonic fit = PAVA (strictly decreasing block means, equal adjacent means merged),
  then a block of p positions with sum S becomes S mod p copies of ⌈S/p⌉ then p − S mod p of ⌊S/p⌋;
  at shift 0 the entry ∞ stands first and is not pooled;
  X(λ, i) = ⊕_{a=1}^{k−1} (Z/2^a)^{2^{|I|+k−1−a}} ⊕ ⊕_D Z/2^{ŷ_i(D)};
  multiplicities m_λ(n) by the rule V·[0] = [1], V·[2l+1] = [2l+2], V·[2l+2] = 2[2l+1] + Φ(V·[l]).
Checks:
  1. Main Theorem (M1): multiset of exponents of ⊕_λ X(λ,(n−λ)/2)^{m_λ(n)} = 2-adic Smith form of
     the Laplacian of Q_n (None = infinite), 1 ≤ n ≤ 9, and exactly one None.
  2. the worked example n = 6 of §1.2.
  3. (S1) λ + 1 = 2^k + o_I with k = len ds(λ), I = {t : ds_t = true}, λ ≤ 300; (S3) I ⊆ range k;
     (S5) the dancer of rank p (bits of p placed on I) has strictly increasing o_D, dancer 0 = ∅.
  4. (M3) support, (n − λ)/2 = 0 iff λ = n, m_n(n) = 1, m_0(n) = 0, n ≤ 40.
Controls (each must fire): unpooled clocks; κ(i + o_D, ξ_D); the shift-0 clocks computed with the\nshift-1 formula (replaces «∞ pooled at shift 0», which could not fail: ∞ first never pools);
the factor a = 0 of the small clocks counted as Z/2 (it is zero)."""
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

LAP = {}
for n in range(1, 10):
    LAP[n] = sorted([e for e in smith2(lap(n)) if e is None or e > 0], key=key)
    R = [e for e in rhs(n) if e is None or e > 0]
    ok(LAP[n] == sorted(R, key=key), ("main", n))
    ok(LAP[n].count(None) == 1, ("one Z2", n))
# 2. example n = 6
ok(Xfam(6, 0) == [1, 1, 1, 1, None, 6, 6, 3], ("ex6", Xfam(6, 0)))
ok(Xfam(4, 1) == [1, 1, 6, 6], ("ex4", Xfam(4, 1)))
ok(Xfam(2, 2) == [5, 2], ("ex2", Xfam(2, 2)))
tot = Counter();
for lam, c in mult(6).items():
    for e in Xfam(lam, (6 - lam) // 2): tot[e] += c
ok(dict(tot) == {1: 12, 2: 4, 3: 1, 5: 4, 6: 10, None: 1}, ("ex6 total", dict(tot)))
# 3. shape
def ds(l):
    if l == 0: return []
    if l % 2 == 1: return [False] + ds((l - 1) // 2)
    return [True] + ds((l - 2) // 2)
for lam in range(301):
    d = ds(lam); k = len(d); I = [t for t, b in enumerate(d) if b]
    ok(lam + 1 == 2 ** k + sum(2 ** t for t in I), ("S1", lam))
    ok(all(t < k for t in I), ("S3", lam))
    ok((k, I) == family(lam), ("ds = binary", lam))
    Ds = dancers(I); os_ = [sum(2 ** t for t in D) for D in Ds]
    ok(Ds[0] == [] and all(os_[p] < os_[p + 1] for p in range(len(os_) - 1)), ("S5", lam))
    ok((lam == 0) == (d == []), ("S2", lam))
# 4. M3
for n in range(1, 41):
    c = mult(n)
    for lam, cnt in c.items():
        if cnt:
            ok(1 <= lam <= n and lam % 2 == n % 2, ("support", n, lam))
            ok(((n - lam) // 2 == 0) == (lam == n), ("shift0", n, lam))
    ok(c[n] == 1 and c[0] == 0, ("mnn", n))
print("checks", checks, "fails", fails)

fired = 0
def fires(**kw):
    return any(sorted([e for e in rhs(n, **kw) if e is None or e > 0], key=key) != LAP[n] for n in range(1, 10))
for kw in (dict(pool=False), dict(ksh=1), dict(pool_inf=True), dict(a0=True)):
    if fires(**kw): fired += 1
    else: print("SILENT control", kw)
print("controls fired", fired, "of 4")
