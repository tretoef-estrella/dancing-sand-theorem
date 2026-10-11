#!/usr/bin/env python3
"""Brute force for piece C31 (Theorem 3.6, the family decomposition, and Lemma 3.7).
Grepy Escribano, 8 Oct 2026. Independent of every earlier script.
  1. Vdot as written in C31 (lists) agrees with the rule V·[λ] of §1.2 of the paper (formal sums),
     for λ ≤ 300.
  2. Characters: ch(V ⊗ T(λ)) = Σ_{μ ∈ Vdot λ} ch T(μ) for λ ≤ 200, with ch T computed from the
     definition of T (ch Φ(N) = (e + e^{-1})·ch N(e^2), ch(V ⊗ M) = (e + e^{-1}) ch M).
  3. Ranks: Σ_{λ ∈ L n} rank T(λ) = 2^n, and the characters: Σ_{λ ∈ L n} ch T(λ) = (e + e^{-1})^n,
     for n ≤ 22.
  4. Support: for n ≥ 1 every λ ∈ L n has 1 ≤ λ ≤ n and λ ≡ n (mod 2); L n is a permutation of
     flatMap (λ ↦ replicate (m λ n) λ) (range (n+1)).
  5. Lemma 3.7 for 1 ≤ n ≤ 60.
Controls: (a) a wrong rule (Vdot (2l+2) = [2l+1] ++ ...) fails the rank check; (b) a wrong rule
(Vdot (2l+2) without the map (2·+1)) fails the character check; (c) a wrong exponent in Lemma 3.7
(m_1(n) = 2^{(n+1)/2}) fails."""
import sys
from collections import Counter
from functools import lru_cache
sys.setrecursionlimit(100000)
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

def mk_vdot(rule):
    @lru_cache(None)
    def vd(l):
        if l == 0: return (1,)
        if l % 2 == 1: return (l + 1,)
        m = (l - 2) // 2
        if rule == "good": return (l - 1, l - 1) + tuple(2 * x + 1 for x in vd(m))
        if rule == "bad_a": return (l - 1,) + tuple(2 * x + 1 for x in vd(m))
        if rule == "bad_b": return (l - 1, l - 1) + tuple(vd(m))
    return vd
vd = mk_vdot("good")

# 1. the formal-sum rule of §1.2, written independently with Counters
@lru_cache(None)
def vsum(l):
    if l == 0: return Counter({1: 1})
    if l % 2 == 1: return Counter({l + 1: 1})
    m = (l - 2) // 2
    c = Counter({l - 1: 2})
    for nu, k in vsum(m).items(): c[2 * nu + 1] += k
    return c
for l in range(301): ok(Counter(vd(l)) == vsum(l), ("rule", l))

# characters as dicts weight -> multiplicity
def mul_v(ch):
    r = Counter()
    for w, k in ch.items(): r[w + 1] += k; r[w - 1] += k
    return +r
def frob(ch): return Counter({2 * w: k for w, k in ch.items()})
@lru_cache(None)
def chT(l):
    if l == 0: return Counter({0: 1})
    if l % 2 == 1: return mul_v(frob(chT((l - 1) // 2)))
    return mul_v(mul_v(frob(chT((l - 2) // 2))))
def rank(l): return sum(chT(l).values())
def chsum(lst):
    r = Counter()
    for x in lst: r.update(chT(x))
    return r

# 2. characters of V ⊗ T(λ)
for l in range(201): ok(mul_v(chT(l)) == chsum(vd(l)), ("char", l))

# 3., 4. the lists L n
def Lists(N, v):
    L = [(0,)]
    for n in range(N): L.append(tuple(x for lam in L[-1] for x in v(lam)))
    return L
L = Lists(22, vd)
for n in range(23):
    ok(sum(rank(x) for x in L[n]) == 2 ** n, ("rank", n))
    vn = Counter({0: 1})
    for _ in range(n): vn = mul_v(vn)
    ok(chsum(L[n]) == vn, ("chpow", n))
# multiplicities as Counters (the same recursion, summed), checked against the lists for n <= 22
C = [Counter({0: 1})]
for n in range(60):
    c = Counter()
    for lam, k in C[-1].items():
        for x in vd(lam): c[x] += k
    C.append(c)
for n in range(23): ok(Counter(L[n]) == C[n], ("counter", n))
def m(lam, n): return C[n][lam]
for n in range(1, 23):
    flat = [lam for lam in range(n + 1) for _ in range(m(lam, n))]
    ok(sorted(L[n]) == flat, ("perm", n))
for n in range(1, 61):
    ok(all(1 <= x <= n and (x - n) % 2 == 0 for x in C[n]), ("supp", n))
# 5. Lemma 3.7
for n in range(1, 61):
    ok(m(0, n) == 0, ("m0", n)); ok(m(n, n) == 1, ("mn", n))
    if n % 2 == 1: ok(m(1, n) == 2 ** ((n - 1) // 2), ("m1", n))
    else: ok(m(2, n) == 2 ** ((n - 2) // 2), ("m2", n))
print("checks", checks, "fails", fails)

# controls (each must FAIL)
fired = 0
La = Lists(14, mk_vdot("bad_a"))
if any(sum(rank(x) for x in La[n]) != 2 ** n for n in range(14)): fired += 1
vb = mk_vdot("bad_b")
if any(mul_v(chT(l)) != chsum(vb(l)) for l in range(40)): fired += 1
if any(m(1, n) != 2 ** ((n + 1) // 2) for n in range(1, 30, 2)): fired += 1
print("controls fired", fired, "of 3")
