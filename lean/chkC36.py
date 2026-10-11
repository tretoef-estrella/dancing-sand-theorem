#!/usr/bin/env python3
"""Brute force for piece C36 (§9.2 Lemma 9.7 and Corollary 1.6, the podium). Grepy Escribano, 8 Oct 2026.
The family machinery (clocks of §1.2, PAVA with rounding, multiplicities, 2-adic Smith form) is copied
verbatim from chkC34.py (written from §1.2 only); multiplicities by counters (no lists).
New here:
  layer_j(G) = 2^{#factors with exponent > j}; cExp(G, r) = sup{e >= 1 : 2^r <= layer_{e-1}(G)} (0 if none);
  exps(n) = the exponents of Syl_2 K(Q_n) read off the families (small clocks a in [1,k) with multiplicity
            2^{|I|+k-1-a}; big clocks yPool (i >= 1) or yPool0 (i = 0, the extra Z_2 dropped)).
  1. (E) exps(n) against the Smith form of the Laplacian of Q_n, 1 <= n <= 9; cExp from layers equals
     the r-th largest exponent, every r <= #exps + 2;
  2. (L) Lemma 9.7, 1 <= n <= 300;
  3. (W) clock at shift 2 = clock at shift 1 when 0 notin I, every k <= 8, I ⊆ [1,k), D ⊆ I;
  4. (B) the per-family bounds of the proof of Corollary 1.6, 4 <= n <= 160;
  5. (P) Corollary 1.6 (three cases) and (G1)-(G3) (Gao et al. Thms 4.1-4.2, Conj. 4.14, poster), 3 <= n <= 160.
Controls (each must fire): c_n = G always; Lemma 9.7 without [n even]; (W) for 0 in I; layer with <= for <;
c_1 = phi(n) for even n."""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
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
def phi(x): return x + v2(x)

def family(lam):
    x = lam + 1; k = x.bit_length() - 1
    I = [t for t in range(k) if (x >> t) & 1]
    return k, I
def dancers(I):
    out = []
    for p in range(2 ** len(I)):
        out.append([I[j] for j in range(len(I)) if (p >> j) & 1])
    return out
def raw(lam, i, D, I, k):
    nxt = lambda t: min([u for u in I + [k] if u > t])
    o = sum(2 ** t for t in D); xi = lam + 1 - 2 * o
    h = sum(nxt(t) - t for t in D)
    return xi + v2(xi) + kap(i + o - 1, xi) + h
def pava_int(xs):
    blocks = []
    for x in xs:
        blocks.append([x, 1])
        while len(blocks) > 1 and Fraction(blocks[-2][0], blocks[-2][1]) <= Fraction(blocks[-1][0], blocks[-1][1]):
            s, c = blocks.pop(); blocks[-1][0] += s; blocks[-1][1] += c
    out = []
    for s, p in blocks:
        q, r = divmod(s, p)
        out += [q + 1] * r + [q] * (p - r)
    return out

@lru_cache(None)
def big(lam, i):
    k, I = family(lam); Ds = dancers(I)
    if i >= 1: return tuple(pava_int([raw(lam, i, D, I, k) for D in Ds]))
    return tuple(pava_int([raw(lam, 0, D, I, k) for D in Ds[1:]]))
def fam_exps(lam, i):
    k, I = family(lam); c = Counter()
    for a in range(1, k): c[a] += 2 ** (len(I) + k - 1 - a)
    for e in big(lam, i): c[e] += 1
    return c

def tdot(l):
    if l == 0: return [1]
    if l % 2 == 1: return [l + 1]
    return [l - 1, l - 1] + [2 * x + 1 for x in tdot((l - 2) // 2)]
@lru_cache(None)
def mult(n):
    if n == 0: return {0: 1}
    d = Counter()
    for lam, cnt in mult(n - 1).items():
        for mu in tdot(lam): d[mu] += cnt
    return dict(d)
def exps(n):
    s = Counter()
    for lam, c in mult(n).items():
        for e, m in fam_exps(lam, (n - lam) // 2).items(): s[e] += c * m
    return s

def loglayer(s, j, strict=True):
    return sum(m for e, m in s.items() if (j < e if strict else j <= e))
def layer(s, j, strict=True):
    return 2 ** loglayer(s, j, strict)
def cExp(s, r, strict=True):
    top = max(s) + 3 if s else 3
    # 2^r <= layer  <=>  r <= log2 layer (layer is a power of 2)
    cands = [e for e in range(1, top) if r <= loglayer(s, e - 1, strict)]
    return max(cands) if cands else 0
def topk(s, r):
    out = []
    for e in sorted(s, reverse=True):
        out += [e] * min(s[e], r - len(out))
        if len(out) >= r: break
    return out
def g(N): return max(phi(y) for y in range(1, N)) if N > 1 else None

def smith2(M):
    n = len(M); A = [[x % MOD for x in r] for r in M]
    live_r = set(range(n)); live_c = set(range(n)); out = []
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
def lap(n):
    N = 1 << n; M = [[0] * N for _ in range(N)]
    for gg in range(N):
        M[gg][gg] = n
        for t in range(n): M[gg][gg ^ (1 << t)] -= 1
    return M

# 1. (E)
for n in range(1, 10):
    S = Counter(e for e in smith2(lap(n)) if e is not None and e > 0)
    ok(S == exps(n), ("E smith", n))
for n in range(1, 61):
    s = exps(n); tot = sum(s.values())
    if n <= 12:
        for j in range(0, max(s, default=0) + 3):
            ok(layer(s, j) == 2 ** sum(m for e, m in s.items() if e > j), ("E1", n, j))
            ok(2 ** n > 0 and all((2 ** r <= layer(s, j)) == (r <= loglayer(s, j)) for r in range(1, 3 * n)), ("E1log", n, j))
    def rth(r):
        acc = 0
        for e in sorted(s, reverse=True):
            acc += s[e]
            if acc >= r: return e
        return None
    srt_r = {r: rth(r) for r in range(1, min(tot, 3 * n) + 3)}
    cnt = {e: sum(m for x, m in s.items() if e <= x) for e in range(1, max(s, default=0) + 3)}
    for r in range(1, min(tot, 3 * n) + 3):
        cr = cExp(s, r)
        ok(cr == (srt_r[r] if r <= tot else 0), ("E2", n, r))
        for e in cnt:
            ok((e <= cr) == (r <= cnt[e]), ("E2iff", n, r, e))
# 2. (L) Lemma 9.7
for n in range(1, 301):
    md = mult(n)
    ok(md.get(n, 0) == 1, ("L1", n))
    if n >= 2: ok(md.get(n - 2, 0) == n - 1 - (1 if n % 2 == 0 else 0), ("L2", n))
    if n % 2 == 1 and n >= 5:
        v = md.get(n - 4, 0)
        ok(v == (n - 1) * (n - 2) // 2 - 1 - (1 if n % 4 == 1 else 0) and v >= 4, ("L3", n))
# 3. (W)
for k in range(1, 9):
    for mask in range(2 ** k):
        if mask & 1: continue
        I = [t for t in range(k) if (mask >> t) & 1]
        lam = 2 ** k + sum(2 ** t for t in I) - 1
        ok(lam % 2 == 1, ("W odd", lam))
        for D in dancers(I):
            ok(raw(lam, 2, D, I, k) == raw(lam, 1, D, I, k), ("W", lam, D))
        ok(big(lam, 2) == big(lam, 1), ("W pool", lam))
# 4. (B) the per-family bounds, 4 <= n <= 160
for n in range(4, 161):
    G = g(n - 1)
    for lam, c in mult(n).items():
        if c == 0: continue
        i = (n - lam) // 2; k, I = family(lam)
        ok(k - 1 < G, ("B0 small", n, lam))
        b = big(lam, i)
        if i >= 2: ok(max(b) <= G, ("B1", n, lam))
        if i == 1:
            ok(b[0] == max(G, phi(n - 1)), ("B2a", n))
            ok(all(x <= G for x in b[1:]), ("B2b", n))
            if n % 2 == 0: ok(len(b) >= 2 and b[0] == G and b[1] == G, ("B7", n))
        if i == 0:
            t1 = I[0] if I else None
            if I:
                A0 = max([phi(lam + 1 - sum(2 ** t for t in I[:l])) for l in range(2, len(I) + 1)], default=None)
                V0 = max(x for x in [phi(n + 1 - 2 ** t1) - 2 ** t1, A0] if x is not None)
                ok(b[0] == V0, ("B3a", n))
                ok(all(x <= G for x in b[1:]), ("B3b", n))
                if n % 2 == 0: ok(V0 == max(phi(n) - 1, A0) if A0 is not None else V0 == phi(n) - 1, ("B3even", n))
                ok(all(phi(lam + 1 - sum(2 ** t for t in I[:l])) <= G for l in range(2, len(I) + 1)), ("B3 Yl", n))
                ok(lam + 1 - 2 ** t1 == n + 1 - 2 ** t1, ("Y1", n))
                if n % 2 == 0: ok(phi(n) - 1 <= b[0] <= max(G, phi(n) - 1), ("B4", n))
                if n % 4 == 1: ok(phi(n - 1) - 2 <= b[0] <= max(G, phi(n - 1) - 2), ("B5", n))
                if n % 4 == 3: ok(b[0] <= G, ("B6", n))
        if i == 2 and lam == n - 4 and n % 2 == 1:
            ok(b[0] == G, ("B8", n))
# 5. (P) Corollary 1.6 and (G1)-(G3)
for n in range(3, 161):
    s = exps(n); c = lambda r: cExp(s, r)
    if n >= 4:
        G = g(n - 1)
        if n % 2 == 0:
            ok(c(1) == max(G, phi(n) - 1) and all(c(r) == G for r in range(2, n + 2)), ("P1", n))
        elif phi(n - 1) <= G:
            ok(all(c(r) == G for r in range(1, n + 2)), ("P2", n))
        else:
            ok(all(c(r) == phi(n - 1) for r in range(1, n)) and c(n) == max(G, phi(n - 1) - 2) and c(n + 1) == G, ("P3", n))
        ok(c(n + 1) == g(n - 1), ("G3 poster", n))
    ok(c(1) == max(g(n), v2(n) + n - 1), ("G1 Thm 4.1", n))
    ok(all(c(r) == g(n) for r in range(2, n)), ("G1 Thm 4.2", n))
    ok(c(n) == max(g(n - 1), v2(n - 1) + n - 3), ("G2 Conj 4.14", n))
ok(sorted(exps(3).elements()) == [1, 3, 3], "n=3 by hand")
print("checks", checks, "fails", fails)

fired = 0
if any(cExp(exps(n), n) != g(n - 1) for n in range(4, 80)): fired += 1
else: print("SILENT c_n = G")
if any(mult(n).get(n - 2, 0) != n - 1 for n in range(2, 60)): fired += 1
else: print("SILENT L2 without [n even]")
if any(raw(2 ** k + sum(2 ** t for t in I) - 1, 2, D, I, k) != raw(2 ** k + sum(2 ** t for t in I) - 1, 1, D, I, k)
       for k in range(1, 6) for mask in range(2 ** k) if mask & 1 for I in [[t for t in range(k) if (mask >> t) & 1]] for D in dancers(I)): fired += 1
else: print("SILENT W with 0 in I")
if any(cExp(exps(n), r, strict=False) != cExp(exps(n), r) for n in range(3, 20) for r in range(1, n + 2)): fired += 1
else: print("SILENT layer <=")
if any(cExp(exps(n), 1) != phi(n) for n in range(4, 80, 2)): fired += 1
else: print("SILENT c1 = phi(n)")
print("controls fired", fired, "of 5")
