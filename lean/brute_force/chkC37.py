#!/usr/bin/env python3
"""Brute force for piece C37 (§9.3: Lemmas 9.8-9.9, Theorem 9.10, Corollary 1.7 = Gao et al. Conj. 5.4).
Grepy Escribano, 8 Oct 2026. Family machinery copied verbatim from chkC36.py (from §1.2).
  A. Lemma 9.8: L(N'+1) = L(N') + 1 for odd N' <= 129 (as lists in flatMap order); ds(lam+1) = same k, I u {0};
     dancers of I u {0} at 2q, 2q+1 are D_q, D_q u {0}; smallExps(lam+1) = 2 smallExps(lam); h' rule.
  B. Lemma 9.9: both closed forms, every family k <= 8, every i, D, e <= 10.
  C. Theorem 9.10: clocks of D and D u {0} in lam+1 equal the clock of D in lam, e <= 10, every odd lam < 2^e-1.
  F. doubled fit: pava_int(x doubled) = pava_int(x) doubled, 3000 random sequences.
  X. Corollary 1.7 multisets: exps(2^e) = 2 exps(2^e-1) + {2^e+e-1}, e <= 8; famExps(lam+1,i) = 2 famExps(lam,i);
     top family; and against the Smith form of the Laplacian for n = 2, 4, 8.
Controls (each must fire): (X) without the extra factor; extra factor 2^e+e; (C) D u {0} at shift i+1;
(A) for even N'; (F) concatenation instead of doubling; (B1) without v2(J)."""
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
import random
random.seed(37)
def lst(n):
    L = [0]
    for _ in range(n): L = [mu for lam in L for mu in tdot(lam)]
    return L
def hfun(I, k, t):
    return min([u for u in I + [k] if u > t]) - t
def smallE(lam):
    k, I = family(lam); c = Counter()
    for a in range(1, k): c[a] += 2 ** (len(I) + k - 1 - a)
    return c
ctrl = Counter()
# A (multiplicities by counters; the list identity follows from: every family of an odd N' is odd)
for Np in range(1, 130, 2):
    a = mult(Np); b = mult(Np + 1)
    ok(all(l % 2 == 1 for l in a), ("A1 odd", Np))
    ok(b == {l + 1: c for l, c in a.items()}, ("A1", Np))
for Np in range(2, 40, 2):
    if mult(Np + 1) != {l + 1: c for l, c in mult(Np).items()}: ctrl["A-even"] += 1
for lam in range(1, 600, 2):
    k, I = family(lam); k2, I2 = family(lam + 1)
    ok(k2 == k and I2 == [0] + I and 0 not in I, ("A2", lam))
    D1 = dancers(I); D2 = dancers(I2)
    for q in range(len(D1)):
        ok(D2[2 * q] == D1[q] and D2[2 * q + 1] == [0] + D1[q], ("A3", lam, q))
    s1 = smallE(lam); s2_ = smallE(lam + 1)
    ok(s2_ == s1 + s1, ("A4", lam))
    t1 = min(I + [k])
    for t in I: ok(hfun(I2, k, t) == hfun(I, k, t), ("A5", lam, t))
    ok(hfun(I2, k, 0) == t1, ("A5zero", lam))
# B, C
for e in range(1, 11):
    for k in range(0, min(e, 9) + 1):
        for oI in range(0, 2 ** k):
            if k > 0 and oI >= 2 ** k: continue
            I = [t for t in range(k) if (oI >> t) & 1]
            for target, kind in ((2 ** e, "N"), (2 ** e + 1, "n")):
                rest = target - 2 ** k - oI
                if rest < 0 or rest % 2: continue
                i = rest // 2
                lam = 2 ** k + oI - 1
                if lam < 0: continue
                for D in dancers(I):
                    o = sum(2 ** t for t in D); J = i + o
                    if J < 1: continue
                    u = raw(lam, i, D, I, k)
                    h = sum(hfun(I, k, t) for t in D)
                    if kind == "N":
                        ok(u == 2 ** e - 2 * J + v2(J) + s2(J) + h, ("B1", e, k, I, i, D))
                        if u != 2 ** e - 2 * J + s2(J) + h: ctrl["B1-no-v2"] += 1
                    else:
                        ok(u == 2 ** e + 1 - 2 * J + s2(J - 1) + h, ("B2", e, k, I, i, D))
    N = 2 ** e - 1
    for lam in range(1, N, 2):
        i = (N - lam) // 2
        k, I = family(lam); k2, I2 = family(lam + 1)
        for D in dancers(I):
            u = raw(lam, i, D, I, k)
            ok(raw(lam + 1, i, D, I2, k2) == u, ("C-D", e, lam, D))
            ok(raw(lam + 1, i, [0] + D, I2, k2) == u, ("C-D0", e, lam, D))
            if raw(lam + 1, i + 1, [0] + D, I2, k2) != u: ctrl["C-shift"] += 1
# F
for _ in range(3000):
    n = random.randint(1, 12)
    x = [random.randint(-20, 40) for _ in range(n)]
    f = pava_int(x)
    ok(pava_int([x[j // 2] for j in range(2 * n)]) == [f[j // 2] for j in range(2 * n)], ("F", x))
    if pava_int(x + x) != [f[j // 2] for j in range(2 * n)]: ctrl["F-concat"] += 1
# X
for e in range(1, 9):
    N = 2 ** e - 1; n = 2 ** e
    a = exps(N); b = exps(n)
    c = a + a; c[2 ** e + e - 1] += 1
    ok(b == c, ("X4", e))
    if b != a + a: ctrl["X-noextra"] += 1
    c2 = a + a; c2[2 ** e + e] += 1
    if b != c2: ctrl["X-extra+1"] += 1
    for lam in range(1, N, 2):
        i = (N - lam) // 2
        ok(fam_exps(lam + 1, i) == fam_exps(lam, i) + fam_exps(lam, i), ("X3", e, lam))
        ok(Counter(big(lam + 1, i)) == Counter(big(lam, i)) + Counter(big(lam, i)), ("X2", e, lam))
        ok(list(big(lam + 1, i)) == [big(lam, i)[j // 2] for j in range(2 * len(big(lam, i)))], ("X1", e, lam))
    top = fam_exps(N, 0) + fam_exps(N, 0); top[2 ** e + e - 1] += 1
    ok(fam_exps(n, 0) == top, ("X5", e))
for n in (2, 4, 8):
    S = Counter(e for e in smith2(lap(n)) if e is not None and e > 0)
    ok(S == exps(n), ("X smith", n))
    N = n - 1; SN = Counter(e for e in smith2(lap(N)) if e is not None and e > 0) if N >= 1 else Counter()
    e = n.bit_length() - 1
    c = SN + SN; c[2 ** e + e - 1] += 1
    ok(S == c, ("X smith cor", n))
print("checks", checks, "fails", fails)
print("controls", dict(ctrl))
print("FIN")
