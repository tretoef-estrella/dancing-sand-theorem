#!/usr/bin/env python3
"""Brute force for Lean piece C7 (Theorem F, steps 1-3: the walk, (Lambda), strict (Cut)), Grepy Escribano, 6 Oct 2026.
Exhaustive for k <= KMAX, every I subset of [0,k), every l < 2^k, alpha in {1,2,3}. Exact fractions. Controls must fail."""
from fractions import Fraction as Q
import itertools, sys
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5

def s2(x): return bin(x).count('1')
def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)
def oE(E): return sum(2**t for t in E)
def nxt(k, I, t): return min([u for u in list(I) + [k] if u > t])
def hh(k, I, t): return nxt(k, I, t) - t
def bit(x, u): return (x >> u) & 1
def r_(u, x): return v2((x >> u) + 1)
def ruler(k, I, a, mu, E): return sum(hh(k, I, t) - a * 2**t for t in E) - kappa(mu, oE(E))
def J(k, l, E): return 1 if l + oE(E) >= 2**k else 0
def dancer(I, p):
    S = sorted(I); return tuple(S[j] for j in range(len(S)) if bit(p, j))
def xH(k, I, a, l, D):
    Dc = tuple(t for t in I if t not in D)
    return ruler(k, I, a, l, D) - ruler(k, I, a, l, Dc)
def kap(k, I, l, t):
    h = hh(k, I, t)
    return min(r_(t, l), h) if bit(l, t) else 1 + min(r_(t + 1, l), h - 1)
def tau(k, I, l, a, t):
    return hh(k, I, t) - a * 2**t - (kap(k, I, l, t) if bit(l, t) else 0)

def pava(x):
    blocks = []
    for v in x:
        blocks.append([Q(v), 1])
        while len(blocks) >= 2 and blocks[-2][0] / blocks[-2][1] < blocks[-1][0] / blocks[-1][1]:
            s, c = blocks.pop(); blocks[-1][0] += s; blocks[-1][1] += c
    z = []
    for s, c in blocks: z += [s / c] * c
    return z
def level_sets(z):
    out, i = [], 0
    while i < len(z):
        j = i
        while j + 1 < len(z) and z[j + 1] == z[i]: j += 1
        out.append((i, j)); i = j + 1
    return out
def ifit(x):
    z = pava(x); out = [None] * len(x)
    for (p, q) in level_sets(z):
        S = sum(x[p:q + 1]); P = q - p + 1; rr = S % P
        for j in range(p, q + 1): out[j] = (S // P + (1 if j - p < rr else 0))
    return out
def is_cut(x, b):
    N = len(x); return 0 < b < N and pava(x) == pava(x[:b]) + pava(x[b:])
def is_strict(x, b):
    z = pava(x); return is_cut(x, b) and z[b] < z[b - 1]

fails = 0; cnt = {}; ctrl = {}
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails <= 20: print('FAIL', m)
def tick(n): cnt[n] = cnt.get(n, 0) + 1
def control(n, broke): ctrl[n] = ctrl.get(n, 0) + (1 if broke else 0)

for k in range(0, KMAX + 1):
    for rI in range(k + 1):
        for I in itertools.combinations(range(k), rI):
            N = 2 ** len(I)
            Ds = [dancer(I, p) for p in range(N)]
            # dancer bookkeeping
            check(len(set(Ds)) == N, 'dancer bijective'); tick('dancer-bij')
            check(all(oE(Ds[p]) < oE(Ds[p + 1]) for p in range(N - 1)), 'dancer o-order'); tick('dancer-order')
            check(all(set(Ds[N - 1 - p]) == set(I) - set(Ds[p]) for p in range(N)), 'dancer mirror'); tick('dancer-mirror')
            if I:
                c = max(I); Ip = tuple(t for t in I if t != c); M = N // 2
                check(all(Ds[p] == dancer(Ip, p) for p in range(M)) and all(set(Ds[M + p]) == set(dancer(Ip, p)) | {c} for p in range(M)), 'dancer halves'); tick('dancer-halves')
            for l in range(2 ** k):
                for a in (1, 2, 3):
                    x = [xH(k, I, a, l, D) for D in Ds]
                    y = ifit(x); z = pava(x)
                    check(all(x[N - 1 - p] == -x[p] for p in range(N)), 'antisym'); tick('antisym')
                    # (Lambda)
                    check(all(abs(v) <= a * (2**k - 1) for v in y), f'Lambda k={k} I={I} l={l} a={a}'); tick('Lambda')
                    control('Lambda with 2^k-2', any(abs(v) > a * (2**k - 2) for v in y) if k >= 1 else True)
                    # (Cut)
                    Js = [J(k, l, D) for D in Ds]
                    check(Js[0] == 0, 'J(empty)=0'); tick('J0')
                    if 1 in Js:
                        b = Js.index(1)
                        check(is_strict(x, b), f'Cut strict b k={k} I={I} l={l} a={a} b={b}'); tick('Cut')
                        check(is_strict(x, N - b), f'Cut strict mirror k={k} I={I} l={l} a={a}'); tick('Cut-mirror')
                        if b + 1 < N: control('Cut at b+1', not is_strict(x, b + 1))
                    # Step 1 (the walk) for I nonempty
                    if I:
                        c = max(I); Ip = tuple(t for t in I if t != c); M = N // 2; lp = l % 2**c
                        xp = [xH(c, Ip, a, lp, dancer(Ip, p)) for p in range(M)]
                        yp = ifit(xp); zp = pava(xp)
                        Jp = [J(c, lp, dancer(Ip, p)) for p in range(M)]
                        T = bit(l, c); kp = kap(k, I, l, c); tc = tau(k, I, l, a, c)
                        d1 = [-tc - (kp if T == 1 else 0) * Jp[p] + (kp if T == 0 else 0) * Jp[M - 1 - p] for p in range(M)]
                        check(all(d1[p] >= d1[p + 1] for p in range(M - 1)), 'd1 noninc'); tick('d1-noninc')
                        ch = [p for p in range(1, M) if d1[p - 1] != d1[p]]
                        allowed = set()
                        if 1 in Jp: bb = Jp.index(1); allowed |= {bb, M - bb}
                        check(set(ch) <= allowed, f'd1 changes k={k} I={I} l={l}'); tick('d1-changes')
                        X1 = [yp[p] + d1[p] for p in range(M)]
                        Z1 = [zp[p] + d1[p] for p in range(M)]
                        check(pava([xp[p] + d1[p] for p in range(M)]) == Z1, 'W real first half fit'); tick('W-Z1')
                        check(ifit([xp[p] + d1[p] for p in range(M)]) == X1, 'W integer first half fit'); tick('W-X1')
                        want_z = [max(Z1[p], 0) for p in range(M)] + [min(-Z1[M - 1 - p], 0) for p in range(M)]
                        want_y = [max(X1[p], 0) for p in range(M)] + [min(-X1[M - 1 - p], 0) for p in range(M)]
                        check(z == want_z, f'W real k={k} I={I} l={l} a={a}'); tick('W-real')
                        check(y == want_y, f'W integer k={k} I={I} l={l} a={a}'); tick('W-int')
                        control('W without max', y != X1 + [-X1[M - 1 - p] for p in range(M)])
                        check(all(x[p] == xp[p] + d1[p] for p in range(M)), 'first half clocks = x_H\' + d1'); tick('C6-reuse')

print('KMAX', KMAX); print('COUNTS', cnt); print('TOTAL FAILURES', fails)
print('CONTROLS', ctrl, 'ALL FIRE' if ctrl and all(v > 0 for v in ctrl.values()) else 'SOME CONTROL SILENT')
