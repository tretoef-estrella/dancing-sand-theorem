#!/usr/bin/env python3
"""Brute force for Lean piece C9 (§7.5: Lemma 7.9 integrality; Theorem 7.10, the floor of every cell, house form),
Grepy Escribano, 6 Oct 2026. Exhaustive for k <= KMAX, every I subset of [0,k), every l < 2^k, alpha in {1,2,3},
penalties P_r, P_c <= PMAX; V built as in C8 (low end of the c_F interval). Controls must fail somewhere."""
from fractions import Fraction as Q
import itertools, sys
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
PMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3

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


def gamma(k, I, D):
    D = set(D)
    if not D: return 0
    m = min(D)
    return sum(hh(k, I, u) for u in I if u not in D and u > m)
def chat(k, I, a, l, A, B):
    return ruler(k, I, a, l, A) - ruler(k, I, a, l, B) + gamma(k, I, set(A) - set(B))

fails = 0; cnt = {}; ctrl = {}
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails <= 20: print('FAIL', m)
def tick(n): cnt[n] = cnt.get(n, 0) + 1
def control(n, broke): ctrl[n] = ctrl.get(n, 0) + (1 if broke else 0)

def arrows(I, N):
    Ds = [set(dancer(I, p)) for p in range(N)]
    return [(p, q) for p in range(N) for q in range(N) if Ds[q] < Ds[p]]

memo = {}
def build(k, I, l, a, mode, checks=False):
    """V on positions, by steps 4-7 of Theorem 7.8; mode in {'low','high'} picks the end of the c_F interval."""
    key = (k, I, l, a, mode)
    if key in memo and not checks: return memo[key]
    N = 2 ** len(I)
    if not I:
        memo[key] = [0]; return ([0], None) if checks else [0]
    c = max(I); Ip = tuple(t for t in I if t != c); M = N // 2; lp = l % 2**c; h = k - c
    Vp = build(c, Ip, lp, a, mode)
    xp = [xH(c, Ip, a, lp, dancer(Ip, p)) for p in range(M)]
    yp = ifit(xp)
    Jp = [J(c, lp, dancer(Ip, p)) for p in range(M)]
    T = bit(l, c); kp = kap(k, I, l, c); tc = tau(k, I, l, a, c)
    d1 = [-tc - (kp if T == 1 else 0) * Jp[p] + (kp if T == 0 else 0) * Jp[M - 1 - p] for p in range(M)]
    X1 = [yp[p] + d1[p] for p in range(M)]
    vp = [Vp[p] - (kp if T == 1 else 0) * Jp[p] for p in range(M)] + [tc + Vp[p] - (kp if T == 0 else 0) * Jp[p] for p in range(M)]
    info = dict(vp=vp, X1=X1, h=h, M=M, c=c, flat=None)
    if X1[M - 1] > 0:
        V = list(vp)
    else:
        f = min(p for p in range(M) if X1[p] <= 0)
        c3 = vp[f]; c4 = vp[N - 1 - f]
        lo = max([c3] + ([vp[N - f]] if f > 0 else [])); hi = min([c4] + ([vp[f - 1]] if f > 0 else []))
        cF = lo if mode == 'low' else hi
        V = [cF if f <= p <= N - 1 - f else vp[p] for p in range(N)]
        info['flat'] = (f, c3, c4, lo, hi)
    memo[key] = V
    return (V, info) if checks else V


def min_matching_cost(Rows_all, Cols_all, r, arr, cost):
    """minimum over r-matchings Rows ⊆ Rows_all, injective beta into Cols_all with arr; None if none. Small cases only."""
    best = None
    for Rows in itertools.combinations(Rows_all, r):
        for cols in itertools.permutations(Cols_all, r):
            if all(arr(a, b) for a, b in zip(Rows, cols)):
                s = sum(cost(a, b) for a, b in zip(Rows, cols))
                best = s if best is None or s < best else best
    return best

for k in range(0, KMAX + 1):
    for rI in range(k + 1):
        for I in itertools.combinations(range(k), rI):
            N = 2 ** len(I); Ds = [dancer(I, p) for p in range(N)]; S = [set(D) for D in Ds]
            for l in range(2 ** k):
                for a in (1, 2, 3):
                    x = [xH(k, I, a, l, D) for D in Ds]; z = pava(x); y = ifit(x)
                    Js = [J(k, l, D) for D in Ds]
                    # Lemma 7.9 (I1): the fit of x_H is integral and equals the integer fit; non-increasing
                    check(all(zz.denominator == 1 for zz in z) and all(z[p] == y[p] for p in range(N)), f'I1 k={k} I={I} l={l} a={a}'); tick('I1')
                    check(all(y[p] >= y[p + 1] for p in range(N - 1)), 'I1 noninc'); tick('I1-noninc')
                    if N >= 2:
                        xb = list(x); xb[0] += 1
                        control('I1: x_H with +1 at the first dancer', any(v.denominator != 1 for v in pava(xb)))
                    V = build(k, I, l, a, 'low')
                    for Pr in range(PMAX + 1):
                        for Pc in range(PMAX + 1):
                            sh = [-Pr * Js[p] + Pc * Js[N - 1 - p] for p in range(N)]
                            zc = [x[p] + sh[p] for p in range(N)]
                            fc = pava(zc); yc = ifit(zc)
                            # (I2): cell fit integral, = integer fit, and = yhat_H + shift
                            check(all(v.denominator == 1 for v in fc) and all(fc[p] == yc[p] for p in range(N)), f'I2 integral k={k} I={I} l={l} a={a} Pr={Pr} Pc={Pc}'); tick('I2')
                            check(all(yc[p] == y[p] + sh[p] for p in range(N)), f'I2 shift k={k} I={I} l={l} a={a} Pr={Pr} Pc={Pc}'); tick('I2-shift')
                            if 1 in Js and (Pr or Pc):
                                b = Js.index(1)
                                if b + 1 < N:
                                    late = [0 if p <= b else 1 for p in range(N)]
                                    sh2 = [-Pr * late[p] + Pc * late[N - 1 - p] for p in range(N)]
                                    control('I2: shift moved one dancer late', ifit([x[p] + sh2[p] for p in range(N)]) != [y[p] + sh2[p] for p in range(N)])
                            # Theorem 7.10 floor (house form): v = V - Pr J, w = V - Pc J satisfy U1-U3
                            v = [V[p] - Pr * Js[p] for p in range(N)]; w = [V[p] - Pc * Js[p] for p in range(N)]
                            check(all(v[p] >= v[p + 1] and w[p] >= w[p + 1] for p in range(N - 1)), 'U1'); tick('U1')
                            check(all(v[p] - w[N - 1 - p] == yc[p] for p in range(N)), f'U2 k={k} I={I} l={l} a={a} Pr={Pr} Pc={Pc}'); tick('U2')
                            def cost(p, q): return chat(k, I, a, l, Ds[p], Ds[q]) - Pr * Js[p] + Pc * Js[q]
                            ok3 = all(v[p] - w[q] <= cost(p, q) for p in range(N) for q in range(N) if S[q] <= S[p])
                            check(ok3, f'U3 k={k} I={I} l={l} a={a} Pr={Pr} Pc={Pc}'); tick('U3')
                            check(all(v[p] - w[p] == cost(p, p) for p in range(N)), 'U3 loops equality'); tick('U3-loop')
                            if Pr != Pc and 1 in Js:
                                control('U3 with w := V (no column penalty)', any(v[p] - V[q] > cost(p, q) for p in range(N) for q in range(N) if S[q] <= S[p]) or any(v[p] - V[N - 1 - p] != yc[p] for p in range(N)))
                            if N <= 4 and Pr <= 1 and Pc <= 1:
                                for r in range(N + 1):
                                    m = min_matching_cost(list(range(N)), list(range(N)), r, lambda p, q: S[q] <= S[p], cost)
                                    if m is not None:
                                        check(m >= sum(yc[N - r:]), 'matching cost >= Y(r)'); tick('U-conclusion')
                    # Part C: the house l = 2^k - 1 (shift 0), I nonempty
                    if l == 2 ** k - 1 and I:
                        check(all(Js[p] == (1 if p != 0 else 0) for p in range(N)), 'C J = [p != 0]'); tick('C-J')
                        check(is_strict(x, 1), 'C strict cut at 1'); tick('C-cut')
                        xs = x[1:]; check(pava(xs) == z[1:] and ifit(xs) == y[1:], 'C deletion = restriction'); tick('C-del')
                        Np = N - 1
                        check(all(V[j + 1] - V[Np - 1 - j] == ifit(xs)[j] for j in range(Np)), 'C U2'); tick('C-U2')
                        check(all(V[j + 1] - V[b] <= chat(k, I, a, l, Ds[j + 1], Ds[b]) for j in range(Np) for b in range(Np) if S[b] <= S[j + 1]), 'C U3'); tick('C-U3')
                        control('C with l = 2^k - 2', k >= 1 and any(J(k, 2 ** k - 2, Ds[p]) != (1 if p else 0) for p in range(N)))

print('KMAX', KMAX, 'PMAX', PMAX); print('COUNTS', cnt); print('TOTAL FAILURES', fails)
print('CONTROLS', ctrl, 'ALL FIRE' if ctrl and all(v > 0 for v in ctrl.values()) else 'SOME CONTROL SILENT')
