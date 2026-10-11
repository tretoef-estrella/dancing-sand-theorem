#!/usr/bin/env python3
"""Brute force for Lean piece C8 (Theorem F, steps 4-8: the potential V with (E), (M), (G)), Grepy Escribano, 6 Oct 2026.
Exhaustive for k <= KMAX, every I subset of [0,k), every l < 2^k, alpha in {1,2,3}; the price c_F at the low and at the
high end of its interval (the inner levels use the same choice). Controls must fail somewhere."""
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

for k in range(0, KMAX + 1):
    for rI in range(k + 1):
        for I in itertools.combinations(range(k), rI):
            N = 2 ** len(I); Ds = [dancer(I, p) for p in range(N)]; AR = arrows(I, N)
            for l in range(2 ** k):
                for a in (1, 2, 3):
                    x = [xH(k, I, a, l, D) for D in Ds]; y = ifit(x)
                    C = {(p, q): chat(k, I, a, l, Ds[p], Ds[q]) for (p, q) in AR}
                    for mode in ('low', 'high'):
                        V, info = build(k, I, l, a, mode, checks=True)
                        if info is not None:
                            vp, X1, h, M = info['vp'], info['X1'], info['h'], info['M']
                            # step 4 (P1): (G) for v' with slack h on same-half arrows, plain when c in a \ b
                            for (p, q) in AR:
                                if (p < M) == (q < M):
                                    check(C[(p, q)] >= vp[p] - vp[q] + h, f'P1 slack k={k} I={I} l={l} a={a}'); tick('P1-slack')
                                    control('P1 slack h+1', C[(p, q)] < vp[p] - vp[q] + h + 1)
                                else:
                                    check(p >= M and q < M, 'cross arrow direction'); tick('P1-dir')
                                    check(C[(p, q)] >= vp[p] - vp[q], 'P1 cross'); tick('P1-cross')
                            X2 = [-X1[M - 1 - p] for p in range(M)]
                            check(all(vp[p] - vp[N - 1 - p] == X1[p] for p in range(M)), 'P2 E first half'); tick('P2')
                            check(all(vp[M + p] - vp[M - 1 - p] == X2[p] for p in range(M)), 'P2 E second half'); tick('P2')
                            check(all(vp[p] >= vp[p + 1] for p in range(M - 1)) and all(vp[M + p] >= vp[M + p + 1] for p in range(M - 1)), 'P3 M halves'); tick('P3')
                            check(vp[M] - vp[M - 1] == -X1[M - 1], 'junction identity'); tick('P5')
                            check(-X1[M - 1] <= h - a, f'junction bound k={k} I={I} l={l} a={a}'); tick('P5')
                            control('junction h-a-1', -X1[M - 1] > h - a - 1)
                            check(all(X1[p] >= X1[p + 1] for p in range(M - 1)), 'X1 noninc'); tick('X1-noninc')
                            if info['flat'] is not None:
                                f, c3, c4, lo, hi = info['flat']
                                Fpos = set(range(f, N - f))
                                check(c3 == max(vp[p] for p in range(f, M)), 'c3 max'); tick('P7')
                                check(c4 == min(vp[p] for p in range(M, N - f)), 'c4 min'); tick('P7')
                                check(c3 - c4 == X1[f] and X1[f] <= 0, 'c3-c4'); tick('P7')
                                check(lo <= hi, f'interval nonempty k={k} I={I} l={l} a={a}'); tick('P7-interval')
                                check(all((y[p] == 0) == (p in Fpos) for p in range(N)), 'yhat zero exactly on F'); tick('P7-F')
                                lo_bad = [lo - 1 if p in Fpos else vp[p] for p in range(N)]
                                hi_bad = [hi + 1 if p in Fpos else vp[p] for p in range(N)]
                                for nm, W in (('c_F = low-1', lo_bad), ('c_F = high+1', hi_bad)):
                                    okM = all(W[p] >= W[p + 1] for p in range(N - 1))
                                    okG = all(W[p] - W[q] <= C[(p, q)] for (p, q) in AR)
                                    control(nm, not (okM and okG))
                            else:
                                check(X1[M - 1] > 0 and all(y[p] != 0 for p in range(N)), 'no flat: yhat never 0'); tick('P6')
                        # Theorem F (Theorem 7.8): (E), (M), (G)
                        check(all(V[p] - V[N - 1 - p] == y[p] for p in range(N)), f'E k={k} I={I} l={l} a={a} {mode}'); tick('E')
                        check(all(V[p] >= V[p + 1] for p in range(N - 1)), f'M k={k} I={I} l={l} a={a} {mode}'); tick('M')
                        check(all(V[p] - V[q] <= C[(p, q)] for (p, q) in AR), f'G k={k} I={I} l={l} a={a} {mode}'); tick('G')
                        if AR: control('G without gold', any(V[p] - V[q] > C[(p, q)] - gamma(k, I, set(Ds[p]) - set(Ds[q])) for (p, q) in AR))

print('KMAX', KMAX); print('COUNTS', cnt); print('TOTAL FAILURES', fails)
print('CONTROLS', ctrl, 'ALL FIRE' if ctrl and all(v > 0 for v in ctrl.values()) else 'SOME CONTROL SILENT')
