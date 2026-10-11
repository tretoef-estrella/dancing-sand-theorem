#!/usr/bin/env python3
"""Brute force for Lean piece C5 (determinantal divisors and Theorem 6.5), Grepy Escribano, 6 Oct 2026.
 A1  the 2-adic determinantal divisor dd_r(M) = min v_2 of non-zero r x r minors is unchanged by
     M -> P M Q with det P, det Q odd (n <= 4).
 A2  for a diagonal matrix diag(u_i 2^{e_i}), u_i odd, e non-decreasing: dd_r = e_0 + ... + e_{r-1}.
 A3  for every non-singular integer M (n <= 4): dd_r(M) = sum of the r smallest 2-adic exponents
     of the Smith form of M (sympy), so the exponents are the increments of dd.
 B   Theorem 6.5, abstract: e non-decreasing, dh(r) = sum_{i<r} e_i - r C, Y <= dh <= U,
     ifit non-increasing  =>  dh = Y and e_i = C + yhat_{N-1-i}.
Controls must fail somewhere.
"""
import itertools, random
from fractions import Fraction as Q
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form

def v2(n):
    n = abs(n); v = 0
    while n % 2 == 0: n //= 2; v += 1
    return v

def det(M):
    n = len(M)
    if n == 0: return 1
    A = [[Q(x) for x in row] for row in M]; d = Q(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None: return 0
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for j in range(c, n): A[r][j] -= f * A[c][j]
    return int(d)

def dd(M, r):
    n = len(M); best = None
    for A in itertools.combinations(range(n), r):
        for B in itertools.combinations(range(n), r):
            d = det([[M[a][b] for b in B] for a in A])
            if d != 0:
                v = v2(d); best = v if best is None else min(best, v)
    return best

def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]

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
        S = sum(x[p:q + 1]); P = q - p + 1; r = S % P
        for t in range(P): out[p + t] = -((-S) // P) if t < r else S // P
    return out

fails = 0; ctrl = {}; cnt = {}
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails <= 20: print('FAIL', m)
def control(name, broke): ctrl[name] = ctrl.get(name, 0) + (1 if broke else 0)
def tick(n): cnt[n] = cnt.get(n, 0) + 1

rnd = random.Random(5)
def rand_mat(n, lo=-8, hi=8):
    while True:
        M = [[rnd.randint(lo, hi) for _ in range(n)] for _ in range(n)]
        if det(M) != 0: return M
def rand_odd(n):
    while True:
        P = [[rnd.randint(-3, 3) for _ in range(n)] for _ in range(n)]
        if det(P) % 2 != 0: return P
def rand_even(n):
    while True:
        P = [[rnd.randint(-3, 3) for _ in range(n)] for _ in range(n)]
        d = det(P)
        if d != 0 and d % 2 == 0: return P

# A1, A3
for n in range(1, 5):
    for _ in range(150 if n < 4 else 60):
        M = rand_mat(n); P, Qm = rand_odd(n), rand_odd(n)
        PMQ = mul(mul(P, M), Qm)
        for r in range(0, n + 1):
            a, b = (dd(M, r), dd(PMQ, r)) if r > 0 else (0, 0)
            check(a == b, f'A1 n={n} r={r}'); tick('A1')
        Pe = rand_even(n); PeM = mul(Pe, M)
        control('A1 with det P even', any(dd(M, r) != dd(PeM, r) for r in range(1, n + 1)))
        snf = smith_normal_form(Matrix(M), domain=ZZ)
        ex = sorted(v2(int(snf[i, i])) for i in range(n))
        for r in range(1, n + 1):
            check(dd(M, r) == sum(ex[:r]), f'A3 n={n} r={r}'); tick('A3')

# A2
for n in range(1, 6):
    for _ in range(200):
        e = sorted(rnd.randint(0, 5) for _ in range(n)); u = [rnd.choice([1, -1, 3, 5, -7]) for _ in range(n)]
        D = [[u[i] * 2**e[i] if i == j else 0 for j in range(n)] for i in range(n)]
        for r in range(1, n + 1):
            check(dd(D, r) == sum(e[:r]), f'A2 n={n} r={r}'); tick('A2')
        eu = [rnd.randint(0, 5) for _ in range(n)]   # control: not sorted
        Du = [[2**eu[i] if i == j else 0 for j in range(n)] for i in range(n)]
        control('A2 without sorting', any(dd(Du, r) != sum(eu[:r]) for r in range(1, n + 1)))

# B
def Ysum(yh, r): N = len(yh); return sum(yh[N - r:])
def Usum(x, r): N = len(x); return sum(x[N - r:])
for N in range(1, 6):
    for _ in range(250 if N < 5 else 40):
        x = [rnd.randint(-3, 4) for _ in range(N)]; yh = ifit(x)
        noninc = all(yh[i] >= yh[i + 1] for i in range(N - 1))
        C = rnd.choice([-1, 0, 2])
        lo = min(yh) + C - 1; hi = max(yh) + C + 1
        for e in itertools.product(range(lo, hi + 1), repeat=N):
            mono = all(e[i] <= e[i + 1] for i in range(N - 1))
            dh = [sum(e[:r]) - r * C for r in range(N + 1)]
            hyp = all(Ysum(yh, r) <= dh[r] <= Usum(x, r) for r in range(N + 1))
            if not hyp: continue
            concl = all(dh[r] == Ysum(yh, r) for r in range(N + 1)) and \
                    all(e[i] == C + yh[N - 1 - i] for i in range(N))
            if mono and noninc:
                check(concl, f'B N={N} x={x} e={e}'); tick('B')
            elif noninc:
                control('B without e non-decreasing', not concl)
            elif mono:
                # (M) is redundant: with e non-decreasing the hypotheses force yhat non-increasing
                check(False, f'B hypotheses hold with yhat not non-increasing N={N} x={x} e={e}'); tick('B-M-redundant')

print('COUNTS', cnt)
print('TOTAL FAILURES', fails)
print('CONTROLS', ctrl, 'ALL FIRE' if ctrl and all(v > 0 for v in ctrl.values()) else 'SOME CONTROL SILENT')
