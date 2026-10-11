#!/usr/bin/env python3
"""Brute force for Lean piece C4 (Theorem O and Corollary 6.3), Grepy Escribano, 6 Oct 2026.
Checks, with controls that must fail somewhere:
 A  Theorem O, binary form: exactly one bijection {N-r..N-1} -> {0..r-1} with golden arrows (s <= 6).
 B  Theorem O, dancer form: same with subsets D of I ordered by o_D, golden = b subset a and gold 0 (k <= 6).
 C  complement reverses the o-order and maps L_r onto F_r; cost identity for every bijection (k <= 5).
 D  Corollary 6.3: exact 2-adic valuation of det M[L_r, F_r] = r*C + U(r) on random matrices (k <= 4).
"""
import itertools, random, sys
from fractions import Fraction

def s2(x): return bin(x).count('1')
def v2(x):
    if x == 0: return 10**9
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)
def oE(E): return sum(2**t for t in E)

def golden_bin(s, p, g):
    if g == p: return True
    for j in range(s):            # clear bits j..s-1, all equal to 1
        top = p >> j
        if top == 2**(s - j) - 1 and g == p % 2**j: return True
    return False
def golden_bin_ctrl(s, p, g):     # control: clear a top block of bits, not required to be all ones
    if g == p: return True
    return any(g == p % 2**j for j in range(s))

def count_bij(rows, cols, ok, cap=2):
    """number of bijections rows->cols with ok(row,col), stopped at cap."""
    cols = list(cols); rows = list(rows)
    adj = {a: [c for c in cols if ok(a, c)] for a in rows}
    rows.sort(key=lambda a: len(adj[a]))
    used = set(); cnt = [0]
    def rec(i):
        if cnt[0] >= cap: return
        if i == len(rows): cnt[0] += 1; return
        for c in adj[rows[i]]:
            if c not in used:
                used.add(c); rec(i + 1); used.discard(c)
    rec(0); return cnt[0]

fails = 0; ctrl = {}
def fail(msg):
    global fails; fails += 1
    if fails <= 20: print('FAIL', msg)

# ---- A
nA = 0; ctrlA = 0
for s in range(0, 7):
    N = 2**s
    for r in range(N + 1):
        rows = range(N - r, N); cols = range(r)
        c = count_bij(rows, cols, lambda p, g: golden_bin(s, p, g)); nA += 1
        if c != 1: fail(f'A s={s} r={r} count={c}')
        if count_bij(rows, cols, lambda p, g: golden_bin_ctrl(s, p, g)) != 1: ctrlA += 1
print(f'A: {nA} cases; control (top block not all ones) fails uniqueness in {ctrlA} cases')
ctrl['A'] = ctrlA

# ---- family helpers
def family(k, I):
    I = sorted(I)
    def nxt(t): return min([u for u in I + [k] if u > t])
    h = {t: nxt(t) - t for t in I}
    def gamma(D):
        if not D: return 0
        m = min(D); return sum(h[u] for u in I if u not in D and u > m)
    return h, gamma

# ---- B
nB = 0; ctrlB = 0
for k in range(0, 7):
    for sz in range(0, k + 1):
        for I in itertools.combinations(range(k), sz):
            h, gamma = family(k, I)
            dancers = [frozenset(c) for n in range(len(I) + 1) for c in itertools.combinations(I, n)]
            dancers.sort(key=oE); N = len(dancers)
            for r in range(N + 1):
                L = dancers[N - r:]; F = dancers[:r]
                ok = lambda a, b: b <= a and gamma(a - b) == 0
                c = count_bij(L, F, ok); nB += 1
                if c != 1: fail(f'B k={k} I={I} r={r} count={c}')
                okc = lambda a, b: b <= a and gamma(a - b) <= 1   # control: allow gold 1
                if count_bij(L, F, okc) != 1: ctrlB += 1
print(f'B: {nB} cases; control (gold <= 1 allowed) fails uniqueness in {ctrlB} cases')
ctrl['B'] = ctrlB

# ---- C
def ruler(h, alpha, mu, E): return sum(h[t] - alpha * 2**t for t in E) - kappa(mu, oE(E))
nC = 0; ctrlC = 0; rnd = random.Random(4)
for k in range(0, 6):
    K = 2**k
    for sz in range(0, k + 1):
        for I in itertools.combinations(range(k), sz):
            h, gamma = family(k, I); Is = frozenset(I)
            dancers = [frozenset(c) for n in range(len(I) + 1) for c in itertools.combinations(I, n)]
            dancers.sort(key=oE); N = len(dancers)
            # complement reverses order
            for a, b in itertools.combinations(dancers, 2):
                if (oE(a) < oE(b)) != (oE(Is - a) > oE(Is - b)): fail('C reverse')
            for r in range(N + 1):
                L = dancers[N - r:]; F = dancers[:r]
                if set(Is - D for D in L) != set(F): fail('C complement')
                for alpha in (1, 2):
                    for m in (0, 1, 5):
                        U = sum(ruler(h, alpha, m, D) - ruler(h, alpha, m + K, Is - D) for D in L)
                        for _ in range(3):
                            perm = F[:]; rnd.shuffle(perm)   # any bijection L -> F (support not needed)
                            lhs = sum(ruler(h, alpha, m, D) - ruler(h, alpha, m + K, b) + gamma(D - b)
                                      for D, b in zip(L, perm))
                            rhs = U + sum(gamma(D - b) for D, b in zip(L, perm))
                            nC += 1
                            if lhs != rhs: fail(f'C cost k={k} I={I} r={r}')
                            # control: rows L, columns L (not F) breaks the identity in general
                            Uc = sum(ruler(h, alpha, m, D) - ruler(h, alpha, m + K, D) for D in L)
                            if Uc != U: ctrlC += 1
print(f'C: {nC} cost identities; control (columns = L_r) differs in {ctrlC} cases')
ctrl['C'] = ctrlC

# ---- D
def det(M):
    n = len(M)
    A = [[Fraction(x) for x in row] for row in M]; d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None: return 0
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for j in range(c, n): A[r][j] -= f * A[c][j]
    assert d.denominator == 1; return int(d)
nD = 0; ctrlD = 0; rnd = random.Random(7)
for k in range(1, 5):
    K = 2**k
    for sz in range(0, k + 1):
        for I in itertools.combinations(range(k), sz):
            h, gamma = family(k, I); Is = frozenset(I)
            dancers = [frozenset(c) for n in range(len(I) + 1) for c in itertools.combinations(I, n)]
            dancers.sort(key=oE); N = len(dancers)
            for alpha in (1, 2):
                for m in (0, 3):
                    chat = {(a, b): ruler(h, alpha, m, a) - ruler(h, alpha, m + K, b) + gamma(a - b)
                            for a in dancers for b in dancers if b <= a}
                    C = alpha * K + kappa(m, K)
                    C = max(C, -min(chat.values()))   # any C with C + chat >= 0
                    for rep in range(2):
                        M = {(a, b): (2**(C + chat[(a, b)]) * rnd.choice([1, 3, 5, -1, -3, 7])
                                      if b <= a else 0) for a in dancers for b in dancers}
                        Mc = dict(M)   # control: a non-zero entry outside the support
                        for r in range(1, N + 1):
                            L = dancers[N - r:]; F = dancers[:r]
                            U = sum(ruler(h, alpha, m, D) - ruler(h, alpha, m + K, Is - D) for D in L)
                            dd = det([[M[(a, b)] for b in F] for a in L]); nD += 1
                            if dd == 0 or v2(dd) != r * C + U: fail(f'D k={k} I={I} r={r} v={v2(dd)} want={r*C+U}')
                            outs = [(a, b) for a in L for b in F if not b <= a]
                            if outs:
                                a0, b0 = outs[0]; Mc2 = dict(M); Mc2[(a0, b0)] = 1
                                dc = det([[Mc2[(a, b)] for b in F] for a in L])
                                if dc == 0 or v2(dc) != r * C + U: ctrlD += 1
print(f'D: {nD} minors; control (one entry 1 outside the support) breaks the valuation in {ctrlD} cases')
ctrl['D'] = ctrlD

print('TOTAL FAILURES', fails)
print('CONTROLS', ctrl, 'ALL FIRE' if all(v > 0 for v in ctrl.values()) else 'SOME CONTROL SILENT')
