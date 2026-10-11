#!/usr/bin/env python3
"""Brute force for Lean piece C2 (paper v8: Lemma 6.1 tropical bound, the unique-least-term lemma behind
Corollary 6.3, Lemma 6.4 convexity, Theorem 7.4 Theorem U). Every claim of C2 is checked on small cases;
controls (false variants) must FAIL somewhere. Grepy Escribano, 6 Oct 2026."""
from fractions import Fraction as Q
from itertools import permutations, product, combinations
import random, sys
# pava, level_sets, ifit copied verbatim from chkC1.py (importing it would run C1's checks and exit)
def pava(x):
    """Antitonic (non-increasing) least-squares fit, exact."""
    blocks = []  # [sum, count]
    for v in x:
        blocks.append([Q(v), 1])
        while len(blocks) >= 2 and blocks[-2][0] / blocks[-2][1] < blocks[-1][0] / blocks[-1][1]:
            s, c = blocks.pop()
            blocks[-1][0] += s; blocks[-1][1] += c
    z = []
    for s, c in blocks:
        z += [s / c] * c
    return z

def level_sets(z):
    """Fibres {i : z_i = c} (intervals, since z is non-increasing)."""
    out, i = [], 0
    while i < len(z):
        j = i
        while j + 1 < len(z) and z[j + 1] == z[i]:
            j += 1
        out.append((i, j)); i = j + 1
    return out

def is_noninc(z):
    return all(z[i] >= z[i + 1] for i in range(len(z) - 1))

def charac(x, z):
    """Lemma 7.1 conditions."""
    if not is_noninc(z):
        return False
    for (p, q) in level_sets(z):
        s = Q(0)
        for j in range(p, q + 1):
            s += x[j] - z[j]
            if s > 0:
                return False
        if s != 0:
            return False
    return True

def ifit(x):
    """Integer fit (x integer): on each level set of p positions and sum S,
    S mod p copies of ceil(S/p) followed by floor(S/p)."""
    z = pava(x)
    out = [None] * len(x)
    for (p, q) in level_sets(z):
        S = sum(x[p:q + 1]); P = q - p + 1
        assert Q(S, P) == z[p]
        r = S % P
        for t in range(P):
            out[p + t] = -((-S) // P) if t < r else S // P
    return out


FAIL = 0; ctrl = {}; counts = {}
def check(c, m):
    global FAIL
    if not c:
        FAIL += 1
        if FAIL <= 10: print("FAIL", m)
def control(name, c): ctrl.setdefault(name, 0); ctrl[name] += (0 if c else 1)
def tick(n): counts[n] = counts.get(n, 0) + 1

def v2(n):
    n = abs(n); k = 0
    if n == 0: return 10**9
    while n % 2 == 0: n //= 2; k += 1
    return k

def det(M):
    n = len(M)
    if n == 0: return 1
    s = 0
    for p in permutations(range(n)):
        sg = 1
        for i in range(n):
            for j in range(i + 1, n):
                if p[i] > p[j]: sg = -sg
        t = sg
        for i in range(n): t *= M[i][p[i]]
        s += t
    return s

random.seed(2)
# ---------- Lemma 6.1 (tropical bound), abstract form ----------
for _ in range(3000):
    n = random.randint(1, 5)
    supp = [[random.random() < 0.7 for _ in range(n)] for _ in range(n)]
    c = [[random.randint(0, 4) for _ in range(n)] for _ in range(n)]
    M = [[(2 ** c[a][b]) * random.choice([1, 3, -1, 5, 2, 6, -4]) if supp[a][b] else 0 for b in range(n)] for a in range(n)]
    for r in range(1, n + 1):
        A = random.sample(range(n), r); B = random.sample(range(n), r)
        sub = [[M[a][b] for b in B] for a in A]
        costs = [sum(c[A[i]][B[p[i]]] for i in range(r)) for p in permutations(range(r)) if all(supp[A[i]][B[p[i]]] for i in range(r))]
        D = det(sub)
        if costs:
            T = min(costs)
            check(D % (2 ** T) == 0, ("6.1", M, A, B)); tick("6.1 minors")
            control("6.1 with T+1 (must fail somewhere)", D % (2 ** (T + 1)) == 0)
        else:
            check(D == 0, ("6.1 empty support", M, A, B)); tick("6.1 empty")

print('section 6.1 done', counts, flush=True)
# ---------- unique least term (Corollary 6.3) ----------
for _ in range(20000):
    k = random.randint(1, 6); v = random.randint(0, 5)
    terms = [(2 ** v) * random.choice([1, 3, -1, -3, 5])] + [(2 ** (v + random.randint(1, 3))) * random.randint(-5, 5) for _ in range(k - 1)]
    random.shuffle(terms); S = sum(terms)
    check(S % (2 ** v) == 0 and S % (2 ** (v + 1)) != 0, ("unique least", terms)); tick("unique least")
    # control: two terms of least valuation can cancel
    t2 = [2 ** v, 2 ** v]
    control("two least terms (must fail)", sum(t2) % (2 ** (v + 1)) != 0)

print('section unique-least done', flush=True)
# ---------- Lemma 6.4 (convexity) ----------
def U(x, r): N = len(x); return sum(x[N - r:])
def Y(yh, r): N = len(yh); return sum(yh[N - r:])
def convex_seqs(N, lo, hi, bound):
    """all d: {0..N} -> Z, d0 = 0, non-decreasing increments in [lo, hi], d(r) <= bound(r)."""
    out = []
    def rec(d, last):
        r = len(d) - 1
        if r == N: out.append(list(d)); return
        for inc in range(max(lo, last), hi + 1):
            nd = d[-1] + inc
            if nd <= bound(r + 1): d.append(nd); rec(d, inc); d.pop()
    rec([0], lo)
    return out
for N, lo, hi in ((1, -3, 3), (2, -3, 3), (3, -3, 3), (4, -2, 3), (5, -2, 2), (6, -1, 2)):
    for x in product(range(lo, hi + 1), repeat=N):
        x = list(x); yh = ifit(x)
        ds = convex_seqs(N, 2 * lo - 1, 2 * hi + 1, lambda r: U(x, r))
        wrong = []  # control: the integer fit with every value rounded down
        z = pava(x); wrong = [None] * N
        for (p, q) in level_sets(z):
            S = sum(x[p:q + 1]); P = q - p + 1; rr = S % P
            for t in range(P): wrong[p + t] = S // P  # all floors (a sum too small whenever S mod P > 0)
        for d in ds:
            check(all(d[r] <= Y(yh, r) for r in range(N + 1)), ("6.4", x, d)); tick("6.4 (x, d)")
            control("6.4 with all floors (must fail)", all(d[r] <= Y(wrong, r) for r in range(N + 1)))
        check(Y(yh, N) == U(x, N), ("Y(N)=U(N)", x)); tick("6.4 sequences")
        # control: without convexity (all d with d0=0, d<=U, small range)
        for d in (product(range(-3, 4), repeat=N) if N <= 3 else ()):
            d = [0] + list(d)
            if all(d[r] <= U(x, r) for r in range(N + 1)):
                control("6.4 without convexity (must fail)", all(d[r] <= Y(yh, r) for r in range(N + 1)))

print('section 6.4 done', counts, flush=True)
# ---------- Theorem 7.4 (Theorem U), abstract form ----------
def matchings(rows, cols, arr):
    for perm in permutations(cols):
        if all(arr[a][b] for a, b in zip(rows, perm)): yield list(zip(rows, perm))
for _ in range(1500):
    N = random.randint(1, 5)
    yh = sorted([random.randint(-4, 4) for _ in range(N)], reverse=random.random() < 0.5)
    v = sorted([Q(random.randint(-6, 6), random.choice([1, 2])) for _ in range(N)], reverse=True)
    w = [None] * N
    for j in range(N): w[N - 1 - j] = v[j] - yh[j]            # (U2)
    u1 = all(w[i] >= w[i + 1] for i in range(N - 1))           # (U1) for w
    arr = [[random.random() < 0.6 for _ in range(N)] for _ in range(N)]
    for a in range(N): arr[a][a] = True
    cost = [[v[a] - w[b] + random.choice([0, 0, Q(1, 2), 1, 3]) for b in range(N)] for a in range(N)]  # (U3)
    for r in range(N + 1):
        Yr = sum(yh[N - r:])
        best = None
        for R in combinations(range(N), r):
            for C in combinations(range(N), r):
                for m in matchings(R, C, arr):
                    s = sum(cost[a][b] for a, b in m)
                    best = s if best is None else min(best, s)
        if best is None: continue
        if u1:
            check(best >= Yr, ("U", N, r)); tick("U (instance, r)")
        else:
            control("U without (U1) for w (must fail)", best >= Yr)

for k, val in counts.items(): print(f"checked {k}: {val}")
print("controls (cases where the FALSE variant failed; must be > 0):")
ok = True
for k, val in ctrl.items(): print(f"  {k}: {val}"); ok = ok and val > 0
print("FAILURES:", FAIL); print("CONTROLS FIRE:", ok)
sys.exit(0 if FAIL == 0 and ok else 1)
