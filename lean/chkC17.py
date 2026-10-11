#!/usr/bin/env python3
"""Brute force for piece C17 (§2.1, the Laplacian of Q_n in the group ring).
Grepy Escribano, 7 Oct 2026. Exact integer arithmetic only. n = 1..6.
Every check prints PASS/FAIL; controls must FAIL (they are reported as FIRES)."""
import itertools, random, math
from math import comb

random.seed(17)
fails = 0
checks = 0
def ok(cond, msg):
    global fails, checks
    checks += 1
    if not cond:
        fails += 1
        print("FAIL", msg)

def mul(f, g, n):
    """product in Z[(Z/2)^n]; elements are dicts bitmask -> int"""
    h = {}
    for a, x in f.items():
        if x == 0: continue
        for b, y in g.items():
            if y == 0: continue
            h[a ^ b] = h.get(a ^ b, 0) + x * y
    return {k: v for k, v in h.items() if v != 0}

def add(f, g, c=1):
    h = dict(f)
    for k, v in g.items():
        h[k] = h.get(k, 0) + c * v
    return {k: v for k, v in h.items() if v != 0}

def s_i(i): return {0: 1, 1 << i: -1}
def s_S(S, n):
    f = {0: 1}
    for i in range(n):
        if S >> i & 1: f = mul(f, s_i(i), n)
    return f
def sigma(n):
    f = {}
    for i in range(n): f = add(f, s_i(i))
    return f

def smith_invariants(M):
    """invariant factors (nonneg, the zeros included) of an integer matrix (list of lists)."""
    A = [row[:] for row in M]
    r, c = len(A), len(A[0]) if A else 0
    inv = []
    t = 0
    while t < min(r, c):
        # find nonzero pivot with min abs
        piv = None
        for i in range(t, r):
            for j in range(t, c):
                if A[i][j] != 0 and (piv is None or abs(A[i][j]) < abs(A[piv[0]][piv[1]])):
                    piv = (i, j)
        if piv is None: break
        i, j = piv
        A[t], A[i] = A[i], A[t]
        for row in A: row[t], row[j] = row[j], row[t]
        while True:
            p = A[t][t]
            done = True
            for i in range(t + 1, r):
                q = A[i][t] // p
                if q:
                    A[i] = [a - q * b for a, b in zip(A[i], A[t])]
                if A[i][t] != 0:
                    done = False
            for j in range(t + 1, c):
                q = A[t][j] // p
                if q:
                    for row in A: row[j] -= q * row[t]
                if A[t][j] != 0: done = False
            if done:
                # divisibility of the rest
                bad = None
                for i in range(t + 1, r):
                    for j in range(t + 1, c):
                        if A[i][j] % p != 0: bad = (i, j); break
                    if bad: break
                if bad is None: break
                A[t] = [a + b for a, b in zip(A[t], A[bad[0]])]
                continue
            # move smallest to pivot
            piv = None
            for i in range(t, r):
                if A[i][t] != 0 and (piv is None or abs(A[i][t]) < abs(A[piv][t])): piv = i
            A[t], A[piv] = A[piv], A[t]
            pj = None
            for j in range(t, c):
                if A[t][j] != 0 and (pj is None or abs(A[t][j]) < abs(A[t][pj])): pj = j
            for row in A: row[t], row[pj] = row[pj], row[t]
        inv.append(abs(A[t][t]))
        t += 1
    zeros = min(r, c) - len(inv)
    return sorted(inv), zeros, r - len(inv)   # (nonzero invariants, ..., corank = rows - rank)

def tau(n):
    return 2 ** (2 ** n - n - 1) * math.prod(k ** comb(n, k) for k in range(1, n + 1))

def v2(x):
    e = 0
    while x % 2 == 0: x //= 2; e += 1
    return e

for n in range(1, 7):
    N = 2 ** n
    sig = sigma(n)
    # (A1), (A2)
    for j in range(n):
        ok(mul(s_i(j), s_i(j), n) == add({}, s_i(j), 2), f"A1 n={n} j={j}")
        for S in range(N):
            lhs = mul(s_i(j), s_S(S, n), n)
            rhs = s_S(S | 1 << j, n) if not S >> j & 1 else add({}, s_S(S, n), 2)
            ok(lhs == rhs, f"A2 n={n} j={j} S={S}")
    # (A3)
    for S in range(N):
        rhs = {}
        for j in range(n):
            if not S >> j & 1: rhs = add(rhs, s_S(S | 1 << j, n))
        rhs = add(rhs, s_S(S, n), 2 * bin(S).count("1"))
        ok(mul(sig, s_S(S, n), n) == rhs, f"A3 n={n} S={S}")
    # (A4) the matrix [s_S(T)] is unitriangular for inclusion
    for S in range(N):
        sv = s_S(S, n)
        for T in range(N):
            val = sv.get(T, 0)
            if T & ~S: ok(val == 0, f"A4 support n={n}")
            else: ok(val == (-1) ** bin(T).count("1"), f"A4 value n={n}")
    # (B1)
    for _ in range(5):
        f = {g: random.randint(-5, 5) for g in range(N)}
        f = {k: v for k, v in f.items() if v}
        sf = mul(sig, f, n)
        for g in range(N):
            Lf = n * f.get(g, 0) - sum(f.get(g ^ (1 << i), 0) for i in range(n))
            ok(sf.get(g, 0) == Lf, f"B1 n={n}")
    # matrix of sigma in the s-basis: column S = coords of sigma*s_S, via (A3)
    Ms = [[0] * N for _ in range(N)]
    for S in range(N):
        for j in range(n):
            if not S >> j & 1: Ms[S | 1 << j][S] += 1
        Ms[S][S] += 2 * bin(S).count("1")
    # (C1): row of the empty set is zero
    ok(all(Ms[0][S] == 0 for S in range(N)), f"C1 n={n}")
    # (C2): restricted to S != 0, lower triangular for |S| with diagonal 2|S|
    for T in range(1, N):
        for S in range(1, N):
            if Ms[T][S] != 0:
                ok(bin(T).count("1") >= bin(S).count("1"), f"C2 tri n={n}")
        ok(Ms[T][T] == 2 * bin(T).count("1") != 0, f"C2 diag n={n}")
    # (C3)/(C4): Laplacian L on Z^G (x-basis) vs T(n) = R_+ / sigma R (rows S != 0, all columns)
    L = [[0] * N for _ in range(N)]
    for g in range(N):
        L[g][g] += n
        for i in range(n): L[g][g ^ (1 << i)] -= 1
    invL, _, corL = smith_invariants(L)
    ok(corL == 1, f"C3 one free summand n={n} (corank {corL})")
    invT, _, corT = smith_invariants([Ms[T] for T in range(1, N)])
    ok(corT == 0, f"C3 T(n) finite n={n}")
    torsL = [d for d in invL if d != 1]
    torsT = [d for d in invT if d != 1]
    ok(torsL == torsT, f"C4 K(Q_n) == T(n) n={n}: {torsL} vs {torsT}")
    ok(math.prod(torsL) == tau(n), f"C4 |K| = tau n={n}")
    # (D2): Syl_2 K = 2-parts; over Z_2 the Laplacian has one zero and the 2-parts
    syl2 = sorted(2 ** v2(d) for d in torsL if v2(d) > 0)
    print(f"n={n}: |K|={math.prod(torsL)} = tau; Syl_2 K = {syl2}")

# ---- controls (must fire) ----
fires = 0
ctrl = 0
# control 1: shifted Laplacian has no free summand
n = 3; N = 8
Lc = [[0] * N for _ in range(N)]
for g in range(N):
    Lc[g][g] += n + 1
    for i in range(n): Lc[g][g ^ (1 << i)] -= 1
_, _, cor = smith_invariants(Lc)
ctrl += 1; fires += (cor != 1)
# control 2: in Z[Z/3], s^2 != 2s
def mul3(f, g):
    h = {}
    for a, x in f.items():
        for b, y in g.items(): h[(a + b) % 3] = h.get((a + b) % 3, 0) + x * y
    return {k: v for k, v in h.items() if v}
s3 = {0: 1, 1: -1}
ctrl += 1; fires += (mul3(s3, s3) != {0: 2, 1: -2})
# control 3: signless operator != sigma*
f = {0: 1, 3: 2}
sf = mul(sigma(3), f, 3)
ctrl += 1; fires += any(sf.get(g, 0) != 3 * f.get(g, 0) + sum(f.get(g ^ (1 << i), 0) for i in range(3)) for g in range(8))
# control 4: R / sigma R without removing the empty row is NOT finite
Ms = [[0] * 8 for _ in range(8)]
for S in range(8):
    for j in range(3):
        if not S >> j & 1: Ms[S | 1 << j][S] += 1
    Ms[S][S] += 2 * bin(S).count("1")
_, _, cor = smith_invariants(Ms)
ctrl += 1; fires += (cor != 0)
# control 5: a wrong tau (drop the 2-power) disagrees
ctrl += 1; fires += (math.prod(k ** comb(3, k) for k in range(1, 4)) != 384)

print(f"checks {checks}, failures {fails}; controls {fires}/{ctrl} fire")
print("FIN-OK" if fails == 0 and fires == ctrl else "FIN-BAD")
