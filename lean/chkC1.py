#!/usr/bin/env python3
"""Brute force for Lean piece C1 (paper v8, §7.1: antitonic fits, Lemmas 7.1-7.3).

Exact rational arithmetic (fractions). Every claim of C1_antitonic_fits.md is
checked on small sequences; controls (false variants) must FAIL somewhere.
Grepy Escribano, 6 Oct 2026.
"""
from fractions import Fraction as Q
from itertools import product
import random, sys

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

def is_cut(x, b):
    return pava(x) == pava(x[:b]) + pava(x[b:])

def strict_cut(x, b):
    z = pava(x)
    return is_cut(x, b) and z[b - 1] > z[b]

FAIL = 0
def check(cond, msg):
    global FAIL
    if not cond:
        FAIL += 1
        if FAIL <= 10:
            print("FAIL", msg)

ctrl = {}
def control(name, cond):
    ctrl.setdefault(name, 0)
    if not cond:
        ctrl[name] += 1

counts = {}
def tick(name):
    counts[name] = counts.get(name, 0) + 1

# ---------- Lemma 7.1 on a grid: characterization <=> equals the fit ----------
for N in (1, 2, 3):
    grid = [Q(a, 6) for a in range(-15, 16)]
    for x in product(range(-2, 3), repeat=N):
        z0 = pava(x)
        check(charac(x, z0), ("7.1 pava satisfies", x))
        # distance minimality vs grid non-increasing sequences
        d0 = sum((Q(a) - b) ** 2 for a, b in zip(x, z0))
        for y in product(grid, repeat=N):
            if not is_noninc(y):
                continue
            c = charac(x, y)
            check(c == (list(y) == z0), ("7.1 iff", x, y))
            d = sum((Q(a) - b) ** 2 for a, b in zip(x, y))
            check(d >= d0, ("7.1 minimal", x, y))
            check((d == d0) == (list(y) == z0), ("7.1 unique", x, y))
            tick("7.1 grid pairs")

# ---------- exhaustive integer sequences ----------
def seqs():
    for N, lo, hi in ((1, -3, 3), (2, -3, 3), (3, -3, 3), (4, -3, 3), (5, -2, 2), (6, -1, 2)):
        for x in product(range(lo, hi + 1), repeat=N):
            yield list(x)

for x in seqs():
    N = len(x); z = pava(x); iz = ifit(x)
    tick("sequences")
    check(charac(x, z), ("7.1", x))
    # integer fit: non-increasing, sums preserved on level sets, values within 1
    # NOTE: the integer fit need not be non-increasing (e.g. (-2,-2,0,-2,-1) ->
    # (-1,-1,-2,-1,-2)); the paper never claims it (Theorem 6.5 assumes it).
    if not is_noninc(iz):
        tick("ifit not non-increasing (allowed)")
    for (p, q) in level_sets(z):
        check(sum(iz[p:q + 1]) == sum(x[p:q + 1]), ("ifit sum", x))
    for b in range(1, N):
        A, B = pava(x[:b]), pava(x[b:])
        # strict drop => cut
        if z[b - 1] > z[b]:
            check(is_cut(x, b), ("strict drop is cut", x, b)); tick("drops")
        # 7.2(a)
        if is_noninc(A + B):
            check(z == A + B, ("7.2a", x, b)); tick("7.2a")
        # 7.2(c)
        if z[:b] == A or z[b:] == B:
            check(is_cut(x, b), ("7.2c", x, b)); tick("7.2c")
    # 7.2(b): cuts b_1<...<b_s, delta non-increasing constant between them
    cuts = [b for b in range(1, N) if is_cut(x, b)]
    lsets = level_sets(z)
    for mask in range(1 << len(cuts)):
        chosen = [cuts[i] for i in range(len(cuts)) if mask >> i & 1]
        pieces = [0] + chosen + [N]
        npieces = len(pieces) - 1
        for vals in product(range(0, 3), repeat=npieces):
            if any(vals[i] < vals[i + 1] for i in range(npieces - 1)):
                continue
            for scale in (Q(1), Q(1, 2)):
                delta = []
                for i in range(npieces):
                    delta += [vals[i] * scale] * (pieces[i + 1] - pieces[i])
                xd = [Q(a) + d for a, d in zip(x, delta)]
                zd = pava(xd)
                check(zd == [a + d for a, d in zip(z, delta)], ("7.2b fit shift", x, delta))
                for b in chosen:
                    check(is_cut(xd, b), ("7.2b cut kept", x, delta, b))
                tick("7.2b shifts")
                integer = scale == 1
                const_on_ls = all(len(set(delta[p:q + 1])) == 1 for (p, q) in lsets)
                if integer and const_on_ls:
                    xi = [a + int(d) for a, d in zip(x, delta)]
                    check(level_sets(pava(xi)) == lsets, ("7.2b level sets", x, delta))
                    for b in range(1, N):
                        if strict_cut(x, b):
                            check(strict_cut(xi, b), ("7.2b strict kept", x, delta, b))
                    check(ifit(xi) == [a + int(d) for a, d in zip(iz, delta)], ("7.2b ifit", x, delta))
                    tick("7.2b integer")
                    # 'in particular': changes only at strict cuts => constant on level sets
                if integer and all(strict_cut(x, b) for b in chosen if delta[b - 1] != delta[b]):
                    check(const_on_ls, ("7.2b in particular", x, delta))
                if integer:
                    xi = [a + int(d) for a, d in zip(x, delta)]
                    # CONTROL: the integer claim without the hypothesis must fail somewhere
                    control("7.2b integer claim without 'constant on level sets'",
                            ifit(xi) == [a + int(d) for a, d in zip(iz, delta)])

# the printed counterexample
x = [3, 4, 3, 4]; d = [1, 1, 0, 0]
check(pava(x) == [Q(7, 2)] * 4 and is_cut(x, 2) and not strict_cut(x, 2), "counterexample cut")
check(ifit([4, 5, 3, 4]) == [5, 4, 4, 3], "counterexample ifit(x+d)")  # x + d = (4,5,3,4)
check([a + b for a, b in zip(ifit(x), d)] == [5, 5, 3, 3], "counterexample ifit(x)+d")

# ---------- antisymmetry and Lemma 7.3 ----------
for Nh in range(1, 5):
    for half in product(range(-4, 5), repeat=Nh):
        x = list(half) + [-v for v in reversed(half)]
        N = 2 * Nh; z = pava(x); iz = ifit(x)
        tick("antisymmetric")
        check(all(z[N - 1 - j] == -z[j] for j in range(N)), ("fit antisym", x))
        check(all(iz[N - 1 - j] == -iz[j] for j in range(N)), ("ifit antisym", x))
        for b in range(1, N):
            check(is_cut(x, b) == is_cut(x, N - b), ("cut mirror", x, b))
            check(strict_cut(x, b) == strict_cut(x, N - b), ("strict mirror", x, b))
        Z1 = pava(x[:Nh]); X1 = ifit(x[:Nh])
        Z2 = [-v for v in reversed(Z1)]; X2 = [-v for v in reversed(X1)]
        check(z == [max(v, 0) for v in Z1] + [min(v, 0) for v in Z2], ("7.3 fit", x))
        check(iz == [max(v, 0) for v in X1] + [min(v, 0) for v in X2], ("7.3 ifit", x))
        check(Z2 == pava(x[Nh:]), ("7.3 Z2 = fit(second half)", x))
        # CONTROL: max/min swapped must fail
        control("7.3 with min/max swapped",
                z == [min(v, 0) for v in Z1] + [max(v, 0) for v in Z2])

# random longer real sequences (rationals) for 7.1, 7.2(a)
random.seed(1)
for _ in range(20000):
    N = random.randint(1, 12)
    x = [Q(random.randint(-20, 20), random.choice([1, 2, 3])) for _ in range(N)]
    z = pava(x); check(charac(x, z), ("7.1 random", x)); tick("random")
    for b in range(1, N):
        A, B = pava(x[:b]), pava(x[b:])
        if is_noninc(A + B):
            check(z == A + B, ("7.2a random", x, b))

for k, v in counts.items():
    print(f"checked {k}: {v}")
print("controls (number of cases where the FALSE variant failed; must be > 0):")
ok = True
for k, v in ctrl.items():
    print(f"  {k}: {v}")
    ok = ok and v > 0
print("FAILURES:", FAIL)
print("CONTROLS FIRE:", ok)
sys.exit(0 if FAIL == 0 and ok else 1)
