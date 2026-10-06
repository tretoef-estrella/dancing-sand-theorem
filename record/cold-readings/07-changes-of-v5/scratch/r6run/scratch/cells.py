#!/usr/bin/env python3
"""cells.py — Grepy el lector frío del cubo 6, 2026-10-05. Own code, exact integers and Fractions.

Re-counts some numbers of §12.2 of «The Dancing Sand Theorem» v4 (mission §2 item 8):
  A. the cells (λ, i, α), 1 ≤ λ ≤ 127, 0 ≤ i ≤ 30, α ∈ {1, 2}: total, i = 0, i = 0 with I ≠ ∅, i ≥ 1  (S-3)
  B. the cells of A where pooling acts (raw sequence not non-increasing)                         (S-4)
  C. raw clocks u_i(D) of §1.2 (α = 1), λ ≤ 255, i ≤ 40: non-integral PAVA block means,
     without (S-6) and with (S-5) the control «+1 at the first dancer»
  D. houses (I, k, ℓ, α), 1 ≤ k ≤ 6, α ≤ 3: non-integral fit of x_H with +1 at the first dancer (S-7)
Definitions are those printed in the paper: §1.2 (u_i), §5 (R_μ, x_D), Prop. 5.4 (R♯, x♯), §7.3 (R_H, x_H).
"""
from fractions import Fraction
from itertools import combinations

def s2(x): return bin(x).count('1')
def v2(x):
    assert x > 0
    return (x & -x).bit_length() - 1
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)
def phi(x): return x + v2(x)

def family(lam):
    """λ+1 = 2^k + Σ_{t∈I} 2^t; returns k, sorted I, h (dict), dancers in o-order (as frozensets)."""
    n1 = lam + 1
    k = n1.bit_length() - 1
    I = [t for t in range(k) if (n1 >> t) & 1]
    h = {}
    for j, t in enumerate(I):
        nxt = I[j + 1] if j + 1 < len(I) else k
        h[t] = nxt - t
    dancers = []
    for r in range(len(I) + 1):
        for c in combinations(I, r):
            dancers.append(frozenset(c))
    dancers.sort(key=lambda D: sum(1 << t for t in D))
    return k, I, h, dancers

def o(E): return sum(1 << t for t in E)

def raw_clock(lam, i, D, k, h):
    """§1.2: u_i(D) = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D), (i, D) ≠ (0, ∅)."""
    xi = lam + 1 - 2 * o(D)
    return phi(xi) + kappa(i + o(D) - 1, xi) + sum(h[t] for t in D)

def cell_clocks(lam, i, alpha):
    """§5: x_D = R_m(D) − R_{m+K}(I∖D) for i ≥ 1; Prop. 5.4: x♯_D for i = 0 (D ≠ ∅). Returns the sequence in o-order."""
    k, I, h, dancers = family(lam)
    K = 1 << k
    Iset = frozenset(I)
    if i >= 1:
        m = i - 1
        R = lambda mu, E: sum(h[t] - alpha * (1 << t) for t in E) - kappa(mu, o(E))
        return [R(m, D) - R(m + K, Iset - D) for D in dancers]
    Rs = lambda E: sum(h[t] - alpha * (1 << t) for t in E) - kappa(K - 1, o(E))
    return [Rs(D) - Rs(Iset - D) for D in dancers if D]

def pava_blocks(x):
    """Antitonic (non-increasing) least-squares fit by pool-adjacent-violators, exact. Returns list of (sum, count)."""
    blocks = []
    for v in x:
        blocks.append([Fraction(v), 1])
        # merge while the previous mean is <= the last mean (block means must be strictly decreasing)
        while len(blocks) >= 2 and blocks[-2][0] * blocks[-1][1] <= blocks[-1][0] * blocks[-2][1]:
            s, c = blocks.pop()
            blocks[-1][0] += s; blocks[-1][1] += c
    return blocks

def nonincreasing(x): return all(x[j] >= x[j + 1] for j in range(len(x) - 1))
def has_nonintegral_mean(x): return any((s / c).denominator != 1 for s, c in pava_blocks(x))

def part_A_B():
    tot = i0 = i0_Ine = ige1 = 0
    pool_all = pool_ige1 = 0
    for lam in range(1, 128):
        k, I, h, dancers = family(lam)
        for i in range(0, 31):
            for alpha in (1, 2):
                tot += 1
                if i == 0:
                    i0 += 1
                    if I: i0_Ine += 1
                else:
                    ige1 += 1
                x = cell_clocks(lam, i, alpha)
                if not nonincreasing(x):
                    pool_all += 1
                    if i >= 1: pool_ige1 += 1
    print(f'A cells total {tot}; i=0 {i0}; i=0 and I!=empty {i0_Ine}; i>=1 {ige1}; total minus 240 = {tot - 240}')
    print(f'B pooling acts: all {pool_all}; i>=1 {pool_ige1}; i=0 {pool_all - pool_ige1}')

def part_C():
    cells = cells_ige1 = 0
    bad = 0
    ctrl_den = ctrl_bad = 0
    eq_check = 0
    for lam in range(1, 256):
        k, I, h, dancers = family(lam)
        K = 1 << k
        for i in range(0, 41):
            cells += 1
            if i >= 1: cells_ige1 += 1
            ds = dancers if i >= 1 else [D for D in dancers if D]
            u = [raw_clock(lam, i, D, k, h) for D in ds]
            # cross-check Prop. 5.3 / 5.4 with my own clocks of the cell (α = 1)
            x = cell_clocks(lam, i, 1)
            const = (k + K + kappa(i - 1, K)) if i >= 1 else (k + K)
            if [a - const for a in u] != x: eq_check += 1
            if has_nonintegral_mean(u): bad += 1
            if I and i >= 1:
                ctrl_den += 1
                uc = list(u); uc[0] += 1
                if has_nonintegral_mean(uc): ctrl_bad += 1
    print(f'C cells {cells} (i>=1: {cells_ige1}); Prop 5.3/5.4 mismatches {eq_check}; non-integral block mean {bad}')
    print(f'C control (+1 at first dancer, I!=empty, i>=1): non-integral in {ctrl_bad} of {ctrl_den}')

def house_x(I, k, ell, alpha):
    h = {}
    for j, t in enumerate(I):
        h[t] = (I[j + 1] if j + 1 < len(I) else k) - t
    dancers = []
    for r in range(len(I) + 1):
        for c in combinations(I, r):
            dancers.append(frozenset(c))
    dancers.sort(key=o)
    Iset = frozenset(I)
    R = lambda E: sum(h[t] - alpha * (1 << t) for t in E) - kappa(ell, o(E))
    return [R(D) - R(Iset - D) for D in dancers]

def part_D():
    houses = bad = ctrl = 0
    for k in range(1, 7):
        for mask in range(1 << k):
            I = [t for t in range(k) if (mask >> t) & 1]
            for ell in range(1 << k):
                for alpha in (1, 2, 3):
                    houses += 1
                    x = house_x(I, k, ell, alpha)
                    if has_nonintegral_mean(x): bad += 1
                    xc = list(x); xc[0] += 1
                    if has_nonintegral_mean(xc): ctrl += 1
    print(f'D houses {houses}; non-integral fit of x_H {bad}; control +1 at first dancer non-integral in {ctrl}')

# self-test of PAVA on the example of Lemma 7.2(b): x = (3,4,3,4) has fit (7/2,...)
assert [(s / c) for s, c in pava_blocks([3, 4, 3, 4])] == [Fraction(7, 2)]
# self-test on the example of §1.2: λ = 4, i = 1 raw clocks 5, 7 -> pooled 6, 6
k_, I_, h_, d_ = family(4)
assert [raw_clock(4, 1, D, k_, h_) for D in d_] == [5, 7]
k_, I_, h_, d_ = family(6)
assert [raw_clock(6, 0, D, k_, h_) for D in d_ if D] == [6, 6, 3]
print('self-tests OK')
part_A_B()
part_C()
part_D()
