#!/usr/bin/env python3
"""Brute force for Lean piece C49b (paper v8 §10.6, Theorem 10.16 at c = 0, l >= 1, by congruence).
Grepy Escribano, 10 Oct 2026. Reuses the lattice dance of chkC48b.py (itself on chkC43.py).
Claims measured, for Xi_c = 2^alpha (D + c) + eta F + sum_{m>=2} z_m F^(m) (constants, eta a unit, alpha >= 2)
and sigma_c = 2^alpha (D + c) + F, on T(l), l >= 1, k = number of moves:
 (T) congruence transport: if two systems agree mod 2^M then the final matrices agree mod 2^(M - k);
     instance: Xi_0 and Xi_{2^N} agree mod 2^(N + alpha), so fin(Xi_0) = fin(Xi_{2^N}) mod 2^(N + alpha - k);
     same for sigma.
 (V) at c = 0: fin(Xi_0) and fin(sigma_0) have the same zero entries and the same entry valuations.
 (S) at c = 0: same Smith exponents of the final matrices (one exponent infinite) and of Xi, sigma on T(l).
Controls: eta = 2; alpha = 1; the bound N + alpha - k + 1 (should fail somewhere, i.e. the loss is real)."""
import random, sys
sys.path.insert(0, '.')
from fractions import Fraction
src = open('chkC48b.py').read()
exec(src[:src.index('fired = {}')])
random.seed(4902)
fired = {}
def fire(name, c): fired[name] = fired.get(name, False) or c
def xi(alpha, c, eta, z):
    return mk_op(lambda d: 2 ** alpha * (d + c), eta, lambda m_, f: z[m_])
def minv(A, B):
    """min valuation of A - B entrywise (None if equal)"""
    vs = [vq(a - b) for ra, rb in zip(A, B) for a, b in zip(ra, rb)]
    vs = [v for v in vs if v is not None]
    return min(vs) if vs else None
cells = 0
zero = {m_: Fraction(0) for m_ in range(MMAX)}
for l in range(1, 10):
    Tl = T(l)
    for alpha in (2, 3):
        s0 = act(xi(alpha, 0, 1, zero), Tl, l + 1)
        okS0, finS0, k = dance_lattice(l, s0, 1)
        ok(okS0, ("sigma_0 dance clean", l, alpha))
        for N in (3, 5, 8):
            sN = act(xi(alpha, 2 ** N, 1, zero), Tl, l + 1)
            okSN, finSN, _ = dance_lattice(l, sN, 1)
            v = minv(finS0, finSN)
            ok(v is None or v >= N + alpha - k, ("T sigma", l, alpha, N, v, k))
        for trial in range(4):
            eta = Fraction(random.choice([1, -1, 3, -3, 5, 7]), random.choice([1, 3, 5]))
            z = {m_: Fraction(random.randint(-7, 7), random.choice([1, 3, 5, 7])) for m_ in range(MMAX)}
            cells += 1
            M0 = act(xi(alpha, 0, eta, z), Tl, l + 1)
            ok0, fin0, k0 = dance_lattice(l, M0, 1)
            ok(ok0 and k0 == k, ("Xi_0 dance clean", l, alpha, trial))
            if not ok0: continue
            # (T)
            for N in (3, 5, 8):
                MN = act(xi(alpha, 2 ** N, eta, z), Tl, l + 1)
                okN, finN, _ = dance_lattice(l, MN, 1)
                ok(okN, ("Xi_2^N clean", l, alpha, N))
                ok(minv(M0, MN) is not None and minv(M0, MN) >= N + alpha, ("systems agree mod 2^(N+alpha)", l, N))
                v = minv(fin0, finN)
                ok(v is None or v >= N + alpha - k, ("T Xi", l, alpha, N, v, k))
                fire("bound + 1 fails somewhere", v is not None and v < N + alpha - k + 1)
            # (V)
            for r1, r2 in zip(fin0, finS0):
                for a, b in zip(r1, r2):
                    ok((a == 0) == (b == 0), ("support", l, alpha, trial))
                    if a != 0 and b != 0: ok(vq(a) == vq(b), ("valuation", l, alpha, trial))
            # (S)
            ok(smith_exps(fin0) == smith_exps(finS0), ("final Smith c = 0", l, alpha, trial))
            ok(smith_exps(M0) == smith_exps(s0), ("coker Xi_0 = coker sigma_0", l, alpha, trial))
            ok(smith_exps(fin0)[-1] is None, ("one infinite exponent", l))
        # controls
        z = {m_: Fraction(random.randint(-7, 7)) for m_ in range(MMAX)}
        Mb = act(xi(alpha, 0, 2, z), Tl, l + 1)
        okb, finb, _ = dance_lattice(l, Mb, 1)
        fire("eta = 2", (not okb) or smith_exps(Mb) != smith_exps(s0))
        M1 = act(xi(1, 0, 1, z), Tl, l + 1)
        ok1, fin1, _ = dance_lattice(l, M1, 1)
        fire("alpha = 1", (not ok1) or smith_exps(M1) != smith_exps(act(xi(1, 0, 1, zero), Tl, l + 1)))
        s1 = act(xi(alpha, 1, 1, zero), Tl, l + 1)
        okS1, finS1, _ = dance_lattice(l, s1, 1)
        fire("support of sigma_1 instead of sigma_0", any((a == 0) != (b == 0) for r1, r2 in zip(finS0, finS1) for a, b in zip(r1, r2)))
print("cells", cells, "checks", checks, "failures", fails)
print("controls fired", sum(fired.values()), "of", len(fired), fired)
