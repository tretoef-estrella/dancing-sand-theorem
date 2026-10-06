# fitlib.py — Grepy el lector frío del cubo 4, 2026-10-05.
# Exact antitonic (non-increasing) least-squares fit, written from §7.1 of the paper, my own code.
# Everything is in integers and Fractions. The PAVA result is re-verified against the
# characterization of Lemma 7.1 (an independent test of the fit), so a bug in the PAVA loop
# cannot pass silently.
from fractions import Fraction


def pava_blocks(x):
    """Blocks [start, length, sum] of the antitonic fit of x (non-increasing).
    Adjacent blocks with equal means are merged (as §1.2 of v2 says)."""
    blocks = []
    for j, v in enumerate(x):
        blocks.append([j, 1, Fraction(v)])
        # merge while the previous mean is <= the last mean (non-increasing needs strict >)
        while len(blocks) >= 2:
            s0, p0, S0 = blocks[-2]
            s1, p1, S1 = blocks[-1]
            if S0 * p1 <= S1 * p0:
                blocks[-2] = [s0, p0 + p1, S0 + S1]
                blocks.pop()
            else:
                break
    return blocks


def fit(x):
    z = []
    for s, p, S in pava_blocks(x):
        z.extend([S / p] * p)
    return z


def level_sets(z):
    """Maximal runs of equal values of z, as (start, length)."""
    out = []
    j = 0
    n = len(z)
    while j < n:
        e = j
        while e + 1 < n and z[e + 1] == z[j]:
            e += 1
        out.append((j, e - j + 1))
        j = e + 1
    return out


def check_lemma71(x, z):
    """Lemma 7.1: z non-increasing, and on every level set the sum of x - z is 0 and every
    prefix sum is <= 0. Returns True iff z = fit(x) by that characterization."""
    n = len(x)
    if len(z) != n:
        return False
    for j in range(n - 1):
        if z[j] < z[j + 1]:
            return False
    for s, p in level_sets(z):
        acc = Fraction(0)
        for j in range(s, s + p):
            acc += Fraction(x[j]) - z[j]
            if acc > 0:
                return False
        if acc != 0:
            return False
    return True


def fit_checked(x):
    z = fit(x)
    assert check_lemma71(x, z), ("PAVA disagrees with Lemma 7.1", x, z)
    return z


def int_fit(x):
    """Integer fit of an integer sequence (§1.2 / §7.1): on each level set of p positions with
    sum S, (S mod p) copies of ceil(S/p) then p - (S mod p) copies of floor(S/p)."""
    z = fit_checked(x)
    out = []
    for s, p in level_sets(z):
        S = sum(x[s:s + p])
        assert S == z[s] * p
        S = int(S)
        q, r = divmod(S, p)          # q = floor(S/p), 0 <= r < p
        out.extend([q + 1] * r + [q] * (p - r))
    return out


def is_cut(x, b):
    """x is cut at b (0 < b < N): fit(x) = fit(x_<b) ++ fit(x_>=b)."""
    assert 0 < b < len(x)
    return fit_checked(x) == fit_checked(x[:b]) + fit_checked(x[b:])


def is_strict_cut(x, b):
    z = fit_checked(x)
    return is_cut(x, b) and z[b - 1] > z[b]


def all_cuts(x):
    return [b for b in range(1, len(x)) if is_cut(x, b)]


def strict_cuts(x):
    z = fit_checked(x)
    return [b for b in range(1, len(x)) if is_cut(x, b) and z[b - 1] > z[b]]


def floor_frac(q):
    return q.numerator // q.denominator


def ceil_frac(q):
    return -((-q.numerator) // q.denominator)


def separation_ok(x):
    """Lemma 7.9's property: adjacent level sets mu_A > mu_B have floor(mu_A) >= ceil(mu_B)."""
    z = fit_checked(x)
    ls = level_sets(z)
    for (s0, p0), (s1, p1) in zip(ls, ls[1:]):
        if floor_frac(z[s0]) < ceil_frac(z[s1]):
            return False
    return True


if __name__ == "__main__":
    # self-test on the two hand examples
    for x, d in (([3, 4, 3, 4], [1, 1, 0, 0]), ([1, 2, 0, 3], [1, 1, 0, 0])):
        xd = [a + b for a, b in zip(x, d)]
        print("x", x, "fit", [str(v) for v in fit_checked(x)], "cuts", all_cuts(x),
              "strict", strict_cuts(x))
        print("  intfit(x+d)", int_fit(xd), " intfit(x)+d",
              [a + b for a, b in zip(int_fit(x), d)],
              " fit(x+d)==fit(x)+d:", fit_checked(xd) == [a + b for a, b in zip(fit_checked(x), d)])
