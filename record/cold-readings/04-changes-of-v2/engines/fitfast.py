# fitfast.py — Grepy el lector frío del cubo 4, 2026-10-05.
# Integer-only PAVA for integer sequences (blocks = level sets, means compared by cross-multiplication),
# with the Lemma 7.1 characterization re-checked in integers. Cross-validated against fitlib.py
# (Fractions) on every house in gate_houses_mine.py.


def blocks(x):
    """Level sets of the antitonic fit of the integer sequence x, as [start, p, S] (S = sum)."""
    bl = []
    for j, v in enumerate(x):
        bl.append([j, 1, v])
        while len(bl) >= 2 and bl[-2][2] * bl[-1][1] <= bl[-1][2] * bl[-2][1]:
            s0, p0, S0 = bl[-2]
            _, p1, S1 = bl[-1]
            bl[-2] = [s0, p0 + p1, S0 + S1]
            bl.pop()
    # Lemma 7.1 in integers: strictly decreasing means; prefix sums p*sum - (len)*S <= 0, total 0
    for (s0, p0, S0), (s1, p1, S1) in zip(bl, bl[1:]):
        assert S0 * p1 > S1 * p0, "means not strictly decreasing"
    for s, p, S in bl:
        acc = 0
        for j in range(s, s + p):
            acc += x[j]
            assert p * acc - (j - s + 1) * S <= 0, "prefix condition of Lemma 7.1 fails"
        assert acc == S
    return bl


def levels(bl):
    return [(s, p) for s, p, S in bl]


def int_fit_bl(bl):
    out = []
    for s, p, S in bl:
        q, r = divmod(S, p)
        out.extend([q + 1] * r + [q] * (p - r))
    return out


def separation_bl(bl):
    for (s0, p0, S0), (s1, p1, S1) in zip(bl, bl[1:]):
        if S0 // p0 < -((-S1) // p1):
            return False
    return True


def strict_drop(bl, b):
    """True iff position b (0<b<N) is a boundary between two level sets."""
    return any(s == b for s, p, S in bl[1:])
