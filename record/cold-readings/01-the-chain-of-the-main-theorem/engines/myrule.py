# myrule.py — the cold reader's own implementation of the Dancing Sand rule (2026-10-04).
# Written from the statements in MISSION.md §1 and FLIGHT1 C.4 / D.5, FLIGHT4 A.4 — no flight code consulted.
# Everything is exact integer arithmetic.
from functools import lru_cache
from fractions import Fraction


def s2(x):
    return bin(x).count('1')


def kappa(a, b):
    """number of carries when adding a and b in base 2 (Kummer)"""
    return s2(a) + s2(b) - s2(a + b)


def v2(x):
    if x == 0:
        return None  # infinite
    return (x & -x).bit_length() - 1


def v2fact(x):
    return x - s2(x)  # Legendre


def digits(lam):
    L = lam + 1
    k = L.bit_length() - 1
    I = [t for t in range(k) if (L >> t) & 1]
    return k, I


# ---------------- multiplicities -----------------
@lru_cache(None)
def VxT(l):
    """fusion recursion: V (x) T(l) as a dict {lambda: mult}"""
    if l == 0:
        return ((1, 1),)
    if l % 2 == 1:
        return ((l + 1, 1),)
    lp = (l - 2) // 2
    d = {l - 1: 2}
    for nu, c in VxT(lp):
        d[2 * nu + 1] = d.get(2 * nu + 1, 0) + c
    return tuple(sorted(d.items()))


@lru_cache(None)
def mult_fusion(n):
    if n == 1:
        return ((1, 1),)
    d = {}
    for lam, c in mult_fusion(n - 1):
        for mu, e in VxT(lam):
            d[mu] = d.get(mu, 0) + c * e
    return tuple(sorted(d.items()))


def char_T(lam):
    """Donkin character at p = 2: prod_{i<k}(e^{2^i}+e^{-2^i}) prod_{i in I}(e^{2^i}+e^{-2^i})"""
    k, I = digits(lam)
    ch = {0: 1}
    for f in list(range(k)) + I:
        w = 1 << f
        new = {}
        for a, c in ch.items():
            new[a + w] = new.get(a + w, 0) + c
            new[a - w] = new.get(a - w, 0) + c
        ch = new
    return ch


def mult_peel(n):
    ch = {0: 1}
    for _ in range(n):
        new = {}
        for a, c in ch.items():
            new[a + 1] = new.get(a + 1, 0) + c
            new[a - 1] = new.get(a - 1, 0) + c
        ch = new
    res = {}
    while True:
        ch = {a: c for a, c in ch.items() if c != 0}
        if not ch:
            break
        top = max(ch)
        c = ch[top]
        if c < 0:
            raise ValueError("negative multiplicity")
        res[top] = c
        for a, e in char_T(top).items():
            ch[a] = ch.get(a, 0) - c * e
    return tuple(sorted(res.items()))


# ---------------- pooling -----------------
def pava_int(vals):
    """non-increasing isotonic fit (pool adjacent violators), then integer splitting of each block:
    a block of p values with sum T -> (T mod p) values ceil(T/p) first, then floor(T/p).
    Returns the list in the same order."""
    blocks = []  # [sum, count]
    for x in vals:
        blocks.append([x, 1])
        # violation: previous block mean < this block mean (we want non-increasing)
        while len(blocks) > 1 and Fraction(blocks[-2][0], blocks[-2][1]) < Fraction(blocks[-1][0], blocks[-1][1]):
            s, c = blocks.pop()
            blocks[-1][0] += s
            blocks[-1][1] += c
    out = []
    for s, c in blocks:
        q, r = divmod(s, c)
        out += [q + 1] * r + [q] * (c - r)
    return out


def pava_real(vals):
    blocks = []
    for x in vals:
        blocks.append([Fraction(x), 1])
        while len(blocks) > 1 and blocks[-2][0] / blocks[-2][1] < blocks[-1][0] / blocks[-1][1]:
            s, c = blocks.pop()
            blocks[-1][0] += s
            blocks[-1][1] += c
    out = []
    for s, c in blocks:
        out += [s / c] * c
    return out


# ---------------- big clocks -----------------
def dancers(I):
    """all subsets D of I in o-order (o_D increasing)"""
    Ds = []
    for mask in range(1 << len(I)):
        D = tuple(I[j] for j in range(len(I)) if (mask >> j) & 1)
        Ds.append(D)
    Ds.sort(key=lambda D: sum(1 << t for t in D))
    return Ds


def nxt(t, I, k):
    return min([u for u in I if u > t] + [k])


def B_naive(mu, j):
    """flight 1 C.4: sum_{r=0}^{mu} (1 + v2(j+r)) - v2(mu!); None if j == 0 (a zero room: Z)"""
    if j == 0:
        return None
    return sum(1 + v2(j + r) for r in range(mu + 1)) - v2fact(mu)


def big_clocks_B(lam, i, pool=True):
    """flight 1 form: naive clocks of the Weyl factors + transfers, pooled. Returns list (o-order); None = Z."""
    k, I = digits(lam)
    Ds = dancers(I)
    u = []
    for D in Ds:
        oD = sum(1 << t for t in D)
        mu = lam - 2 * oD
        b = B_naive(mu, i + oD)
        if b is None:
            u.append(None)
        else:
            u.append(b + sum(nxt(t, I, k) - t for t in D))
    if not pool:
        return u
    if u[0] is None:
        return [None] + pava_int(u[1:])
    return pava_int(u)


def R_ruler(mu, D, I, k, alpha=1):
    """mission: R_mu(D) = sum_{t in D} (h_t - alpha 2^t) - #carries(mu + o_D)"""
    oD = sum(1 << t for t in D)
    return sum(nxt(t, I, k) - t - alpha * (1 << t) for t in D) - kappa(mu, oD)


def big_clocks_X(lam, i, pool=True, ctrl=None, alpha=1):
    """mission form, i >= 1: x_D = R_m(D) - R_{m+K}(I\\D), pooled, plus the constant k + alpha K + kappa(m, K).
    ctrl='m_only' reads the column ruler at m instead of m + K (the mission's control)."""
    assert i >= 1
    k, I = digits(lam)
    K = 1 << k
    m = i - 1
    Ds = dancers(I)
    x = []
    for D in Ds:
        E = tuple(t for t in I if t not in D)
        mc = m if ctrl == 'm_only' else m + K
        x.append(R_ruler(m, D, I, k, alpha) - R_ruler(mc, E, I, k, alpha))
    const = k + alpha * K + kappa(m, K)
    y = pava_int(x) if pool else x
    return [const + t for t in y]


def small_clocks(lam):
    k, I = digits(lam)
    return {a: 2 ** (len(I) + k - 1 - a) for a in range(1, k)}


def group_rule(n, form='B', pool=True, ctrl=None, mults=None):
    """Syl_2 K(Q_n) (+) Z_2 by the rule, as {exponent: count} with 'Z' for the free part."""
    if mults is None:
        mults = mult_fusion(n)
    G = {}
    for lam, c in mults:
        if c == 0:
            continue
        i = (n - lam) // 2
        for a, e in small_clocks(lam).items():
            G[a] = G.get(a, 0) + c * e
        if form == 'B' or i == 0:
            bc = big_clocks_B(lam, i, pool=pool)
        else:
            bc = big_clocks_X(lam, i, pool=pool, ctrl=ctrl)
        for e in bc:
            key = 'Z' if e is None else e
            G[key] = G.get(key, 0) + c
    return G


def fmt(G):
    keys = sorted([e for e in G if e != 'Z' and G[e]]) + (['Z'] if G.get('Z') else [])
    return '{' + ', '.join(f'{e}:{G[e]}' for e in keys) + '}'


if __name__ == '__main__':
    import sys
    for n in range(1, int(sys.argv[1]) + 1):
        print(n, fmt(group_rule(n)))
