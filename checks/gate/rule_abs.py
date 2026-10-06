# rule_abs.py — the Main Theorem's rule exactly as printed in the paper (absolute form of the clocks),
# plus the fusion multiplicities. Grepy Bross, 5 Oct 2026. Used by the gate of the printed text.
import sys
from fractions import Fraction
INF = 10**9
def v2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def s2(x): return bin(x).count('1')
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)
def phi(x): return x + v2(x)
def digits(lam):
    N = lam + 1; k = N.bit_length() - 1
    I = [t for t in range(k) if (N >> t) & 1]
    return k, I
def dancers(I):
    out = []
    for mask in range(1 << len(I)):
        D = [I[j] for j in range(len(I)) if (mask >> j) & 1]
        out.append(D)
    out.sort(key=lambda D: sum(1 << t for t in D))
    return out
def h_of(I, k):
    nx = sorted(I) + [k]
    return {t: nx[j + 1] - t for j, t in enumerate(sorted(I))}
def pava_int(x):
    # integer antitonic fit (non-increasing), pools: (S mod p) ceil values first, then floor
    blocks = []  # [sum, count]
    for v in x:
        blocks.append([v, 1])
        while len(blocks) > 1 and Fraction(blocks[-2][0], blocks[-2][1]) <= Fraction(blocks[-1][0], blocks[-1][1]):
            s, c = blocks.pop(); blocks[-1][0] += s; blocks[-1][1] += c
    out = []
    for s, p in blocks:
        q, r = divmod(s, p)
        out += [q + 1] * r + [q] * (p - r)
    return out
def big_clocks(lam, i):
    k, I = digits(lam); h = h_of(I, k)
    raw = []
    for D in dancers(I):
        o = sum(1 << t for t in D)
        if i == 0 and o == 0: raw.append(INF); continue
        xi = lam + 1 - 2 * o
        raw.append(phi(xi) + kappa(i + o - 1, xi) + sum(h[t] for t in D))
    if i == 0:
        return [INF] + pava_int(raw[1:])
    return pava_int(raw)
def X(lam, i):
    k, I = digits(lam); g = {}
    for a in range(1, k):
        g[a] = g.get(a, 0) + 2 ** (len(I) + k - 1 - a)
    for e in big_clocks(lam, i):
        g[e] = g.get(e, 0) + 1
    return g
def mults(n):
    # fusion recursion on formal sums {lam: mult}
    def V_times(T):
        out = {}
        def add(l, c): out[l] = out.get(l, 0) + c
        for l, c in T.items():
            if l == 0: add(1, c)
            elif l % 2 == 1: add(l + 1, c)
            else:
                add(l - 1, 2 * c)
                for l2, c2 in V_times({(l - 2) // 2: 1}).items(): add(2 * l2 + 1, c * c2)
        return out
    T = {0: 1}
    for _ in range(n): T = V_times(T)
    return T
def syl2(n):
    g = {}
    for lam, c in mults(n).items():
        for e, m in X(lam, (n - lam) // 2).items():
            g[e] = g.get(e, 0) + c * m
    g.pop(INF, None)
    assert g.get(0, 0) == 0
    return dict(sorted(g.items()))
if __name__ == '__main__':
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        print(n, syl2(n))
