"""rule.py — the rule of §1.2 of «The Dancing Sand Theorem» v1, written from §1 ALONE.

Cold reader «Grepy el lector frío del cubo 3», 2026-10-05.
Integers only. A 2-group is a Counter {exponent: count}; the free summand Z_2 is the key INF.

Definitions copied from §1.2:
  s2, v2, kappa(a,b) = s2(a)+s2(b)-s2(a+b), phi(x) = x + v2(x)
  lambda+1 = 2^k + sum_{t in I} 2^t ; next(t) = min{u in I ∪ {k}: u > t}; h_t = next(t)-t
  dancers D ⊆ I, o_D = sum 2^t, h(D) = sum h_t ; o-order = increasing o_D
  m_lambda(n): V.[0]=[1], V.[2l+1]=[2l+2], V.[2l+2] = 2[2l+1] + Phi(V.[l]), Phi([nu]) = [2nu+1]
  xi_D = lambda+1-2 o_D ; u_i(D) = phi(xi_D) + kappa(i+o_D-1, xi_D) + h(D) ; u_0(∅) = INF
  integer antitonic fit: PAVA blocks with strictly decreasing means; block (p positions, sum S) ->
      (S mod p) copies of ceil(S/p) then p-(S mod p) copies of floor(S/p); at shift 0, INF first, not pooled
  X(lambda,i) = ⊕_{a=1}^{k-1} (Z/2^a)^{2^{|I|+k-1-a}} ⊕ ⊕_D Z/2^{yhat_i(D)}
  Syl_2 K(Q_n) ⊕ Z_2 = ⊕_{1<=lambda<=n, lambda≡n (2)} X(lambda,(n-lambda)/2)^{m_lambda(n)}
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations

INF = 10**9  # stands for Z/2^infinity = Z_2 (never pooled)


def s2(x):
    assert x >= 0
    return bin(x).count("1")


def v2(x):
    assert x != 0
    x = abs(x)
    return (x & -x).bit_length() - 1


def kappa(a, b):
    assert a >= 0 and b >= 0
    return s2(a) + s2(b) - s2(a + b)


def phi(x):
    assert x >= 1
    return x + v2(x)


def family(lam, drop_digit=None):
    """Return (k, I, h) for the family lam. drop_digit: CONTROL ONLY — remove that element from I."""
    N = lam + 1
    k = N.bit_length() - 1
    I = [t for t in range(k) if (N >> t) & 1]
    if drop_digit is not None and drop_digit in I:
        I = [t for t in I if t != drop_digit]
    h = {}
    for t in I:
        nxt = min([u for u in I + [k] if u > t])
        h[t] = nxt - t
    return k, I, h


def dancers(I):
    """All subsets of I, in o-order (increasing o_D)."""
    out = []
    for r in range(len(I) + 1):
        for D in combinations(I, r):
            out.append(tuple(D))
    out.sort(key=lambda D: sum(1 << t for t in D))
    return out


def raw_clocks(lam, i, drop_digit=None):
    k, I, h = family(lam, drop_digit)
    res = []
    for D in dancers(I):
        oD = sum(1 << t for t in D)
        hD = sum(h[t] for t in D)
        if i == 0 and len(D) == 0:
            res.append(INF)
            continue
        xi = lam + 1 - 2 * oD
        assert xi >= 1
        res.append(phi(xi) + kappa(i + oD - 1, xi) + hD)
    return res


def pava_blocks(x):
    """Antitonic (non-increasing) least-squares fit by PAVA; merge while mean(left) <= mean(right),
    so the final block means are STRICTLY decreasing. Returns list of (sum, count)."""
    st = []
    for v in x:
        st.append([v, 1])
        while len(st) >= 2 and st[-2][0] * st[-1][1] <= st[-1][0] * st[-2][1]:
            s, c = st.pop()
            st[-1][0] += s
            st[-1][1] += c
    return st


def integer_antitonic_fit(x):
    out = []
    for S, p in pava_blocks(x):
        q, r = divmod(S, p)  # Python divmod: floor, r in [0,p)
        out += [q + 1] * r + [q] * (p - r)
    return out


def pooled_clocks(lam, i, drop_digit=None):
    u = raw_clocks(lam, i, drop_digit)
    if i == 0:
        assert u[0] == INF
        return [INF] + integer_antitonic_fit(u[1:])
    return integer_antitonic_fit(u)


def X(lam, i, drop_digit=None):
    k, I, h = family(lam, drop_digit)
    g = Counter()
    for a in range(1, k):
        g[a] += 2 ** (len(I) + k - 1 - a)
    for y in pooled_clocks(lam, i, drop_digit):
        g[y] += 1
    return g


@lru_cache(maxsize=None)
def Vdot(lam):
    """V.[lam] as a tuple of (nu, coeff)."""
    if lam == 0:
        return ((1, 1),)
    if lam % 2 == 1:
        return ((lam + 1, 1),)
    l = (lam - 2) // 2
    out = Counter({lam - 1: 2})
    for nu, c in Vdot(l):
        out[2 * nu + 1] += c
    return tuple(sorted(out.items()))


@lru_cache(maxsize=None)
def multiplicities(n):
    """m_lambda(n) as a dict."""
    if n == 0:
        return {0: 1}
    prev = multiplicities(n - 1)
    out = Counter()
    for lam, c in prev.items():
        for nu, d in Vdot(lam):
            out[nu] += c * d
    return dict(out)


def syl2_plus_free(n, drop_digit_mode=None):
    """Right-hand side of the Main Theorem: Counter of exponents, INF = free summand.
    drop_digit_mode: CONTROL ONLY. 'lowest' drops the lowest element of I in every family."""
    m = multiplicities(n)
    g = Counter()
    for lam, c in m.items():
        assert (lam - n) % 2 == 0 and 1 <= lam <= n, (n, lam)
        i = (n - lam) // 2
        dd = None
        if drop_digit_mode == "lowest":
            k, I, h = family(lam)
            dd = I[0] if I else None
        for e, cnt in X(lam, i, dd).items():
            g[e] += c * cnt
    return g


def fold(g):
    """2·A : remove the exponent-1 factors, lower the others by one (INF stays INF)."""
    out = Counter()
    for e, c in g.items():
        if e == INF:
            out[INF] += c
        elif e >= 2:
            out[e - 1] += c
    return out


def fmt(g):
    return "{" + ", ".join(("inf" if e == INF else str(e)) + ": " + str(c)
                           for e, c in sorted(g.items()) if c) + "}"


# --- the "equivalent form" of §1.2 (stated as Proposition 5.3) ---
def R(mu, D, h):
    return sum(h[t] - (1 << t) for t in D) - kappa(mu, sum(1 << t for t in D))


def equivalent_form_clock(lam, i, D):
    k, I, h = family(lam)
    assert i >= 1
    m = i - 1
    K = 1 << k
    comp = tuple(t for t in I if t not in D)
    xD = R(m, D, h) - R(m + K, comp, h)
    return k + K + kappa(m, K) + xD


if __name__ == "__main__":
    import sys
    for n in range(1, int(sys.argv[1]) + 1 if len(sys.argv) > 1 else 9):
        print(n, fmt(syl2_plus_free(n)), "mult", dict(sorted(multiplicities(n).items())))
