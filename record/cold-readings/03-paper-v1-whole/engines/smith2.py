"""smith2.py — exact 2-adic Smith form of an integer matrix, by elimination modulo 2^E.

Cold reader «Grepy el lector frío del cubo 3», 2026-10-05. No floats: numpy unsigned integers wrap
exactly modulo 2^E (E = 32 or 64), and Z/2^E is a quotient of Z_2, so every step is exact there.

Algorithm (local ring Z_2, read modulo 2^E):
  level v = 0, 1, 2, ...: while the remaining matrix has an odd entry (unit at this level), take it as
  pivot, clear its column by row operations (factor = col * pivot^{-1}), record an invariant factor 2^v,
  drop the pivot row and column (the pivot row is then cleared by column operations that touch nothing
  else, because the column is zero off the pivot). When no odd entry is left, every entry is divisible by
  2: divide the matrix by 2 (right shift), v += 1, and the modulus drops to 2^(E-v).
  When the remaining matrix is zero modulo 2^(E-v), each remaining row is an invariant factor of
  valuation >= E ("BIG"): for a Laplacian of a connected graph there must be exactly ONE (the free Z).
"""
import numpy as np
from collections import Counter

BIG = 10**9  # valuation >= E; equals rule.INF for the free summand


def inv_mod_2E(u, E):
    """inverse of odd u modulo 2^E (Newton)."""
    M = 1 << E
    u %= M
    assert u & 1
    x = u
    for _ in range(7):
        x = (x * (2 - u * x)) % M
    assert (x * u) % M == 1
    return x


def smith2(A, E=32):
    """A: square integer numpy array (any int dtype, may be negative). Returns Counter {valuation: count},
    BIG for valuation >= E."""
    dt = {32: np.uint32, 64: np.uint64}[E]
    n = A.shape[0]
    assert A.shape == (n, n)
    M = np.array(A, dtype=np.int64).astype(dt)  # wraps negatives modulo 2^E exactly
    res = Counter()
    v = 0          # current level: the remaining matrix is (original block) / 2^v, meaningful mod 2^(E-v)
    size = n
    while size > 0:
        W = M[:size, :size]
        odd = (W & dt(1))
        flat = int(np.argmax(odd))
        p, q = divmod(flat, size)
        if not odd[p, q]:
            # no unit at this level. Bits above E-v are garbage from wrapped arithmetic: clear them
            # BEFORE testing for zero and BEFORE shifting (a shift would move garbage into bit E-v-1).
            W &= dt((1 << (E - v)) - 1)
            if not np.any(W):
                res[BIG] += size
                break
            W >>= dt(1)
            v += 1
            if v >= E:
                res[BIG] += size
                break
            continue
        last = size - 1
        if p != last:
            W[[p, last], :] = W[[last, p], :]
        if q != last:
            W[:, [q, last]] = W[:, [last, q]]
        piv = int(W[last, last])
        inv = dt(inv_mod_2E(piv, E))
        col = W[:last, last].copy()
        if np.any(col):
            fac = col * inv  # wraps mod 2^E; low E-v bits are exact
            W[:last, :last] -= np.outer(fac, W[last, :last])
        res[v] += 1
        size = last
    return res


def cayley_laplacian(d, gens):
    """Laplacian of the Cayley (multi)graph of F_2^d with the generator list gens (ints, repeats allowed;
    a generator 0 is a loop, which does not change the Laplacian)."""
    N = 1 << d
    L = np.zeros((N, N), dtype=np.int64)
    idx = np.arange(N)
    for g in gens:
        L[idx, idx] += 1
        L[idx, idx ^ g] -= 1
    return L


def cube_laplacian(n):
    return cayley_laplacian(n, [1 << i for i in range(n)])


def folded_laplacian(n):
    """Q_n/<1...1> = Cayley graph of F_2^(n-1) with e_1..e_{n-1} and (1,...,1) (n >= 1)."""
    d = n - 1
    return cayley_laplacian(d, [1 << i for i in range(d)] + [(1 << d) - 1])


def x1x2_quotient_laplacian(n):
    """Q_n/<x1 x2> (CONTROL): F_2^n/<e1+e2> = F_2^(n-1) via x -> (x1+x2, x3, ..., xn);
    e1, e2 -> e'_1 (twice), e_j -> e'_{j-1}."""
    d = n - 1
    return cayley_laplacian(d, [1, 1] + [1 << i for i in range(1, d)])


def syl2_from_smith(res):
    """drop valuation-0 factors; keep BIG as the free summand."""
    return Counter({e: c for e, c in res.items() if e != 0 and c})
