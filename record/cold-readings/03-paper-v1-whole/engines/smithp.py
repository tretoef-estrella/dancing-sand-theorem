"""smithp.py — exact p-adic Smith form (odd p) by elimination modulo p^E in int64 (p^E < 2^31 so products fit).
Cold reader, 2026-10-05. Same algorithm as smith2.py: unit pivot, clear column, drop row/col; when no unit is left,
divide by p (exact) and lower E. Returns Counter {valuation: count}, BIG for >= E."""
import numpy as np
from collections import Counter
BIG = 10**9


def smithp(A, p):
    E = 1
    while p ** (E + 1) < 2 ** 31:
        E += 1
    mod = p ** E
    M = np.array(A, dtype=np.int64) % mod
    n = M.shape[0]
    res = Counter(); v = 0; size = n
    while size > 0:
        W = M[:size, :size]
        unit = (W % p) != 0
        flat = int(np.argmax(unit)); a, b = divmod(flat, size)
        if not unit[a, b]:
            if not np.any(W):
                res[BIG] += size; break
            W //= p; v += 1; mod //= p
            W %= mod
            if mod == 1:
                res[BIG] += size; break
            continue
        last = size - 1
        if a != last: W[[a, last], :] = W[[last, a], :]
        if b != last: W[:, [b, last]] = W[:, [last, b]]
        inv = pow(int(W[last, last]) % mod, -1, mod)
        col = W[:last, last].copy()
        fac = (col * inv) % mod
        W[:last, :last] = (W[:last, :last] - (fac[:, None] * W[last, :last][None, :]) % mod) % mod
        res[v] += 1; size = last
    return res
