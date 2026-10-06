"""lattices.py — the dance lattices T(lambda) from §3.1/§3.3 (copied verbatim from engines/family_lattice.py so that
other engines can import them without running that script). Cold reader, 2026-10-05."""
import numpy as np


def Phi(F, w):
    n = len(w)
    G = np.zeros((2 * n, 2 * n), dtype=np.int64)  # basis: b0 n_j (0..n-1), b1 n_j (n..2n-1); columns = images
    for j in range(n):
        G[n + j, j] = 1                    # F(b0 n_j) = b1 n_j
        G[:n, n + j] = 2 * F[:, j]         # F(b1 n_j) = 2 b0 F n_j
    return G, [2 * x + 1 for x in w] + [2 * x - 1 for x in w]


def Vtensor(F, w):
    n = len(w)
    G = np.zeros((2 * n, 2 * n), dtype=np.int64)  # basis b0⊗m_j, b1⊗m_j
    for j in range(n):
        G[n + j, j] += 1                   # F b0 = b1
        G[:n, j] += F[:, j]                # b0 ⊗ F m
        G[n:, n + j] += F[:, j]            # F(b1 ⊗ m) = b1 ⊗ F m
    return G, [x + 1 for x in w] + [x - 1 for x in w]


def T(lam):
    if lam == 0:
        return np.zeros((1, 1), dtype=np.int64), [0]
    if lam % 2 == 1:
        return Phi(*T((lam - 1) // 2))
    return Vtensor(*Phi(*T((lam - 2) // 2)))


