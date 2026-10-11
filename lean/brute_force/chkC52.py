# chkC52.py — brute force for Lean piece C52 (odd parts). Grepy Escribano, 10 Oct 2026.
# (1) Fourier identities as integer matrices; (2) p-parts of direct Smith forms vs (B0),(B1),(C4),(C5); controls.
import numpy as np, itertools
from math import comb
fails = 0; checks = 0
def ok(c, msg):
    global fails, checks
    checks += 1
    if not c:
        fails += 1; print("FAIL", msg)

def popc(x): return bin(x).count('1')
def chi(S, g): return -1 if popc(S & g) % 2 else 1

def lap_cube(n):
    N = 1 << n; L = np.zeros((N, N), dtype=np.int64)
    for g in range(N):
        L[g, g] += n
        for i in range(n): L[g, g ^ (1 << i)] -= 1
    return L

def fold_reps(n):  # representatives of G/<1>: top bit 0
    return [w for w in range(1 << n) if not (w >> (n - 1)) & 1]
def frep(n, w): return w ^ ((1 << n) - 1) if (w >> (n - 1)) & 1 else w

def lap_fold(n):
    reps = fold_reps(n); pos = {w: k for k, w in enumerate(reps)}; N = len(reps)
    L = np.zeros((N, N), dtype=np.int64)
    for w in reps:
        a = pos[w]; L[a, a] += n
        for i in range(n): L[a, pos[frep(n, w ^ (1 << i))]] -= 1
    return L

# (1) identities
for n in range(0, 7):
    N = 1 << n
    Fm = np.array([[chi(S, g) for g in range(N)] for S in range(N)], dtype=np.int64)  # fourier: row S, col g
    Im = Fm.T.copy()                                                                     # ifourier: row g, col S
    D = np.diag([2 * popc(S) for S in range(N)]).astype(np.int64)
    L = lap_cube(n)
    ok((Fm @ L == D @ Fm).all(), f"F1 n={n}")
    ok((L @ Im == Im @ D).all(), f"F2 n={n}")
    ok((Im @ Fm == N * np.eye(N, dtype=np.int64)).all() and (Fm @ Im == N * np.eye(N, dtype=np.int64)).all(), f"F3 n={n}")
for n in range(1, 7):
    reps = fold_reps(n); ev = [S for S in range(1 << n) if popc(S) % 2 == 0]
    # chiBar well defined
    ok(all(chi(S, w) == chi(S, frep(n, w ^ ((1 << n) - 1))) for S in ev for w in range(1 << n)), f"X0 n={n}")
    Fb = np.array([[chi(S, w) for w in reps] for S in ev], dtype=np.int64); Ib = Fb.T.copy()
    Db = np.diag([2 * popc(S) for S in ev]).astype(np.int64); Lb = lap_fold(n); M = 1 << (n - 1)
    ok(len(ev) == M == len(reps), f"sizes n={n}")
    ok((Fb @ Lb == Db @ Fb).all(), f"C1 n={n}")
    ok((Lb @ Ib == Ib @ Db).all(), f"C2 n={n}")
    ok((Ib @ Fb == M * np.eye(M, dtype=np.int64)).all() and (Fb @ Ib == M * np.eye(M, dtype=np.int64)).all(), f"C3 n={n}")

# (2) p-adic Smith forms
EXP = {3: 19, 5: 13, 7: 11, 2: 30}
def vp(x, p):
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
def smith_p(L, p):
    E = EXP[p]; MOD = p ** E
    A = np.array(L, dtype=np.int64) % MOD
    out = {}; zeros = 0
    while A.shape[0] > 0:
        nz = np.argwhere(A != 0)
        if len(nz) == 0: zeros += A.shape[0]; break
        best = None
        for (r, c) in nz:
            v = vp(int(A[r, c]), p)
            if best is None or v < best[0]:
                best = (v, r, c)
                if v == 0: break
        v, r, c = best
        u = int(A[r, c]) // p ** v; uinv = pow(u, -1, MOD)
        row = (A[r] * uinv) % MOD
        col = A[:, c] // p ** v
        A = (A - np.outer(col, row) % MOD) % MOD
        A = np.delete(np.delete(A, r, 0), c, 1)
        if v > 0: out[v] = out.get(v, 0) + 1
    return out, zeros
def profile(vals, p):
    d = {}
    for x in vals:
        v = vp(x, p)
        if v > 0: d[v] = d.get(v, 0) + 1
    return d
ctrl = {"fold_vs_all": 0, "cube_vs_even": 0, "p2_cube": 0}
for p in (3, 5, 7):
    for n in range(1, 9):
        sm, z = smith_p(lap_cube(n), p)
        ok(z == 1, f"cube zero factors p={p} n={n} z={z}")
        B0 = profile([2 * popc(S) for S in range(1, 1 << n)], p)
        B1 = profile([j for j in range(1, n + 1) for _ in range(comb(n, j))], p)
        ok(sm == B0, f"B0 p={p} n={n} {sm} {B0}"); ok(sm == B1, f"B1 p={p} n={n}")
        ev = profile([2 * popc(S) for S in range(1, 1 << n) if popc(S) % 2 == 0], p)
        if sm != ev: ctrl["cube_vs_even"] += 1
    for n in range(1, 10):
        sm, z = smith_p(lap_fold(n), p)
        ok(z == 1, f"fold zero factors p={p} n={n} z={z}")
        C4 = profile([2 * popc(S) for S in range(1, 1 << n) if popc(S) % 2 == 0], p)
        C5 = profile([2 * 2 * (t + 1) for t in range(n // 2) for _ in range(comb(n, 2 * (t + 1)))], p)
        ok(sm == C4, f"C4 p={p} n={n} {sm} {C4}"); ok(sm == C5, f"C5 p={p} n={n}")
        allS = profile([2 * popc(S) for S in range(1, 1 << n)], p)
        if sm != allS: ctrl["fold_vs_all"] += 1
for n in range(2, 9):
    sm, z = smith_p(lap_cube(n), 2)
    if sm != profile([2 * popc(S) for S in range(1, 1 << n)], 2): ctrl["p2_cube"] += 1
print("checks", checks, "fails", fails)
print("controls (number of cells where the false variant FAILS; each must be > 0):", ctrl)
print("CONTROLS-FIRE" if all(v > 0 for v in ctrl.values()) else "CONTROL-SILENT")
