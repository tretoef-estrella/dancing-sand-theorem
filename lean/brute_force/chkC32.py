#!/usr/bin/env python3
"""Brute force for piece C32 (Theorem 3.8: the groups of the families). Grepy Escribano, 8 Oct 2026.
Independent of every earlier script. Two models, built separately:
  * the LATTICE model of T(λ) (C29): T(0) = A (weight 0, F = 0); Φ(N): basis (e, j), weight
    2 wt(j) + (1 if e = 0 else −1), F(b0 n) = b1 n, F(b1 n) = 2 b0 (F n); V ⊗ M: basis (a, j),
    weight wtV(a) + wt(j), F = F_V ⊗ 1 + 1 ⊗ F_M (F_V b0 = b1, F_V b1 = 0);
    T(2l+1) = Φ(T(l)), T(2l+2) = V ⊗ Φ(T(l)).
  * the TOWER model (C13): ds(0) = [], ds(2l+1) = false :: ds(l), ds(2l+2) = true :: ds(l);
    false: index (q, e), floor 2 fl + e, F(q,0) = (q,1), F(q,1) = 2 (F q, 0);
    true: index (q, j), j ∈ {A,B,C,Dd} = {0,1,2,3}, floors 2fl + (0,1,1,2),
    F A = B + 2C, F B = 2 A(F q), F C = Dd, F Dd = 2 C(F q).
Checks (2-adic Smith forms as multisets of exponents, None = infinite):
  1. (B0b) λ + 1 = 2^{len ds(λ)} + Σ_{t : ds(λ)_t = true} 2^t, λ ≤ 2000.
  2. (B1) ranks agree; the floor of the tower = (λ − weight)/2 as multisets per floor, λ ≤ 40.
  3. (B2) coker(F + 2^{α−1}(λ + 2i − H) on the lattice) ≅ coker(F + 2^α (i + fl) on the tower)
     for λ ≤ 12, α ∈ {1, 2, 3}, i ≤ 4.
  4. (B3) Theorem 3.8: the 2-adic Smith form of the Laplacian of Q_n equals the union over λ ∈ L n
     of those of the lattice operator with α = 1, i = (n − λ)/2, for 1 ≤ n ≤ 8 (one infinite exponent,
     the ℤ_2); also (B4) the multiplicity form (sum over λ ≤ n with m_λ(n) copies).
Controls: (a) ds with false/true swapped fails check 3; (b) i = n − λ instead of (n − λ)/2 fails
check 4; (c) the tower with 2^{α−1} instead of 2^α fails check 3."""
import itertools
from collections import Counter
E = 48
MOD = 1 << E
checks = 0; fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)

def v2(x):
    x %= MOD
    if x == 0: return None
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

def smith2(M):
    """2-adic Smith exponents of a square integer matrix (list of rows), mod 2^E."""
    n = len(M)
    A = [[x % MOD for x in r] for r in M]
    out = []
    rows = list(range(n)); cols = list(range(n))
    R = n
    while True:
        best = None
        for i in rows:
            for j in cols:
                vv = v2(A[i][j])
                if vv is not None and (best is None or vv < best[0]):
                    best = (vv, i, j)
                    if vv == 0: break
            if best is not None and best[0] == 0: break
        if best is None: break
        vv, pi, pj = best
        out.append(vv)
        p = A[pi][pj]
        u = p >> vv
        uinv = pow(u, -1, MOD)
        for i in rows:
            if i == pi: continue
            a = A[i][pj]
            if a == 0: continue
            # a = 2^vv * c with c integral (vv minimal)
            c = ((a >> vv) * uinv) % MOD
            rowp = A[pi]; rowi = A[i]
            for j in cols: rowi[j] = (rowi[j] - c * rowp[j]) % MOD
        rows.remove(pi); cols.remove(pj)
    out += [None] * len(rows)
    return sorted(out, key=lambda x: (x is None, x))

# ---------- lattice model ----------
def lat_T(l):
    """returns (basis list, weight dict, F as dict basis -> {basis: coeff})"""
    if l == 0:
        return [()], {(): 0}, {(): {}}
    if l % 2 == 1:
        B, W, F = lat_T((l - 1) // 2)
        return phi(B, W, F)
    B, W, F = lat_T((l - 2) // 2)
    return tensV(*phi(B, W, F))
def phi(B, W, F):
    nb = [(e, j) for e in (0, 1) for j in B]
    nw = {(e, j): 2 * W[j] + (1 if e == 0 else -1) for (e, j) in nb}
    nf = {}
    for j in B:
        nf[(0, j)] = {(1, j): 1}
        d = {}
        for t, c in F[j].items(): d[(0, t)] = d.get((0, t), 0) + 2 * c
        nf[(1, j)] = d
    return nb, nw, nf
def tensV(B, W, F):
    nb = [(a, j) for a in (0, 1) for j in B]
    nw = {(a, j): (1 if a == 0 else -1) + W[j] for (a, j) in nb}
    nf = {}
    for (a, j) in nb:
        d = {}
        if a == 0: d[(1, j)] = d.get((1, j), 0) + 1
        for t, c in F[j].items(): d[(a, t)] = d.get((a, t), 0) + c
        nf[(a, j)] = d
    return nb, nw, nf

# ---------- tower model ----------
def ds_of(l, swap=False):
    if l == 0: return []
    if l % 2 == 1: return [swap] + ds_of((l - 1) // 2, swap)
    return [not swap] + ds_of((l - 2) // 2, swap)
def tower(ds):
    if not ds:
        return [()], {(): 0}, {(): {}}
    B, FL, F = tower(ds[1:])
    if ds[0] is False:
        nb = [(q, e) for q in B for e in (0, 1)]
        fl = {(q, e): 2 * FL[q] + e for (q, e) in nb}
        nf = {}
        for q in B:
            nf[(q, 0)] = {(q, 1): 1}
            d = {}
            for t, c in F[q].items(): d[(t, 0)] = d.get((t, 0), 0) + 2 * c
            nf[(q, 1)] = d
        return nb, fl, nf
    nb = [(q, j) for q in B for j in range(4)]
    off = [0, 1, 1, 2]
    fl = {(q, j): 2 * FL[q] + off[j] for (q, j) in nb}
    nf = {}
    for q in B:
        nf[(q, 0)] = {(q, 1): 1, (q, 2): 2}
        d = {}
        for t, c in F[q].items(): d[(t, 0)] = d.get((t, 0), 0) + 2 * c
        nf[(q, 1)] = d
        nf[(q, 2)] = {(q, 3): 1}
        d = {}
        for t, c in F[q].items(): d[(t, 2)] = d.get((t, 2), 0) + 2 * c
        nf[(q, 3)] = d
    return nb, fl, nf

def mat(B, F, diag):
    idx = {b: k for k, b in enumerate(B)}
    n = len(B)
    M = [[0] * n for _ in range(n)]
    for b in B:
        col = idx[b]
        for t, c in F[b].items(): M[idx[t]][col] += c
        M[col][col] += diag(b)
    return M

def lat_op(l, alpha, i):
    B, W, F = lat_T(l)
    return mat(B, F, lambda b: 2 ** (alpha - 1) * (l + 2 * i - W[b]))
def tow_op(l, alpha, i, swap=False, half=False):
    B, FL, F = tower(ds_of(l, swap))
    a = 2 ** (alpha - 1) if half else 2 ** alpha
    return mat(B, F, lambda b: a * (i + FL[b]))

# 1. digits
for l in range(2001):
    d = ds_of(l)
    ok(l + 1 == 2 ** len(d) + sum(2 ** t for t, x in enumerate(d) if x), ("digits", l))
# 2. ranks and floors
for l in range(41):
    B, W, _ = lat_T(l); Bt, FL, _ = tower(ds_of(l))
    ok(len(B) == len(Bt), ("rank", l))
    ok(all((l - W[b]) % 2 == 0 and l - W[b] >= 0 for b in B), ("parity", l))
    ok(Counter((l - W[b]) // 2 for b in B) == Counter(FL.values()), ("floors", l))
# 3. coker iso
S3 = {}
for l in range(13):
    for alpha in (1, 2, 3):
        for i in range(5):
            s1 = smith2(lat_op(l, alpha, i)); s2 = smith2(tow_op(l, alpha, i))
            S3[(l, alpha, i)] = s1
            ok(s1 == s2, ("coker", l, alpha, i))
# 4. Theorem 3.8
def lap(n):
    N = 1 << n
    M = [[0] * N for _ in range(N)]
    for g in range(N):
        M[g][g] = n
        for t in range(n): M[g][g ^ (1 << t)] -= 1
    return M
def Lst(n):
    L = [0]
    for _ in range(n):
        L = [x for lam in L for x in tdot(lam)]
    return L
def tdot(l):
    if l == 0: return [1]
    if l % 2 == 1: return [l + 1]
    m = (l - 2) // 2
    return [l - 1, l - 1] + [2 * x + 1 for x in tdot(m)]
LAP = {}
for n in range(1, 9):
    LAP[n] = smith2(lap(n))
    fam = []
    for lam in Lst(n): fam += smith2(lat_op(lam, 1, (n - lam) // 2))
    ok(LAP[n] == sorted(fam, key=lambda x: (x is None, x)), ("thm38", n))
    ok(LAP[n].count(None) == 1, ("one Z2", n))
    cnt = Counter(Lst(n)); fam2 = []
    for lam in range(n + 1):
        for _ in range(cnt[lam]): fam2 += smith2(lat_op(lam, 1, (n - lam) // 2))
    ok(sorted(fam2, key=lambda x: (x is None, x)) == LAP[n], ("thm38 mult", n))
print("checks", checks, "fails", fails)

# controls (each must fire)
fired = 0
if any(smith2(lat_op(l, 1, i)) != smith2(tow_op(l, 1, i, swap=True)) for l in range(2, 9) for i in range(3)): fired += 1
bad = False
for n in range(2, 8):
    fam = []
    for lam in Lst(n): fam += smith2(lat_op(lam, 1, n - lam))
    if sorted(fam, key=lambda x: (x is None, x)) != LAP[n]: bad = True
if bad: fired += 1
if any(smith2(lat_op(l, 2, i)) != smith2(tow_op(l, 2, i, half=True)) for l in range(1, 9) for i in range(3)): fired += 1
print("controls fired", fired, "of 3")
