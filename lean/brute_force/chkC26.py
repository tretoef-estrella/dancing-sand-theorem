#!/usr/bin/env python3
"""Brute force for piece C26 (Lemma 3.3 for one pair in the lifting and extension forms).
Grepy Escribano, 8 Oct 2026. Every test is run over Q and modulo p = 2, 3, 5 (the statements
claim every commutative ring); matrices M[j][i] = coefficient of e_j in the image of e_i.
  1. (L1) on the NON-split sequences V⊗∇(m−1) → V⊗V⊗∇(m) → V⊗∇(m+1) (id_V ⊗ the C19 maps),
     l = m (kernel weights in [−m, m]); every h : Δ(m) → Z in a basis of Hom; the recipe
     x = weight-l preimage of h(δ_0), h' = sW x: morphism, g h' = h, E^{(s)}x = 0, F^{(r)}x = 0.
  2. (X1) on Y = Δ(m+1) ⊕ K0 → X = (V⊗Δ(m)) ⊕ K0 → Δ(m−1) (the C19 Δ-sequence, non-split
     modulo 2, plus a summand K0 with weights in [−l, l]), X rewritten in a random weight basis;
     k = random combination of Homs Y → K; recipe k' = k ∘ ρ with f ρ = id − sW x ∘ g:
     morphism, k' f = k.
  3. (B1) m > l and (B2) m > l by the dual routes, on split sums in a random weight basis
     (the recipes go through X1 / L1 on the duals): morphisms, g h' = h, k' f = k.
  4. (B5): B1 with h = id, B2 with k = id.
Controls must fail (reported as FIRES)."""
import os, sys, random
from fractions import Fraction as Fr
from math import comb
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "chkC25.py")).read()
head = src[:src.index("RM = 7")]
_keep_stdout = sys.stdout; sys.stdout = open(os.devnull, "w")
exec(head)          # helpers of chkC25: dense, dual, is_dp, is_hom, dsum, rand_wt_basis, conj, sW, ...
sys.stdout = _keep_stdout
random.seed(20261008 + 26)
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

RM = 7
weyl = lambda l: dense(c18.weyl(l), RM)
dweyl = lambda l: dense(c18.dweyl(l), RM)
tV = lambda L: dense(c18.tensorV(L), RM)

# ---- arithmetic in a field: p = 0 means Q ----
def red(A, p):
    if p == 0: return [[Fr(x) for x in r] for r in A]
    return [[x % p for x in r] for r in A]
def finv(a, p): return 1 / a if p == 0 else pow(a, p - 2, p)
def fnorm(x, p): return x if p == 0 else x % p
def mulp(A, B, p):
    return [[fnorm(x, p) for x in r] for r in mul(A, B)]
def redD(D, p): return {'wt': D['wt'], 'F': [red(m, p) for m in D['F']], 'E': [red(m, p) for m in D['E']]}
def is_hom_p(S, X, Y, p):
    bad = 0
    for i in range(len(X['wt'])):
        for j in range(len(Y['wt'])):
            if fnorm(S[j][i], p) and X['wt'][i] != Y['wt'][j]: bad += 1
    for r in range(min(len(X['F']), len(Y['F']))):
        for op in 'FE':
            bad += mulp(S, X[op][r], p) != mulp(Y[op][r], S, p)
    return bad
def rref(M, p):
    M = [r[:] for r in M]; piv = []; r = 0
    for c in range(len(M[0]) if M else 0):
        k = next((i for i in range(r, len(M)) if fnorm(M[i][c], p)), None)
        if k is None: continue
        M[r], M[k] = M[k], M[r]; t = finv(M[r][c], p); M[r] = [fnorm(x * t, p) for x in M[r]]
        for i in range(len(M)):
            if i != r and fnorm(M[i][c], p):
                t = M[i][c]; M[i] = [fnorm(a - t * b, p) for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    return M, piv
def solve(A, b, p, cols=None):
    """a solution x of A x = b supported on cols (default all), or None"""
    n = len(A[0]); cols = list(range(n)) if cols is None else cols
    M = [[A[j][c] for c in cols] + [b[j]] for j in range(len(A))]
    R, piv = rref(M, p)
    if len(cols) in piv: return None
    x = [fnorm(0, p)] * n
    for k, c in enumerate(piv): x[cols[c]] = R[k][-1]
    return x
def nullspace(A, p):
    n = len(A[0]); R, piv = rref(A, p); out = []
    for f in range(n):
        if f in piv: continue
        v = [fnorm(0, p)] * n; v[f] = fnorm(1, p)
        for k, c in enumerate(piv): v[c] = fnorm(-R[k][f], p)
        out.append(v)
    return out
def hom_basis_from_delta(l, Z, p):
    """basis of the vectors z of weight l with E^{(s)} z = 0 (s >= 1), F^{(r)} z = 0 (r > l);
    each gives h = sW z : Δ(l) -> Z"""
    n = len(Z['wt']); idx = [k for k in range(n) if Z['wt'][k] == l]
    if not idx: return []
    rows = []
    for s in range(1, RM + 1): rows += [[Z['E'][s][j][k] for k in idx] for j in range(n)]
    for r in range(l + 1, RM + 1): rows += [[Z['F'][r][j][k] for k in idx] for j in range(n)]
    out = []
    for v in nullspace(rows, p):
        z = [fnorm(0, p)] * n
        for k, c in zip(idx, v): z[k] = c
        out.append(z)
    return out
def sWp(X, x, l, p): return [[fnorm(v, p) for v in r] for r in sW(X, x, l)]
def blockV(Fm):  # id_V ⊗ f for the index layout e * n + i
    a, b = len(Fm), len(Fm[0])
    M = zeros(2 * a, 2 * b)
    for e in range(2):
        for j in range(a):
            for i in range(b): M[e * a + j][e * b + i] = Fm[j][i]
    return M
PRIMES = [0, 2, 3, 5]

# ---- recipes ----
def lift_L1(f, g, X, Z, h, l, p):
    """L1 recipe: x of weight l with g x = h(δ_0); returns (h', x)"""
    z = [h[j][0] for j in range(len(h))]
    idx = [k for k in range(len(X['wt'])) if X['wt'][k] == l]
    x = solve(g, z, p, idx)
    return (None, None) if x is None else (sWp(X, x, l, p), x)
def extend_X1(f, g, X, k, l, p):
    """X1 recipe: x of weight l with g x = δ_0, ρ with f ρ = id − sW x g, k' = k ρ"""
    n = len(X['wt']); idx = [i for i in range(n) if X['wt'][i] == l]
    x = solve(g, [fnorm(1, p)] + [fnorm(0, p)] * l, p, idx)
    S = sWp(X, x, l, p); I = red(ident(n), p)
    Pm = [[fnorm(a - b, p) for a, b in zip(ra, rb)] for ra, rb in zip(I, mulp(S, g, p))]
    rho = []
    for c in range(n):
        y = solve(f, [Pm[j][c] for j in range(n)], p)
        rho.append(y)
    rho = [list(r) for r in zip(*rho)]
    return mulp(k, rho, p), rho

# 1. (L1) on V ⊗ (C19 ∇-sequence)
for m in range(1, 5):
    _, _, fN, gN = c19.maps(m)
    Ff = [[fN(i).get(j, 0) for i in range(m)] for j in range(2 * (m + 1))]
    Gg = [[gN(i).get(j, 0) for i in range(2 * (m + 1))] for j in range(m + 2)]
    N0, X0, Z0 = tV(c18.dweyl(m - 1)), tV(c18.tensorV(c18.dweyl(m))), tV(c18.dweyl(m + 1))
    f0, g0 = blockV(Ff), blockV(Gg)
    ok(is_hom(f0, N0, X0) == 0 and is_hom(g0, X0, Z0) == 0, f"L1 input m={m}")
    for p in PRIMES:
        N, X, Z, f, g = redD(N0, p), redD(X0, p), redD(Z0, p), red(f0, p), red(g0, p)
        hs = hom_basis_from_delta(m, Z, p)
        ok(len(hs) >= 1, f"L1 nonzero Hom Δ({m}) -> Z p={p}")
        nz = len(Z['wt'])
        combos = []
        for _ in range(2):
            cs = [random.randint(-3, 3) for _ in hs]
            combos.append([fnorm(sum(c * hh[i] for c, hh in zip(cs, hs)), p) for i in range(nz)])
        for z in hs + combos:
            h = sWp(Z, z, m, p)
            ok(is_hom_p(h, redD(weyl(m), p), Z, p) == 0, f"L1 h hom m={m} p={p}")
            hp, x = lift_L1(f, g, X, Z, h, m, p)
            ok(hp is not None, f"L1 preimage m={m} p={p}")
            if hp is None: continue
            ok(all(fnorm(v, p) == 0 for s in range(1, RM + 1) for v in matvec(X['E'][s], x)), f"L1 E x = 0 m={m} p={p}")
            ok(all(fnorm(v, p) == 0 for r in range(m + 1, RM + 1) for v in matvec(X['F'][r], x)), f"L1 F x = 0 m={m} p={p}")
            ok(is_hom_p(hp, redD(weyl(m), p), X, p) == 0, f"L1 h' hom m={m} p={p}")
            ok(mulp(g, hp, p) == h, f"L1 g h' = h m={m} p={p}")

# 2. (X1) on (C19 Δ-sequence) ⊕ K0, random weight basis
def X1_setup(m, K0):
    fD, gD, _, _ = c19.maps(m)
    nY = 2 * (m + 1)
    F1 = [[fD(i).get(j, 0) for i in range(m + 2)] for j in range(nY)]
    G1 = [[gD(i).get(j, 0) for i in range(nY)] for j in range(m)]
    Y0, X0 = dsum(weyl(m + 1), K0), dsum(tV(c18.weyl(m)), K0)
    nk = len(K0['wt']); ny, nx = m + 2 + nk, nY + nk
    f0 = zeros(nx, ny); g0 = zeros(m, nx)
    for j in range(nY):
        for i in range(m + 2): f0[j][i] = F1[j][i]
    for t in range(nk): f0[nY + t][m + 2 + t] = 1
    for j in range(m):
        for i in range(nY): g0[j][i] = G1[j][i]
    P, Pi = rand_wt_basis(X0['wt'])
    return Y0, conj(X0, P, Pi), mul(P, f0), mul(g0, Pi), nk
for m in range(2, 6):
    l = m - 1
    for K0 in [dweyl(l), weyl(l), dweyl(max(l - 1, 0)), tV(c18.dweyl(l - 1)), dsum(weyl(l), dweyl(l))]:
        Y0, X0, f0, g0, nk = X1_setup(m, K0)
        ok(is_hom(f0, Y0, X0) == 0 and is_hom(g0, X0, weyl(l)) == 0, f"X1 input m={m}")
        for p in PRIMES:
            Y, X, f, g = redD(Y0, p), redD(X0, p), red(f0, p), red(g0, p)
            K = redD(K0, p); ny = len(Y['wt'])
            # Homs Y -> K: the projection to K0 times a random scalar, plus (if any) Homs Δ(m+1) -> K (none by weights)
            c = random.randint(1, 4)
            k = [[fnorm(c if (i == ny - nk + j) else 0, p) for i in range(ny)] for j in range(nk)]
            ok(is_hom_p(k, Y, K, p) == 0, f"X1 k hom m={m} p={p}")
            kp, rho = extend_X1(f, g, X, k, l, p)
            ok(mulp(rho, f, p) == red(ident(ny), p), f"X1 ρ f = id m={m} p={p}")
            ok(is_hom_p(kp, X, K, p) == 0, f"X1 k' hom m={m} p={p}")
            ok(mulp(kp, f, p) == k, f"X1 k' f = k m={m} p={p}")

# 3. (B1) and (B2) for m > l by the dual routes; 4. (B5)
def B1_dual(m, l, Zextra, p):
    """kernel ∇(m), m > l; X = ∇(m) ⊕ Z0 with Z0 = Δ(l) ⊕ Zextra, random weight basis; h = inclusion of Δ(l)"""
    Z0 = dsum(weyl(l), Zextra); Nb = dweyl(m); X0 = dsum(Nb, Z0)
    n = len(X0['wt']); nN = m + 1; nZ = len(Z0['wt'])
    P, Pi = rand_wt_basis(X0['wt']); Xc = conj(X0, P, Pi)
    f0 = mul(P, [[1 if i == j else 0 for i in range(nN)] for j in range(n)])
    g0 = mul([[1 if i == nN + j else 0 for i in range(n)] for j in range(nZ)], Pi)
    h0 = [[1 if i == j else 0 for i in range(l + 1)] for j in range(nZ)]
    X, Z, f, g, h = redD(Xc, p), redD(Z0, p), red(f0, p), red(g0, p), red(h0, p)
    ok(is_hom_p(h, redD(weyl(l), p), Z, p) == 0, f"B1 h hom m={m} l={l} p={p}")
    # dual sequence dual Z -> dual X -> Δ(m) (D4: dual ∇(m) = Δ(m) with the identity), k = trM h : dual Z -> ∇(l)
    Xs, Zs = dual(X), dual(Z)
    k = tr(h)
    kp, _ = extend_X1(tr(g), tr(f), Xs, k, m, p)   # X1 with cokernel Δ(m), K = ∇(l) (weights in [-l, l] ⊆ [-m, m])
    ok(is_hom_p(kp, Xs, redD(dweyl(l), p), p) == 0, f"B1 k' hom m={m} l={l} p={p}")
    hp = tr(kp)
    ok(is_hom_p(hp, redD(weyl(l), p), X, p) == 0, f"B1 h' hom m={m} l={l} p={p}")
    ok(mulp(g, hp, p) == h, f"B1 g h' = h m={m} l={l} p={p}")
def B2_dual(m, l, Yextra, p):
    """cokernel Δ(l), m > l; X = Y0 ⊕ Δ(l) with Y0 = ∇(m) ⊕ Yextra, random weight basis; k = projection to ∇(m)"""
    Y0 = dsum(dweyl(m), Yextra); X0 = dsum(Y0, weyl(l))
    n = len(X0['wt']); nY = len(Y0['wt'])
    P, Pi = rand_wt_basis(X0['wt']); Xc = conj(X0, P, Pi)
    f0 = mul(P, [[1 if i == j else 0 for i in range(nY)] for j in range(n)])
    g0 = mul([[1 if i == nY + j else 0 for i in range(n)] for j in range(l + 1)], Pi)
    k0 = [[1 if i == j else 0 for i in range(nY)] for j in range(m + 1)]
    X, Y, f, g, k = redD(Xc, p), redD(Y0, p), red(f0, p), red(g0, p), red(k0, p)
    ok(is_hom_p(k, Y, redD(dweyl(m), p), p) == 0, f"B2 k hom m={m} l={l} p={p}")
    Xs = dual(X)
    # dual sequence ∇(l) -> dual X -> dual Y, h = trM k : Δ(m) -> dual Y, lift by L1 (kernel weights in [-l, l] ⊆ [-m, m])
    hp, _ = lift_L1(tr(g), tr(f), Xs, dual(Y), tr(k), m, p)
    ok(hp is not None and is_hom_p(hp, redD(weyl(m), p), Xs, p) == 0, f"B2 h' hom m={m} l={l} p={p}")
    kp = tr(hp)
    ok(is_hom_p(kp, X, redD(dweyl(m), p), p) == 0, f"B2 k' hom m={m} l={l} p={p}")
    ok(mulp(kp, f, p) == k, f"B2 k' f = k m={m} l={l} p={p}")
for m in range(1, 6):
    for l in range(0, m):
        for extra in [weyl(0), dweyl(l), tV(c18.weyl(max(l - 1, 0)))]:
            for p in PRIMES:
                B1_dual(m, l, extra, p); B2_dual(m, l, extra, p)
print(f"chkC26: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
# C1: X1 recipe with K of too large weights: Δ(3) -> V⊗Δ(2) -> Δ(1), K = ∇(3), k = the nonzero Hom Δ(3) -> ∇(3)
fD, gD, _, _ = c19.maps(2)
F1 = [[fD(i).get(j, 0) for i in range(4)] for j in range(6)]; G1 = [[gD(i).get(j, 0) for i in range(6)] for j in range(2)]
Xv = tV(c18.weyl(2)); zz = hom_basis_from_delta(3, dweyl(3), 0)
kk = sWp(dweyl(3), zz[0], 3, 0)
kp, _ = extend_X1(red(F1, 0), red(G1, 0), redD(Xv, 0), kk, 1, 0)
control("X1 recipe with K weights beyond [-l, l]", is_hom_p(kp, redD(Xv, 0), redD(dweyl(3), 0), 0) > 0)
# C2: L1 recipe with kernel weights beyond [-l, l]: lift id of Δ(1) through V⊗Δ(2) -> Δ(1) (kernel Δ(3))
hp, x = lift_L1(red(F1, 0), red(G1, 0), redD(Xv, 0), redD(weyl(1), 0), red(ident(2), 0), 1, 0)
control("L1 recipe with kernel weights beyond [-l, l]", hp is None or is_hom_p(hp, redD(weyl(1), 0), redD(Xv, 0), 0) > 0)
# C3: Ext^1(Δ(0), Δ(2)) ≠ 0 modulo 2: no section of V⊗V -> Δ(0) at all modulo 2 (Hom space solved, not the recipe)
fD, gD, _, _ = c19.maps(1)
G = [[gD(i).get(j, 0) for i in range(4)] for j in range(1)]; VV = tV(c18.weyl(1))
def has_section(p):
    zs = hom_basis_from_delta(0, redD(VV, p), p)      # all Homs Δ(0) -> V⊗V
    vals = [mulp(red(G, p), sWp(redD(VV, p), z, 0, p), p)[0][0] for z in zs]
    return any(fnorm(v, p) for v in vals)
control("no section of Δ(2) -> V⊗V -> Δ(0) modulo 2", not has_section(2))
control("(sanity, must hold) a section exists modulo 3", has_section(3))
# C4: X1 recipe with x not of weight l (add a vector of another weight): k' f = k or Hom fails
Y0, X0, f0, g0, nk = X1_setup(3, dweyl(2))
n = len(X0['wt']); idx = [i for i in range(n) if X0['wt'][i] == 2]
x = solve(red(g0, 0), [Fr(1), Fr(0), Fr(0)], 0, idx)
other = next(i for i in range(n) if X0['wt'][i] == 0); x[other] += 1
S = sWp(redD(X0, 0), x, 2, 0)
control("sW of an x not of weight l is not a section", mulp(red(g0, 0), S, 0) != red(ident(3), 0) or is_hom_p(S, redD(weyl(2), 0), redD(X0, 0), 0) > 0)
print(f"controls: {fires}/{ctrl} fire")
