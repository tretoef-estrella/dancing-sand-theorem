#!/usr/bin/env python3
"""Brute force for piece C28 (lifting modulo 2 and Corollary 3.4). Grepy Escribano, 8 Oct 2026.
Over Z localized at 2 (exact fractions with odd denominators) and over F_2.
  1. (L2) surjectivity: for Δ-filtered M and ∇-filtered N, dim_F2 of weight-preserving morphisms
     M/2 → N/2 equals dim_Q of weight-preserving morphisms M → N.
  2. (L2) the procedure: for every basis morphism h̄ modulo 2, φ0 = h̄ (0/1 entries), d φ0 has even
     entries; δ = d φ0 / 2 satisfies the cocycle equations of C27 (G2); d ψ = δ has a 2-integral
     weight-preserving solution ψ; h = φ0 − 2ψ commutes with every F^(r), E^(r) and h ≡ h̄ mod 2.
  3. (C1) 1 + 2W has odd determinant (unit of Z_(2)) for random integer W.
  4. (C3) on X = Y ∈ {V⊗V, V⊗V⊗V}: random weight-preserving automorphisms modulo 2 lift to
     morphisms with odd determinant.
Controls: Hom(Δ0, Δ2) is 0 over Q and nonzero mod 2 (the lift fails without filtrations); a matrix
≡ 1 mod 3 with even determinant. A search for a non-weight-preserving morphism modulo 2 is reported
(it is expected to find none: Kostant's theorem; it is not a control that can fire)."""
import os, sys, random
from fractions import Fraction as Fr
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "chkC25.py")).read()
head = src[:src.index("RM = 7")]
_keep_stdout = sys.stdout; sys.stdout = open(os.devnull, "w")
exec(head)
sys.stdout = _keep_stdout
src27 = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "chkC27.py")).read()
exec(src27[src27.index("def fnorm"):src27.index("def d_vectors")])
gch = c18.gchoose
random.seed(20261008 + 28)
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

RM = 6
weyl = lambda l: dense(c18.weyl(l), RM)
dweyl = lambda l: dense(c18.dweyl(l), RM)
tV = lambda L: dense(c18.tensorV(L), RM)

def v2(x):
    x = Fr(x)
    if x == 0: return 10 ** 9
    n, d, v = x.numerator, x.denominator, 0
    while n % 2 == 0: n //= 2; v += 1
    while d % 2 == 0: d //= 2; v -= 1
    return v
def mod2(x):
    x = Fr(x); assert v2(x) >= 0
    return (x.numerator * pow(x.denominator, -1, 2)) % 2

def unknowns(M, N, wp=True):
    return [(j, i) for j in range(len(N['wt'])) for i in range(len(M['wt'])) if (not wp) or M['wt'][i] == N['wt'][j]]
def tomat(M, N, unk, x):
    P = zeros(len(N['wt']), len(M['wt']))
    for (j, i), v in zip(unk, x): P[j][i] = v
    return P
def dmap(M, N, P):
    return {op: [add(mul(P, M[op][r]), mul(N[op][r], P), -1) for r in range(RM + 1)] for op in 'FE'}
def comm_rows(M, N, unk):
    """rows of the linear map x ↦ (d x) (all operators, all entries)"""
    cols = []
    for k in range(len(unk)):
        x = [0] * len(unk); x[k] = 1
        D = dmap(M, N, tomat(M, N, unk, x))
        cols.append([a for op in 'FE' for r in range(RM + 1) for row in D[op][r] for a in row])
    return [list(r) for r in zip(*cols)] if cols else []
def nullspace_mod2(rows, n):
    R = [[a % 2 for a in r] for r in rows]; piv = []; r0 = 0
    for c in range(n):
        p = next((i for i in range(r0, len(R)) if R[i][c]), None)
        if p is None: continue
        R[r0], R[p] = R[p], R[r0]
        for i in range(len(R)):
            if i != r0 and R[i][c]: R[i] = [(a + b) % 2 for a, b in zip(R[i], R[r0])]
        piv.append(c); r0 += 1
    free = [c for c in range(n) if c not in piv]; out = []
    for f in free:
        x = [0] * n; x[f] = 1
        for k, c in enumerate(piv): x[c] = R[k][f] % 2
        out.append(x)
    return out
def solve_2adic(rows, b, n):
    """solve rows · y = b with y in Z_(2) (full pivoting by least 2-valuation); None if impossible"""
    A = [[Fr(a) for a in r] + [Fr(bb)] for r, bb in zip(rows, b)]
    m = len(A); colperm = list(range(n)); T = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    piv = []; r0 = 0
    while r0 < m and r0 < n:
        best = None
        for i in range(r0, m):
            for c in range(r0, n):
                if A[i][c] != 0 and (best is None or v2(A[i][c]) < best[0]): best = (v2(A[i][c]), i, c)
        if best is None: break
        _, i, c = best
        A[r0], A[i] = A[i], A[r0]
        for row in A: row[r0], row[c] = row[c], row[r0]
        for row in T: row[r0], row[c] = row[c], row[r0]
        p = A[r0][r0]
        for i in range(m):
            if i != r0 and A[i][r0] != 0:
                f = A[i][r0] / p; A[i] = [a - f * bb for a, bb in zip(A[i], A[r0])]
        for c2 in range(r0 + 1, n):   # column operations (unimodular over Z_(2): p divides the entry)
            if A[r0][c2] != 0:
                f = A[r0][c2] / p
                for row in A: row[c2] -= f * row[r0]
                for row in T: row[c2] -= f * row[r0]
        piv.append(p); r0 += 1
    for i in range(r0, m):
        if A[i][n] != 0: return None
    y = [Fr(0)] * n
    for k in range(r0):
        y[k] = A[k][n] / A[k][k]
        if v2(y[k]) < 0: return None
    return [sum(T[i][k] * y[k] for k in range(n)) for i in range(n)]

def lift_check(M, N, mn, nn, expect=True):
    unkw = unknowns(M, N); rows = comm_rows(M, N, unkw)
    dQ = len(unkw) - (rank(rows, 0) if rows else 0)
    basis2 = nullspace_mod2(rows, len(unkw)) if unkw else []
    d2 = len(basis2)
    if expect: ok(dQ == d2, f"L2 surjective {mn},{nn}: dim_Q {dQ} vs dim_F2 {d2}")
    allgood = True
    for hb in basis2:
        P0 = tomat(M, N, unkw, hb); D = dmap(M, N, P0)
        even = all(a % 2 == 0 for op in 'FE' for r in range(RM + 1) for row in D[op][r] for a in row)
        if expect: ok(even, f"L2 d φ0 even {mn},{nn}")
        if not even: allgood = False; continue
        delta = {op: [scal(Fr(1, 2), D[op][r]) for r in range(RM + 1)] for op in 'FE'}
        # δ satisfies the cocycle equations (G2) of C27: evaluate the rows on δ
        U = Unk(M, N); x = [0] * U.n; inW = True
        for op in 'FE':
            for r in range(RM + 1):
                for j in range(len(N['wt'])):
                    for i in range(len(M['wt'])):
                        if delta[op][r][j][i]:
                            k = U.idx.get((op, r, j, i))
                            if k is None: inW = False
                            else: x[k] = delta[op][r][j][i]
        crows = cocycle_rows(U)
        if expect:
            ok(inW, f"L2 δ satisfies (W) {mn},{nn}")
            ok(all(sum(a * c for a, c in zip(rr, x)) == 0 for rr in crows), f"L2 δ cocycle {mn},{nn}")
        bvec = [a for op in 'FE' for r in range(RM + 1) for row in delta[op][r] for a in row]
        y = solve_2adic(rows, bvec, len(unkw))
        if expect: ok(y is not None, f"L2 dψ = δ solvable 2-adically {mn},{nn}")
        if y is None: allgood = False; continue
        Psi = tomat(M, N, unkw, y); Hh = add(P0, Psi, -2)
        Dh = dmap(M, N, Hh)
        good = all(a == 0 for op in 'FE' for r in range(RM + 1) for row in Dh[op][r] for a in row)
        red = all(mod2(Hh[j][i]) == P0[j][i] % 2 for j in range(len(N['wt'])) for i in range(len(M['wt'])))
        if expect:
            ok(good, f"L2 h commutes {mn},{nn}"); ok(red, f"L2 h ≡ h̄ mod 2 {mn},{nn}")
        allgood = allgood and good and red
    return dQ, d2, allgood

Dlist = [("Δ0", weyl(0)), ("Δ1", weyl(1)), ("Δ2", weyl(2)), ("Δ3", weyl(3)), ("V⊗Δ1", tV(c18.weyl(1))), ("V⊗Δ2", tV(c18.weyl(2))), ("V⊗V", tV(c18.V)), ("V⊗V⊗V", tV(c18.tensorV(c18.V)))]
Nlist = [("∇0", dweyl(0)), ("∇1", dweyl(1)), ("∇2", dweyl(2)), ("∇3", dweyl(3)), ("V⊗∇1", tV(c18.dweyl(1))), ("V⊗∇2", tV(c18.dweyl(2))), ("V⊗V", tV(c18.V)), ("V⊗V⊗V", tV(c18.tensorV(c18.V)))]
tot2 = 0
for (mn, M) in Dlist:
    for (nn, N) in Nlist:
        dQ, d2, _ = lift_check(M, N, mn, nn); tot2 += d2
print(f"(lifts tested: {tot2} basis morphisms modulo 2)")

# 3 (C1)
def det(Mx):
    A = [[Fr(a) for a in r] for r in Mx]; n = len(A); dt = Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: A[c], A[p] = A[p], A[c]; dt = -dt
        dt *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]; A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    return dt
for _ in range(200):
    n = random.randint(1, 6); W = [[random.randint(-9, 9) for _ in range(n)] for _ in range(n)]
    ok(v2(det(add(ident(n), scal(2, W)))) == 0, "C1 det(1 + 2W) odd")

# 4 (C3) on X = Y
for (xn, X) in [("V⊗V", tV(c18.V)), ("V⊗V⊗V", tV(c18.tensorV(c18.V)))]:
    unkw = unknowns(X, X); rows = comm_rows(X, X, unkw); basis2 = nullspace_mod2(rows, len(unkw))
    tried = 0
    while tried < 15:
        coef = [random.randint(0, 1) for _ in basis2]
        hb = [sum(c * b[k] for c, b in zip(coef, basis2)) % 2 for k in range(len(unkw))]
        P0 = tomat(X, X, unkw, hb)
        if det(P0).numerator % 2 == 0: continue   # not an automorphism modulo 2
        tried += 1
        D = dmap(X, X, P0)
        delta = [a / 2 for op in 'FE' for r in range(RM + 1) for row in D[op][r] for a in map(Fr, row)]
        y = solve_2adic(rows, delta, len(unkw))
        ok(y is not None, f"C3 lift exists {xn}")
        if y is None: continue
        Hh = add(P0, tomat(X, X, unkw, y), -2)
        ok(v2(det(Hh)) == 0, f"C3 lifted automorphism has odd determinant {xn}")
print(f"chkC28: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
dQ, d2, good = lift_check(weyl(0), weyl(2), "Δ0", "Δ2", expect=False)
control(f"Hom(Δ0, Δ2): dim_Q {dQ} < dim_F2 {d2}, and the procedure fails", dQ < d2 and not good)
found = None
for (mn, M) in Dlist + Nlist:
    for (nn, N) in Dlist + Nlist:
        ua = [(j, i) for (j, i) in unknowns(M, N, wp=False) if (M['wt'][i] - N['wt'][j]) % 2 == 0]
        uw = unknowns(M, N)
        if len(nullspace_mod2(comm_rows(M, N, ua), len(ua))) > len(nullspace_mod2(comm_rows(M, N, uw), len(uw))):
            found = (mn, nn); break
    if found: break
control(f"a non-weight-preserving morphism modulo 2 exists ({found})", found is not None)
control("a matrix ≡ 1 mod 3 with even determinant ([[1,3],[3,1]], det −8)", v2(det([[1, 3], [3, 1]])) > 0)
print(f"controls: {fires}/{ctrl} fire")
