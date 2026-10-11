#!/usr/bin/env python3
"""Brute force for piece C25 (Lemma 3.2 = Lemma W; Lemma 3.3 for one pair Δ(l), ∇(m); the
contravariant dual). Grepy Escribano, 8 Oct 2026. Exact integers and rationals, dense matrices.
  1. (D1) dual X satisfies (W), (P0), (P1), (K) for several X; (D3) dual(dual X) = X.
  2. (D4) dual Δ(l) = ∇(l) and dual ∇(l) = Δ(l) entrywise, l <= 10.
  3. (D2) transposes of the explicit morphisms of C19 are morphisms between the duals;
     (D5) the transposed sequences of C19 are short exact (ranks mod several primes).
  4. (W) the construction s(e_r) = F^{(r)} x on X = Δ(l) ⊕ N rewritten in a random weight basis
     (N with weights in [-l, l]): s is a morphism, weight-preserving, g s = id.
  5. (E2) on X = ∇(m) ⊕ Δ(l) in a random weight basis: m <= l by W directly; m > l by the dual
     route (W on the dual sequence, transpose back to a retraction r, section s = (1 - f r) σ
     with a random linear section σ): r f = id, g s = id, r and s morphisms.
Controls must fail (reported as FIRES)."""
import importlib.util, sys, os, random
from fractions import Fraction as Fr
from math import comb
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
spec = importlib.util.spec_from_file_location("c18", os.path.join(os.path.dirname(os.path.abspath(__file__)), "chkC18.py"))
c18 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c18)
spec = importlib.util.spec_from_file_location("c19", os.path.join(os.path.dirname(os.path.abspath(__file__)), "chkC19.py"))
c19 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c19)
sys.stdout = _out
gchoose = c18.gchoose
random.seed(20261008)
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

# ---- dense matrices: M[j][i] = coefficient of e_j in the image of e_i ----
def zeros(a, b): return [[0] * b for _ in range(a)]
def ident(n): return [[1 if i == j else 0 for i in range(n)] for j in range(n)]
def mul(A, B):
    n, k, m = len(A), len(B), len(B[0]) if B else 0
    return [[sum(A[i][t] * B[t][j] for t in range(k) if A[i][t]) for j in range(m)] for i in range(n)]
def tr(A): return [list(r) for r in zip(*A)] if A else []
def add(A, B, c=1): return [[a + c * b for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]
def scal(c, A): return [[c * a for a in r] for r in A]
def matvec(A, v): return [sum(a * x for a, x in zip(r, v)) for r in A]

def dense(L, RM):
    n = len(L['wt'])
    def mat(op, r):
        M = zeros(n, n)
        for i in range(n):
            for j, x in L[op](r, i).items(): M[j][i] = x
        return M
    return {'wt': list(L['wt']), 'F': [mat('F', r) for r in range(RM + 1)], 'E': [mat('E', r) for r in range(RM + 1)]}

def dual(D, swap=True):
    if swap: return {'wt': D['wt'], 'F': [tr(m) for m in D['E']], 'E': [tr(m) for m in D['F']]}
    return {'wt': D['wt'], 'F': [tr(m) for m in D['F']], 'E': [tr(m) for m in D['E']]}

def is_dp(D):
    bad = 0; n = len(D['wt']); RM = len(D['F']) - 1
    for i in range(n):
        w = D['wt'][i]
        for r in range(RM + 1):
            for j in range(n):
                if D['F'][r][j][i] and D['wt'][j] != w - 2 * r: bad += 1
                if D['E'][r][j][i] and D['wt'][j] != w + 2 * r: bad += 1
    bad += D['F'][0] != ident(n); bad += D['E'][0] != ident(n)
    for a in range(RM + 1):
        for b in range(RM + 1 - a):
            for op in 'FE':
                bad += mul(D[op][a], D[op][b]) != scal(comb(a + b, a), D[op][a + b])
    for i in range(n):
        w = D['wt'][i]; ei = [1 if k == i else 0 for k in range(n)]
        for r in range(RM + 1):
            for s in range(RM + 1):
                lhs = matvec(D['E'][s], matvec(D['F'][r], ei))
                rhs = [0] * n
                for j in range(min(r, s) + 1):
                    v = matvec(D['F'][r - j], matvec(D['E'][s - j], ei))
                    c = gchoose(w + s - r, j)
                    rhs = [x + c * y for x, y in zip(rhs, v)]
                bad += lhs != rhs
    return bad

def is_hom(S, X, Y):  # S : X -> Y, matrix len(Y) x len(X)
    bad = 0; RM = min(len(X['F']), len(Y['F'])) - 1
    for i in range(len(X['wt'])):
        for j in range(len(Y['wt'])):
            if S[j][i] and X['wt'][i] != Y['wt'][j]: bad += 1
    for r in range(RM + 1):
        for op in 'FE':
            bad += mul(S, X[op][r]) != mul(Y[op][r], S)
    return bad

def dsum(D1, D2):
    n1, n2 = len(D1['wt']), len(D2['wt'])
    def blk(A, B):
        M = zeros(n1 + n2, n1 + n2)
        for j in range(n1):
            for i in range(n1): M[j][i] = A[j][i]
        for j in range(n2):
            for i in range(n2): M[n1 + j][n1 + i] = B[j][i]
        return M
    RM = min(len(D1['F']), len(D2['F'])) - 1
    return {'wt': D1['wt'] + D2['wt'], 'F': [blk(D1['F'][r], D2['F'][r]) for r in range(RM + 1)],
            'E': [blk(D1['E'][r], D2['E'][r]) for r in range(RM + 1)]}

def rand_wt_basis(wt):
    """random weight-preserving unimodular integer P and its inverse (unipotent within weights)"""
    n = len(wt); P = ident(n)
    for _ in range(3 * n):
        i, j = random.randrange(n), random.randrange(n)
        if i != j and wt[i] == wt[j]:
            c = random.randint(-3, 3)
            P = [[P[a][b] + (c * P[j][b] if a == i else 0) for b in range(n)] for a in range(n)]
    return P, inv_int(P)

def inv_int(P):
    n = len(P); A = [[Fr(x) for x in r] + [Fr(1 if i == j else 0) for j in range(n)] for i, r in enumerate(P)]
    for c in range(n):
        piv = next(k for k in range(c, n) if A[k][c])
        A[c], A[piv] = A[piv], A[c]
        p = A[c][c]; A[c] = [x / p for x in A[c]]
        for k in range(n):
            if k != c and A[k][c]:
                t = A[k][c]; A[k] = [a - t * b for a, b in zip(A[k], A[c])]
    out = [[A[i][n + j] for j in range(n)] for i in range(n)]
    assert all(x.denominator == 1 for r in out for x in r)
    return [[int(x) for x in r] for r in out]

def conj(D, P, Pi):
    return {'wt': D['wt'], 'F': [mul(mul(P, m), Pi) for m in D['F']], 'E': [mul(mul(P, m), Pi) for m in D['E']]}

def sW(X, x, l):  # columns F^{(r)} x, r = 0..l
    cols = [matvec(X['F'][r], x) for r in range(l + 1)]
    return tr(cols)

RM = 7
weyl = lambda l: dense(c18.weyl(l), RM)
dweyl = lambda l: dense(c18.dweyl(l), RM)

# 1. (D1), (D3)
lats = [("Δ3", weyl(3)), ("∇4", dweyl(4)), ("V⊗Δ2", dense(c18.tensorV(c18.weyl(2)), RM)),
        ("V⊗V⊗V", dense(c18.tensorV(c18.tensorV(c18.V)), RM)), ("V⊗∇3", dense(c18.tensorV(c18.dweyl(3)), RM)),
        ("Δ2⊕∇5", dsum(weyl(2), dweyl(5)))]
for name, D in lats:
    ok(is_dp(D) == 0, f"input {name} is DP")
    ok(is_dp(dual(D)) == 0, f"D1 dual {name}")
    ok(dual(dual(D)) == D, f"D3 {name}")
# 2. (D4)
for l in range(0, 11):
    ok(dual(weyl(l)) == dweyl(l), f"D4 dual Δ({l}) = ∇({l})")
    ok(dual(dweyl(l)) == weyl(l), f"D4 dual ∇({l}) = Δ({l})")
# 3. (D2), (D5) on the C19 sequences
for m in range(1, 6):
    fD, gD, fN, gN = c19.maps(m)
    Xd, Yd, Zd = weyl(m + 1), dense(c18.tensorV(c18.weyl(m)), RM), weyl(m - 1)
    nY = 2 * (m + 1)
    F = [[fD(i).get(j, 0) for i in range(m + 2)] for j in range(nY)]
    G = [[gD(i).get(j, 0) for i in range(nY)] for j in range(m)]
    ok(is_hom(F, Xd, Yd) == 0 and is_hom(G, Yd, Zd) == 0, f"C19 maps m={m}")
    ok(is_hom(tr(G), dual(Zd), dual(Yd)) == 0, f"D2 trM g m={m}")
    ok(is_hom(tr(F), dual(Yd), dual(Xd)) == 0, f"D2 trM f m={m}")
    for p in (2, 3, 5, 7, 11):
        ok(c19.rank_mod([r[:] for r in tr(G)], p) == m, f"D5 trM g injective mod {p} m={m}")
        ok(c19.rank_mod([r[:] for r in tr(F)], p) == m + 2, f"D5 trM f surjective mod {p} m={m}")
    ok(mul(tr(F), tr(G)) == zeros(m + 2, m), f"D5 trM f ∘ trM g = 0 m={m}")

# 4. (W) on X = Δ(l) ⊕ N, random weight basis
def W_test(l, N, xextra=None):
    D = weyl(l); X0 = dsum(D, N); n = len(X0['wt']); n1 = l + 1
    P, Pi = rand_wt_basis(X0['wt']); X = conj(X0, P, Pi)
    g = mul([[1 if (i == j) else 0 for i in range(n)] for j in range(n1)], Pi)   # projection ∘ P^{-1}
    x0 = [0] * n; x0[0] = 1
    for k in range(n1, n):
        if X0['wt'][k] == l: x0[k] = random.randint(-5, 5)
    if xextra is not None: x0[xextra] += 1
    x = matvec(P, x0)
    S = sW(X, x, l)
    return is_hom(S, D, X), mul(g, S) == ident(n1)
for l in range(1, 6):
    for N in [weyl(k) for k in range(0, l + 1)] + [dweyl(k) for k in range(0, l + 1)] + [dsum(weyl(l), dweyl(max(l - 2, 0)))]:
        for _ in range(3):
            b, gs = W_test(l, N)
            ok(b == 0, f"W hom l={l}"); ok(gs, f"W g s = id l={l}")

# 5. (E2) on X = ∇(m) ⊕ Δ(l), random weight basis
def solve_weight(A, b, idx):
    """solve A x = b over Q with x supported on idx; return integer x or None"""
    cols = [[A[j][i] for j in range(len(A))] for i in idx]
    M = [[Fr(cols[c][j]) for c in range(len(idx))] + [Fr(b[j])] for j in range(len(A))]
    piv = []; r = 0
    for c in range(len(idx)):
        p = next((k for k in range(r, len(M)) if M[k][c]), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; t = M[r][c]; M[r] = [x / t for x in M[r]]
        for k in range(len(M)):
            if k != r and M[k][c]:
                t = M[k][c]; M[k] = [a - t * bb for a, bb in zip(M[k], M[r])]
        piv.append(c); r += 1
    if any(M[k][-1] for k in range(r, len(M))): return None
    x = [Fr(0)] * len(idx)
    for k, c in enumerate(piv): x[c] = M[k][-1]
    return x
def E_test(m, l):
    Nb, D = dweyl(m), weyl(l); X0 = dsum(Nb, D); n = len(X0['wt']); nN = m + 1; nD = l + 1
    P, Pi = rand_wt_basis(X0['wt']); X = conj(X0, P, Pi)
    f = mul(P, [[1 if i == j else 0 for i in range(nN)] for j in range(n)])            # N -> X
    g = mul([[1 if i == nN + j else 0 for i in range(n)] for j in range(nD)], Pi)      # X -> Δ(l)
    ok(is_hom(f, Nb, X) == 0 and is_hom(g, X, D) == 0 and mul(g, f) == zeros(nD, nN), f"E input m={m} l={l}")
    e0 = [1] + [0] * l
    if m <= l:
        idx = [k for k in range(n) if X['wt'][k] == l]
        xs = solve_weight(g, e0, idx); x = [0] * n
        for k, v in zip(idx, xs): x[k] = v
        S = sW(X, x, l)
    else:
        Xs = dual(X); fT = tr(f)                       # dual sequence: ∇(l) -> X* -> Δ(m)
        idx = [k for k in range(n) if Xs['wt'][k] == m]
        xs = solve_weight(fT, [1] + [0] * m, idx); x = [0] * n
        for k, v in zip(idx, xs): x[k] = v
        Sd = sW(Xs, x, m)                              # Δ(m) -> X*, section of trM f
        ok(is_hom(Sd, weyl(m), Xs) == 0, f"E dual section hom m={m} l={l}")
        R = tr(Sd)                                     # X -> ∇(m)
        ok(is_hom(R, X, Nb) == 0, f"E retraction hom m={m} l={l}")
        ok(mul(R, f) == ident(nN), f"E r f = id m={m} l={l}")
        sig = mul(P, [[1 if i + nN == j else 0 for i in range(nD)] for j in range(n)])
        K = [[random.randint(-4, 4) for _ in range(nD)] for _ in range(nN)]
        sig = add(sig, mul(f, K))                      # a random linear section of g
        S = mul(add(ident(n), mul(f, R), -1), sig)
    ok(is_hom(S, D, X) == 0, f"E section hom m={m} l={l}")
    ok(mul(g, S) == ident(nD), f"E g s = id m={m} l={l}")
for m in range(0, 6):
    for l in range(0, 6):
        for _ in range(2): E_test(m, l)
print(f"chkC25: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
b, gs = W_test(3, dweyl(3), xextra=5)   # add δ of weight l - 2 = 1 (index 5: the weight-1 vector of the ∇(3) part) to x
control("x not of weight l", b > 0)
fD, gD, _, _ = c19.maps(2)               # Δ(3) -> V⊗Δ(2) -> Δ(1): sub weights exceed [-1, 1]
Y = dense(c18.tensorV(c18.weyl(2)), RM); G = [[gD(i).get(j, 0) for i in range(6)] for j in range(2)]
idx = [k for k in range(6) if Y['wt'][k] == 1]; xs = solve_weight(G, [1, 0], idx); x = [0] * 6
for k, v in zip(idx, xs): x[k] = v
control("W on V⊗Δ(2) -> Δ(1) (sub weights too big)", is_hom(sW(Y, x, 1), weyl(1), Y) > 0)
control("dual without the swap is not DP", is_dp(dual(weyl(3), swap=False)) > 0)
control("dual Δ(3) is not Δ(3)", dual(weyl(3)) != weyl(3))
Nb, D = dweyl(4), weyl(2); X0 = dsum(Nb, D); n = 8
P, Pi = rand_wt_basis(X0['wt']); X = conj(X0, P, Pi)
x0 = [0] * n; x0[5] = 1; x0[1] = 1                     # weight-2 preimage of e_0 with a ∇(4) component (index 1)
control("m > l by W directly", is_hom(sW(X, matvec(P, x0), 2), D, X) > 0)
print(f"controls: {fires}/{ctrl} fire")
