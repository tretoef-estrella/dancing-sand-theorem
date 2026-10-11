#!/usr/bin/env python3
"""Brute force for piece C30 (the step of Theorem 3.6 and the kit of isomorphisms).
Grepy Escribano, 8 Oct 2026.
  1. (W1) on the table himg: every term has the weight of its source row, for N.wt i in [-4, 4].
  2. The explicit matrix of lemma35Iso (from himg, uIdx, L5img) for N in {one, V, V⊗V} over F_2:
     weight-preserving, invertible mod 2, commutes mod 2 with every F^(r), E^(r) of the reductions
     of X = V⊗V⊗Φ(N) and Y = Φ(N)^2 ⊕ Φ(V⊗N).
  3. (A1): the hom and the inverse lift (procedure of C28 (L2)) to f, g over Z_(2) commuting with
     every operator; g f and f g are ≡ 1 mod 2 with odd determinant.
  4. (K2): the reindexing Fin 2 × (M ⊕ N) ≃ (Fin 2 × M) ⊕ (Fin 2 × N) intertwines Φ(M ⊕ N) and
     Φ(M) ⊕ Φ(N) exactly over Q, for several M, N.
Controls: a wrong row of himg (e_1 ↦ e_2) is not weight-preserving; a wrong reindexing in (K2)
does not commute; a wrong matrix (one entry flipped) does not commute mod 2."""
import os, sys
from fractions import Fraction as Fr
here = os.path.dirname(os.path.abspath(__file__))
s29 = open(os.path.join(here, "chkC29.py")).read()
_keep30 = sys.stdout; sys.stdout = open(os.devnull, "w")
exec(s29[:s29.index("for lam in range(0, 8):")])
sys.stdout = _keep30
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)
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
wV = {0: 1, 1: -1}
uIdx = {0: (0, 0), 1: (1, 0), 2: (0, 1), 3: (1, 1)}
HIMG = {(0,0,0): ['e0'], (0,0,1): ['e1','b0'], (0,1,0): ['e1','b0','c0'], (0,1,1): ['e2','c1'],
        (1,0,0): ['e1','c0'], (1,0,1): ['e2','b1','c1'], (1,1,0): ['e2','b1'], (1,1,1): ['e3']}
def term_wt(t, w):
    k, x = t[0], int(t[1])
    if k == 'e': e, e2 = uIdx[x]; return 2 * (wV[e2] + w) + wV[e]
    return 2 * w + wV[x]
def wpres(table):
    good = True
    for (a, b, c), ts in table.items():
        for w in range(-4, 5):
            src = wV[a] + wV[b] + 2 * w + wV[c]
            good &= all(term_wt(t, w) == src for t in ts)
    return good
ok(wpres(HIMG), "W1 table weight-preserving")

def hom_matrix(n, table):
    """X basis (a,b,c,i): a*4n + b*2n + c*n + i; Y: inl inl (e,i) e*n+i; inl inr 2n+e*n+i;
    inr (e,(e',i)) 4n + e*2n + e'*n + i"""
    Mx = zeros(8 * n, 8 * n)
    for (a, b, c), ts in table.items():
        for i in range(n):
            src = a * 4 * n + b * 2 * n + c * n + i
            for t in ts:
                k, x = t[0], int(t[1])
                if k == 'e': e, e2 = uIdx[x]; tgt = 4 * n + e * 2 * n + e2 * n + i
                elif k == 'b': tgt = x * n + i
                else: tgt = 2 * n + x * n + i
                Mx[tgt][src] = (Mx[tgt][src] + 1) % 2
    return Mx
def red(Mx): return [[mod2(a) for a in r] for r in Mx]
def mul2(A, B): return [[x % 2 for x in r] for r in mul(A, B)]
def inv2(Mx):
    n = len(Mx); Aug = [r[:] + [int(i == j) for j in range(n)] for i, r in enumerate(Mx)]
    for c in range(n):
        p = next((i for i in range(c, n) if Aug[i][c] % 2), None)
        if p is None: return None
        Aug[c], Aug[p] = Aug[p], Aug[c]
        for i in range(n):
            if i != c and Aug[i][c] % 2: Aug[i] = [(x + y) % 2 for x, y in zip(Aug[i], Aug[c])]
    return [r[n:] for r in Aug]
def as_dict(S):
    return {'wt': S['wt'], 'F': lambda r, i, S=S: {j: S['F'][r][j][i] for j in range(len(S['wt'])) if S['F'][r][j][i]} if r <= RM else {},
            'E': lambda r, i, S=S: {j: S['E'][r][j][i] for j in range(len(S['wt'])) if S['E'][r][j][i]} if r <= RM else {}}
def commutes2(Mx, X, Y):
    return all(mul2(Mx, red(X[op][r])) == mul2(red(Y[op][r]), Mx) for op in 'FE' for r in range(RM + 1))
def wp_mat(Mx, X, Y):
    return all(Mx[j][i] == 0 or X['wt'][i] == Y['wt'][j] for j in range(len(Y['wt'])) for i in range(len(X['wt'])))

for name, N in [("one", c18.triv), ("V", c18.V), ("V⊗V", c18.tensorV(c18.V))]:
    n = len(N['wt'])
    X = dense(c18.tensorV(c18.tensorV(Phi(N))), RM)
    P = dense(Phi(N), RM); Q = dense(Phi(c18.tensorV(N)), RM)
    Y = dsum(dsum(P, P), Q)
    Hm = hom_matrix(n, HIMG); Gm = inv2(Hm)
    ok(Gm is not None, f"{name}: invertible mod 2")
    ok(wp_mat(Hm, X, Y), f"{name}: hom weight-preserving")
    ok(Gm is not None and wp_mat(Gm, Y, X), f"{name}: inv weight-preserving")
    ok(commutes2(Hm, X, Y), f"{name}: hom commutes mod 2")
    ok(Gm is not None and commutes2(Gm, Y, X), f"{name}: inv commutes mod 2")
    # (A1) lifts
    lifts = []
    for (S, T, M0) in [(X, Y, Hm), (Y, X, Gm)]:
        unk = unknowns(S, T); rows = comm_rows(S, T, unk)
        D = dmap(S, T, M0)
        even = all(Fr(a).numerator % 2 == 0 for op in 'FE' for r in range(RM + 1) for row in D[op][r] for a in row)
        ok(even, f"{name}: d φ0 even")
        bvec = [Fr(a) / 2 for op in 'FE' for r in range(RM + 1) for row in D[op][r] for a in row]
        y = solve_2adic(rows, bvec, len(unk)); ok(y is not None, f"{name}: lift solvable")
        if y is None: lifts.append(None); continue
        L = add(M0, tomat(S, T, unk, y), -2)
        Dl = dmap(S, T, L)
        ok(all(a == 0 for op in 'FE' for r in range(RM + 1) for row in Dl[op][r] for a in row), f"{name}: lift commutes")
        ok(red(L) == M0, f"{name}: lift reduces")
        lifts.append(L)
    if None not in lifts:
        f, g = lifts
        for C in (mul(g, f), mul(f, g)):
            ok(red(C) == ident(len(C)), f"{name}: composite ≡ 1 mod 2")
            ok(v2(det(C)) == 0, f"{name}: composite has odd determinant")
# (K2)
def K2(M, N, wrong=False):
    m, n = len(M['wt']), len(N['wt'])
    Sd = dsum(dense(M, RM), dense(N, RM))
    L = dense(Phi(as_dict(Sd)), RM); R = dsum(dense(Phi(M), RM), dense(Phi(N), RM))
    Pm = zeros(2 * (m + n), 2 * (m + n))
    for e in range(2):
        for k in range(m + n):
            src = e * (m + n) + k
            e2 = (1 - e) if (wrong and k == m) else e
            tgt = e2 * m + k if k < m else 2 * m + e2 * n + (k - m)
            Pm[tgt][src] = 1
    return all(mul(Pm, L[op][r]) == mul(R[op][r], Pm) for op in 'FE' for r in range(RM + 1)) and \
        all(Pm[j][i] == 0 or L['wt'][i] == R['wt'][j] for j in range(len(R['wt'])) for i in range(len(L['wt'])))
for (a, b) in [(c18.triv, c18.V), (c18.V, c18.V), (c18.weyl(2), c18.dweyl(3)), (c18.tensorV(c18.V), c18.weyl(1))]:
    ok(K2(a, b), "K2 reindexing intertwines")
print(f"chkC30: {checks} checks, {fails} failures")

fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
bad = dict(HIMG); bad[(0, 0, 1)] = ['e2', 'b0']
control("wrong himg row not weight-preserving", not wpres(bad))
control("wrong reindexing does not intertwine", not K2(c18.V, c18.V, wrong=True))
N = c18.V; n = 2
X = dense(c18.tensorV(c18.tensorV(Phi(N))), RM); P = dense(Phi(N), RM); Q = dense(Phi(c18.tensorV(N)), RM)
Y = dsum(dsum(P, P), Q); Hb = hom_matrix(n, HIMG); Hb[0][0] ^= 1; Hb[4 * n][0] ^= 1; Hb[0][n] ^= 1
control("flipped matrix does not commute", not commutes2(Hb, X, Y))
print(f"controls: {fires}/{ctrl} fire")
