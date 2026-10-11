#!/usr/bin/env python3
"""Brute force for piece C27 (glued lattices, cocycles, Ext^1(M, N) = 0 for Δ-filtered M and
∇-filtered N). Grepy Escribano, 8 Oct 2026. Over Q and over F_2, F_3, F_5.
  1. (G2) ⟺ IsDP: for every basis cocycle (solution of the linear equations (W), (P0), (P1), (K))
     the glued block data satisfy IsDP (checked with the C25 engine over Q, integer-scaled); random
     non-cocycles fail it (control).
  2. (G4) every dψ (ψ weight-preserving) satisfies the cocycle equations.
  3. (V4) dim Z^1(M, N) = dim B^1(M, N) for Δ-filtered M (Δ(l), V⊗Δ(m), V⊗V⊗V) and ∇-filtered N
     (∇(m), V⊗∇(m), V⊗V) over Q, F_2, F_3, F_5.
  4. (G7) the cocycle read off the C19 sequences (cF r = ρ X.F σ) satisfies the equations, and
     the glued lattice is conjugate to X by θ.
Controls: Ext^1(Δ(0), Δ(2)) ≠ 0 and Ext^1(∇(2), ∇(0)) ≠ 0 modulo 2 (Z^1 > B^1), random c not a cocycle."""
import os, sys, random
from fractions import Fraction as Fr
from math import comb
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "chkC25.py")).read()
head = src[:src.index("RM = 7")]
_keep_stdout = sys.stdout; sys.stdout = open(os.devnull, "w")
exec(head)
exec(src[src.index("def solve_weight"):src.index("def E_test")])
sys.stdout = _keep_stdout
gch = c18.gchoose
random.seed(20261008 + 27)
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

def fnorm(x, p): return x if p == 0 else x % p
def finv(a, p): return 1 / a if p == 0 else pow(a, p - 2, p)
def rank(rows, p):
    M = [[Fr(x) if p == 0 else x % p for x in r] for r in rows]
    if not M: return 0
    r = 0
    for c in range(len(M[0])):
        k = next((i for i in range(r, len(M)) if M[i][c]), None)
        if k is None: continue
        M[r], M[k] = M[k], M[r]; t = finv(M[r][c], p); M[r] = [fnorm(x * t, p) for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                t = M[i][c]; M[i] = [fnorm(a - t * b, p) for a, b in zip(M[i], M[r])]
        r += 1
    return r
def nullspace_Q(rows, n):
    M = [[Fr(x) for x in r] for r in rows]; piv = []; r = 0
    for c in range(n):
        k = next((i for i in range(r, len(M)) if M[i][c]), None)
        if k is None: continue
        M[r], M[k] = M[k], M[r]; t = M[r][c]; M[r] = [x / t for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                t = M[i][c]; M[i] = [a - t * b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    out = []
    for f in range(n):
        if f in piv: continue
        v = [Fr(0)] * n; v[f] = Fr(1)
        for k, c in enumerate(piv): v[c] = -M[k][f]
        out.append(v)
    return out

class Unk:
    """unknowns: cF r and cE r entries (j, i) allowed by (W)"""
    def __init__(s, M, N):
        s.M, s.N = M, N; s.idx = {}
        for op, sg in (('F', -1), ('E', 1)):
            for r in range(RM + 1):
                for i in range(len(M['wt'])):
                    for j in range(len(N['wt'])):
                        if N['wt'][j] == M['wt'][i] + sg * 2 * r: s.idx[(op, r, j, i)] = len(s.idx)
        s.n = len(s.idx)
    def mat(s, x, op, r):
        A = zeros(len(s.N['wt']), len(s.M['wt']))
        for (o, rr, j, i), k in s.idx.items():
            if o == op and rr == r: A[j][i] = x[k]
        return A
def cocycle_rows(U):
    """rows of the linear equations (P0), (P1), (K) of (G2) (as functions of the unknown vector)"""
    M, N = U.M, U.N; nM, nN = len(M['wt']), len(N['wt']); rows = []
    def basisvec(k):
        x = [0] * U.n; x[k] = 1; return x
    # we build each equation as a linear functional by evaluating on basis vectors of the unknowns
    cols = [basisvec(k) for k in range(U.n)]
    def emit(fun):  # fun(x) -> list of numbers (an equation block = 0); linear in x
        if not cols: return
        vals = [fun(c) for c in cols]
        for t in range(len(vals[0])): rows.append([v[t] for v in vals])
    flat = lambda A: [a for r_ in A for a in r_]
    for op in 'FE':
        emit(lambda x, op=op: flat(U.mat(x, op, 0)))
        for a in range(RM + 1):
            for b in range(RM + 1 - a):
                emit(lambda x, op=op, a=a, b=b: flat(add(add(mul(N[op][a], U.mat(x, op, b)), mul(U.mat(x, op, a), M[op][b])),
                                                         scal(comb(a + b, a), U.mat(x, op, a + b)), -1)))
            for b in range(RM + 1 - a, RM + 1):   # a + b > RM: then cX(a+b) = 0 by (W)
                emit(lambda x, op=op, a=a, b=b: flat(add(mul(N[op][a], U.mat(x, op, b)), mul(U.mat(x, op, a), M[op][b]))))
    for i in range(nM):
        w = M['wt'][i]; e = [1 if k == i else 0 for k in range(nM)]
        for r in range(RM + 1):
            for s_ in range(RM + 1):
                def kf(x, r=r, s_=s_, w=w, e=e):
                    lhs = [p + q for p, q in zip(matvec(N['E'][s_], matvec(U.mat(x, 'F', r), e)), matvec(U.mat(x, 'E', s_), matvec(M['F'][r], e)))]
                    rhs = [0] * nN
                    for j in range(min(r, s_) + 1):
                        c = gch(w + s_ - r, j)
                        v = [p + q for p, q in zip(matvec(N['F'][r - j], matvec(U.mat(x, 'E', s_ - j), e)), matvec(U.mat(x, 'F', r - j), matvec(M['E'][s_ - j], e)))]
                        rhs = [a + c * b for a, b in zip(rhs, v)]
                    return [a - b for a, b in zip(lhs, rhs)]
                emit(kf)
    return rows
def d_vectors(U):
    """dψ for ψ running over a basis of the weight-preserving maps, as unknown vectors"""
    M, N = U.M, U.N; out = []
    for i in range(len(M['wt'])):
        for j in range(len(N['wt'])):
            if M['wt'][i] != N['wt'][j]: continue
            psi = zeros(len(N['wt']), len(M['wt'])); psi[j][i] = 1
            x = [0] * U.n
            for op in 'FE':
                for r in range(RM + 1):
                    D = add(mul(psi, M[op][r]), mul(N[op][r], psi), -1)
                    for jj in range(len(N['wt'])):
                        for ii in range(len(M['wt'])):
                            if D[jj][ii]:
                                k = U.idx.get((op, r, jj, ii))
                                if k is None: x = None; break
                                x[k] = D[jj][ii]
                        if x is None: break
                    if x is None: break
                if x is None: break
            out.append(x)
    return out
def glued(U, x):
    M, N = U.M, U.N; nM, nN = len(M['wt']), len(N['wt']); n = nN + nM
    def blk(op, r):
        B = zeros(n, n); C = U.mat(x, op, r)
        for j in range(nN):
            for i in range(nN): B[j][i] = N[op][r][j][i]
            for i in range(nM): B[j][nN + i] = C[j][i]
        for j in range(nM):
            for i in range(nM): B[nN + j][nN + i] = M[op][r][j][i]
        return B
    return {'wt': N['wt'] + M['wt'], 'F': [blk('F', r) for r in range(RM + 1)], 'E': [blk('E', r) for r in range(RM + 1)]}
_cache = {}
def Z_B(M, N, p):
    key = (id(M), id(N))
    if key not in _cache:
        U0 = Unk(M, N); _cache[key] = (U0, cocycle_rows(U0))
    U, rows = _cache[key]
    z = U.n - (rank(rows, p) if rows else 0)
    ds = d_vectors(U)
    b = rank(ds, p) if ds else 0
    return z, b, U, rows, ds

Dlist = [("Δ0", weyl(0)), ("Δ1", weyl(1)), ("Δ2", weyl(2)), ("Δ3", weyl(3)), ("V⊗Δ1", tV(c18.weyl(1))), ("V⊗Δ2", tV(c18.weyl(2))), ("V⊗V⊗V", tV(c18.tensorV(c18.V)))]
Nlist = [("∇0", dweyl(0)), ("∇1", dweyl(1)), ("∇2", dweyl(2)), ("∇3", dweyl(3)), ("V⊗∇1", tV(c18.dweyl(1))), ("V⊗∇2", tV(c18.dweyl(2))), ("V⊗V", tV(c18.V))]

# 1, 2 over Q on a few pairs
for (mn, M) in Dlist[:5]:
    for (nn, N) in Nlist[:5]:
        z, b, U, rows, ds = Z_B(M, N, 0)
        ok(all(rank(rows + [d], 0) == rank(rows, 0) or not any(sum(a * c for a, c in zip(r, d)) for r in rows) for d in ds), f"G4 {mn},{nn}")
        for d in ds: ok(all(sum(a * c for a, c in zip(r, d)) == 0 for r in rows), f"G4 dψ is a cocycle {mn},{nn}")
        for v in nullspace_Q(rows, U.n):
            den = 1
            for t in v: den = den * t.denominator // __import__('math').gcd(den, t.denominator)
            x = [int(t * den) for t in v]
            ok(is_dp(glued(U, x)) == 0, f"G2 cocycle ⇒ IsDP {mn},{nn}")
# 3 the vanishing
for (mn, M) in Dlist:
    for (nn, N) in Nlist:
        for p in (0, 2, 3, 5):
            z, b, U, rows, ds = Z_B(M, N, p)
            ok(z == b, f"V4 Z^1 = B^1 {mn},{nn} p={p}: {z} vs {b}")
# 4 (G7) on the C19 sequences
for m in range(1, 4):
    fD, gD, fN, gN = c19.maps(m)
    for (Xs, Ns, Ms, f, g, nN, nX, nM) in [
        (tV(c18.weyl(m)), weyl(m + 1), weyl(m - 1), fD, gD, m + 2, 2 * (m + 1), m),
        (tV(c18.dweyl(m)), dweyl(m - 1), dweyl(m + 1), fN, gN, m, 2 * (m + 1), m + 2)]:
        Fm = [[f(i).get(j, 0) for i in range(nN)] for j in range(nX)]
        Gm = [[g(i).get(j, 0) for i in range(nX)] for j in range(nM)]
        # weight-preserving section of g and retraction of f over Q
        sig = zeros(nX, nM)
        for i in range(nM):
            idx = [k for k in range(nX) if Xs['wt'][k] == Ms['wt'][i]]
            col = solve_weight(Gm, [1 if t == i else 0 for t in range(nM)], idx)
            for k, v in zip(idx, col): sig[k][i] = v
        P = add(ident(nX), mul(sig, Gm), -1)
        rho = zeros(nN, nX)
        for c in range(nX):
            col = solve_weight(Fm, [P[j][c] for j in range(nX)], list(range(nN)))
            for k in range(nN): rho[k][c] = col[k]
        U = Unk(Ms, Ns); x = [0] * U.n; good = True
        for op in 'FE':
            for r in range(RM + 1):
                C = mul(mul(rho, Xs[op][r]), sig)
                for j in range(nN):
                    for i in range(nM):
                        if C[j][i]:
                            k = U.idx.get((op, r, j, i))
                            if k is None: good = False
                            else: x[k] = C[j][i]
        ok(good, f"G7 (W) m={m}")
        rows = cocycle_rows(U)
        ok(all(sum(a * c for a, c in zip(rr, x)) == 0 for rr in rows), f"G7 cocycle m={m}")
        Th = [r_ for r_ in rho] + [r_ for r_ in Gm]          # θ = (ρ, g)
        Gl = glued(U, x)
        ok(all(mul(Th, Xs[op][r]) == mul(Gl[op][r], Th) for op in 'FE' for r in range(RM + 1)), f"G7 θ intertwines m={m}")
print(f"chkC27: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
z, b, *_ = Z_B(weyl(0), weyl(2), 2); control(f"Ext^1(Δ0, Δ2) ≠ 0 mod 2 (Z={z}, B={b})", z > b)
z, b, *_ = Z_B(dweyl(2), dweyl(0), 2); control(f"Ext^1(∇2, ∇0) ≠ 0 mod 2 (Z={z}, B={b})", z > b)
z, b, *_ = Z_B(weyl(0), weyl(2), 3); control(f"(sanity, must hold) Ext^1(Δ0, Δ2) = 0 mod 3 (Z={z}, B={b})", z == b)
U = Unk(weyl(1), dweyl(1)); x = [random.randint(-3, 3) for _ in range(U.n)]
control("a random c is not a cocycle (glued data not DP)", is_dp(glued(U, x)) > 0)
print(f"controls: {fires}/{ctrl} fire")
