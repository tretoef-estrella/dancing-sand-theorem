#!/usr/bin/env python3
"""Brute force for Lean piece C50 (paper v8 §10.7, Lemma 10.19: the glue commutes with the dance).
Grepy Escribano, 10 Oct 2026. Integer matrices stand in for the noncommutative ring Bf Z_2; inverses are
exact rationals with odd determinants (2-adic integers). Claims:
 (B1) block rules of glue(X, Y, Z) = [[X, 0], [Z, Y]];
 (G2) glue(Q_X, Q_Y, -Q_Y P_Z Q_X) inverts glue(P_X, P_Y, P_Z); the lower-left L of the glued Schur
      complement has 2L = S_Y - S_X; with S_X = 2X', S_Y = 2Y', Y' - X' = 2W: L = 2W;
 (S3) the relabelling index identity with the glue index on top; (S4) slots ds (2r) = 2 slots ds r.
Controls must fire."""
import random, itertools
from fractions import Fraction as Fr
random.seed(5010)
cnt = {}; fails = []; ctrl = {}
def ok(name, cond, info=None):
    cnt[name] = cnt.get(name, 0) + 1
    if not cond: fails.append((name, info))
def fire(name, cond):
    ctrl[name] = ctrl.get(name, 0) + (1 if cond else 0)

def Z(n): return [[Fr(0)] * n for _ in range(n)]
def I(n): return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
def add(A, B): return [[a + b for a, b in zip(r, s)] for r, s in zip(A, B)]
def sub(A, B): return [[a - b for a, b in zip(r, s)] for r, s in zip(A, B)]
def sc(c, A): return [[c * a for a in r] for r in A]
def mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]
def rnd(n, lo=-3, hi=3): return [[Fr(random.randint(lo, hi)) for _ in range(n)] for _ in range(n)]
def inv(A):
    n = len(A); M = [r[:] + I(n)[i] for i, r in enumerate(A)]
    for c in range(n):
        p = next(i for i in range(c, n) if M[i][c] != 0)
        M[c], M[p] = M[p], M[c]
        pv = M[c][c]; M[c] = [x / pv for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[c])]
    return [r[n:] for r in M]
def det(A):
    A = [r[:] for r in A]; n = len(A); d = Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]; A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return d
def v2int(x):
    """True iff the rational x is a 2-adic integer."""
    return x.denominator % 2 == 1
def glue(X, Y, Zl):
    n = len(X); G = Z(2 * n)
    for i in range(n):
        for j in range(n):
            G[i][j] = X[i][j]; G[n + i][j] = Zl[i][j]; G[n + i][n + j] = Y[i][j]
    return G
def blocks(G):
    n = len(G) // 2
    return ([r[:n] for r in G[:n]], [r[n:] for r in G[n:]], [r[:n] for r in G[n:]], [r[n:] for r in G[:n]])

for n in (3, 4):
    for trial in range(200):
        # (B1)
        X, Y, Zl, X2, Y2, Z2 = (rnd(n) for _ in range(6))
        ok("B1-mul", mul(glue(X, Y, Zl), glue(X2, Y2, Z2)) == glue(mul(X, X2), mul(Y, Y2), add(mul(Zl, X2), mul(Y, Z2))))
        ok("B1-add", add(glue(X, Y, Zl), glue(X2, Y2, Z2)) == glue(add(X, X2), add(Y, Y2), add(Zl, Z2)))
        ok("B1-one", glue(I(n), I(n), Z(n)) == I(2 * n))
        # (G2): pivots invertible over Z_2 (odd determinant)
        while True:
            PX = add(I(n), sc(2, rnd(n))); p = rnd(n); PY = add(PX, sc(2, p))
            if det(PX).numerator % 2 and det(PY).numerator % 2: break
        PZ = p  # 2 PZ = PY - PX
        b, c, d = rnd(n), rnd(n), rnd(n)
        BX, CX, DX = rnd(n), rnd(n), rnd(n)
        BY, CY, DY = add(BX, sc(2, b)), add(CX, sc(2, c)), add(DX, sc(2, d))
        QX, QY = inv(PX), inv(PY)
        ok("G2-int", all(v2int(x) for M in (QX, QY) for r in M for x in r))
        QZ = sc(-1, mul(mul(QY, PZ), QX))
        Pg, Qg = glue(PX, PY, PZ), glue(QX, QY, QZ)
        ok("G2-inv-right", mul(Pg, Qg) == I(2 * n)); ok("G2-inv-left", mul(Qg, Pg) == I(2 * n))
        Qbad = glue(QX, QY, sc(-1, QZ))
        fire("ctl-sign", mul(Pg, Qbad) != I(2 * n))
        Bg, Cg, Dg = glue(BX, BY, b), glue(CX, CY, c), glue(DX, DY, d)
        S = sub(Dg, mul(mul(Bg, Qg), Cg))
        SX, SY, L, UR = blocks(S)
        SXd = sub(DX, mul(mul(BX, QX), CX)); SYd = sub(DY, mul(mul(BY, QY), CY))
        ok("G2-blocks", SX == SXd and SY == SYd and all(x == 0 for r in UR for x in r))
        ok("G2-2L", sc(2, L) == sub(SY, SX))
        Bbad = glue(BX, BY, add(b, I(n)))
        Lb = blocks(sub(Dg, mul(mul(Bbad, Qg), Cg)))[2]
        fire("ctl-perturb-BZ", sc(2, Lb) != sub(SY, SX))
        # (G2) with S_X = 2X', S_Y = 2Y', Y' - X' = 2W: choose D to force it
        Xp, W = rnd(n), rnd(n); Yp = add(Xp, sc(2, W))
        DX2 = add(sc(2, Xp), mul(mul(BX, QX), CX))
        DY2 = add(sc(2, Yp), mul(mul(BY, QY), CY))
        d2 = sc(Fr(1, 2), sub(DY2, DX2))
        S2 = sub(glue(DX2, DY2, d2), mul(mul(Bg, Qg), Cg))
        ok("G2-L=2W", blocks(S2)[2] == sc(2, W) and blocks(S2)[0] == sc(2, Xp) and blocks(S2)[1] == sc(2, Yp))
        Yq = add(Yp, I(n)); DY3 = add(sc(2, Yq), mul(mul(BY, QY), CY)); d3 = sc(Fr(1, 2), sub(DY3, DX2))
        S3 = sub(glue(DX2, DY3, d3), mul(mul(Bg, Qg), Cg))
        fire("ctl-not-congruent", blocks(S3)[2] != sc(2, W))

# (S3) index identity: glue index on top
def s3(r, top=True):
    r2 = 2 * r
    for j in range(r2 * 2):
        jj, b = j // 2, j % 2                  # (splitIso r2).symm j
        g, s = (jj // r, jj % r) if top else (jj % 2, jj // 2)   # (gE h).symm jj
        G2, k = (j // (2 * r), j % (2 * r)) if top else (j % 2, j // 2)   # (gE h2).symm j, h2 : r2*2 = 2*(r*2)
        s2, b2 = k // 2, k % 2                 # (splitIso r).symm k
        if not (g == G2 and s == s2 and b == b2): return False
    return True
for r in range(1, 7):
    ok("S3-top", s3(r))
    if r >= 2: fire("ctl-bottom-digit", not s3(r, top=False))
# (S4) slots
def slots(ds, r):
    for x in ds:
        if x: r *= 2
    return r
for L in range(7):
    for ds in itertools.product([False, True], repeat=L):
        for r in range(1, 5):
            ok("S4", slots(ds, 2 * r) == 2 * slots(ds, r))

tot = sum(cnt.values())
print("COUNTS", cnt)
print("TOTAL", tot, "FAILURES", len(fails), fails[:5])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
