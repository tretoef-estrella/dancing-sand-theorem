# fdance.py — «Grepy el volador 8», 4 Oct 2026. Flight 2's dance in the FORMAL Borel algebra:
# an element is  x = sum_m x_m(D) F^(m)  with x_m a table of values at the TARGET floor f = 0..L (Fractions).
# Product: (x y)_m(f) = sum_{a+b=m} C(m,a) x_a(f) y_b(f-a)   (sources f-m >= 0 only).
# Moves (exactly the slot conventions of tilt_dp / pdance):
#   doblar  N = Phi(N'):  x -> [[x00, x01], [x10, x11]] over N' (slots b0, b1), then Schur on (b1-rows x b0-cols), / 2
#   paso    N = V(x)Phi(N'): x -> 4x4 over N' in (A, B, C, Dd), then Schur on (B, Dd rows x A, C cols), / 2
# Systems: r x r matrices of elements (lower triangular in the dancer order). Final matrix: constant terms at floor 0.
import sys
sys.path.insert(0, 'engines')
from fractions import Fraction
from math import comb
from tilt_dp import dfact_odd

class E:
    """formal element: dict m -> list of L+1 Fractions (value at target floor f)."""
    __slots__ = ('L', 'c')
    def __init__(self, L, c=None):
        self.L = L; self.c = c if c is not None else {}
    def get(self, m, f):
        if f < m or f < 0 or f > self.L: return Fraction(0)
        t = self.c.get(m); return t[f] if t is not None else Fraction(0)
    def copy(self): return E(self.L, {m: list(t) for m, t in self.c.items()})

def zero(L): return E(L)
def one(L): return E(L, {0: [Fraction(1)] * (L + 1)})
def scal(L, fn): return E(L, {0: [Fraction(fn(f)) for f in range(L + 1)]})

def add(x, y, s=1):
    L = x.L; c = {m: list(t) for m, t in x.c.items()}
    for m, t in y.c.items():
        if m not in c: c[m] = [Fraction(0)] * (L + 1)
        for f in range(L + 1): c[m][f] += s * t[f]
    return E(L, {m: t for m, t in c.items() if any(t)})

def mul(x, y):
    L = x.L; c = {}
    for a, ta in x.c.items():
        for b, tb in y.c.items():
            m = a + b
            if m > L: continue
            k = comb(m, a); tm = c.setdefault(m, [Fraction(0)] * (L + 1))
            for f in range(m, L + 1):
                xa = ta[f]
                if xa: tm[f] += k * xa * tb[f - a]
    return E(L, {m: t for m, t in c.items() if any(t)})

def smul(s, x): return E(x.L, {m: [s * v for v in t] for m, t in x.c.items()})

def inv(x):
    """two-sided inverse; needs x_0(f) invertible for every f."""
    L = x.L; y = {}
    x0 = [x.get(0, f) for f in range(L + 1)]
    y[0] = [Fraction(1) / v for v in x0]
    for m in range(1, L + 1):
        t = [Fraction(0)] * (L + 1)
        for f in range(m, L + 1):
            s = Fraction(0)
            for a in range(1, m + 1):
                xa = x.get(a, f)
                if xa: s += comb(m, a) * xa * y[m - a][f - a]
            t[f] = -s / x0[f]
        y[m] = t
    return E(L, {m: t for m, t in y.items() if any(t)})

# ---------- matrices of elements ----------
def mzero(n, L): return [[zero(L) for _ in range(n)] for _ in range(n)]
def mmul(A, B):
    n, k, p = len(A), len(B), len(B[0]); L = A[0][0].L
    R = [[zero(L) for _ in range(p)] for _ in range(n)]
    for i in range(n):
        for j in range(p):
            acc = zero(L)
            for t in range(k):
                if A[i][t].c and B[t][j].c: acc = add(acc, mul(A[i][t], B[t][j]))
            R[i][j] = acc
    return R
def madd(A, B, s=1): return [[add(a, b, s) for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]

def minv_lower(P):
    """inverse of a matrix of elements that is lower triangular up to a permutation? We assume block lower triangular
    with invertible diagonal entries in the given order (true for the dance's pivot blocks)."""
    n = len(P); L = P[0][0].L
    # check upper part zero
    for i in range(n):
        for j in range(i + 1, n):
            assert not P[i][j].c, 'pivot block not lower triangular'
    X = mzero(n, L)
    for j in range(n):
        X[j][j] = inv(P[j][j])
        for i in range(j + 1, n):
            acc = zero(L)
            for t in range(j, i):
                if P[i][t].c and X[t][j].c: acc = add(acc, mul(P[i][t], X[t][j]))
            X[i][j] = smul(-1, mul(inv(P[i][i]), acc))
    return X

# ---------- the moves on one element ----------
def doblar_elem(x, Lp):
    """x on Phi(N') (floors 0..2Lp+1) -> 2x2 over N' (floors 0..Lp): [[x00, x01], [x10, x11]] (rows: output slot)."""
    c00, c11, c10, c01 = {}, {}, {}, {}
    for m, t in x.c.items():
        if m % 2 == 0:
            q = m // 2; den = dfact_odd(q)
            c00[q] = [t[2 * f] / den if 2 * f <= x.L else Fraction(0) for f in range(Lp + 1)]
            c11[q] = [t[2 * f + 1] / den if 2 * f + 1 <= x.L else Fraction(0) for f in range(Lp + 1)]
        else:
            q = (m - 1) // 2; den = dfact_odd(q + 1)
            c10[q] = [t[2 * f + 1] / den if 2 * f + 1 <= x.L else Fraction(0) for f in range(Lp + 1)]
            c01[q + 1] = [t[2 * f] * (2 * q + 2) / den if 2 * f <= x.L else Fraction(0) for f in range(Lp + 1)]
    mk = lambda c: E(Lp, {m: tt for m, tt in c.items() if any(tt)})
    return [[mk(c00), mk(c01)], [mk(c10), mk(c11)]]

def phi_slot(m, Lp):
    """slot matrix of F_Phi^(m) (no coefficient) over N': rows/cols slot 0, 1."""
    Z = zero(Lp)
    if m % 2 == 0:
        q = m // 2; e = E(Lp, {q: [Fraction(1, dfact_odd(q))] * (Lp + 1)})
        return [[e, Z], [Z, e]]
    q = (m - 1) // 2
    e10 = E(Lp, {q: [Fraction(1, dfact_odd(q + 1))] * (Lp + 1)})
    e01 = E(Lp, {q + 1: [Fraction(2 * q + 2, dfact_odd(q + 1))] * (Lp + 1)})
    return [[Z, e01], [e10, Z]]

def paso_elem(x, Lp):
    """x on V(x)Phi(N') (floors 0..2Lp+2) -> 4x4 over N' in the basis (A, B, C, Dd)."""
    # (v, sigma) blocks: index 2v + sigma; output floor 2f + sigma + v
    blk = [[zero(Lp) for _ in range(4)] for _ in range(4)]
    for m, t in x.c.items():
        for (vo, vi, mm) in ((0, 0, m), (1, 1, m), (1, 0, m - 1)):
            if mm < 0: continue
            S = phi_slot(mm, Lp)
            for so in (0, 1):
                coef = [t[2 * f + so + vo] if 2 * f + so + vo <= x.L else Fraction(0) for f in range(Lp + 1)]
                if not any(coef): continue
                cf = E(Lp, {0: coef})
                for si in (0, 1):
                    if S[so][si].c:
                        blk[2 * vo + so][2 * vi + si] = add(blk[2 * vo + so][2 * vi + si], mul(cf, S[so][si]))
    # basis change: rows B = 01, C = 10 + 01; cols B = 01 - 10.  index: 00 -> 0, 01 -> 1, 10 -> 2, 11 -> 3
    R = [[e.copy() for e in row] for row in blk]
    R[2] = [add(a, b) for a, b in zip(R[2], R[1])]                 # row C = row10 + row01
    for i in range(4): R[i][1] = add(R[i][1], R[i][2], -1)         # col B = col01 - col10
    return R   # order (A, B, C, Dd) = (0, 1, 2, 3)

def tree(l):
    out = []
    while l > 0:
        if l % 2 == 1: out.append('phi'); l = (l - 1) // 2
        else: out.append('vphi'); l = (l - 2) // 2
    return out

def step(G, mv, Lp):
    """G: r x r system on the current level. Returns the next system (after Schur and / 2), tray min valuation."""
    r = len(G)
    if mv == 'phi':
        B = [[doblar_elem(G[s][t], Lp) for t in range(r)] for s in range(r)]
        # pivot rows: b1 of each dancer; pivot cols: b0. remaining rows b0, cols b1.
        P = [[B[s][t][1][0] for t in range(r)] for s in range(r)]
        Bm = [[B[s][t][0][0] for t in range(r)] for s in range(r)]     # rem rows (b0) x piv cols (b0)
        Cm = [[B[s][t][1][1] for t in range(r)] for s in range(r)]     # piv rows (b1) x rem cols (b1)
        Dm = [[B[s][t][0][1] for t in range(r)] for s in range(r)]     # rem rows (b0) x rem cols (b1)
        newr = r
    else:
        B = [[paso_elem(G[s][t], Lp) for t in range(r)] for s in range(r)]
        piv_r = [(s, 1) for s in range(r)] + [(s, 3) for s in range(r)]      # B, Dd rows
        piv_c = [(s, 0) for s in range(r)] + [(s, 2) for s in range(r)]      # A, C cols
        rem_r = [(s, k) for s in range(r) for k in (0, 2)]                  # (A, C) rows, dancer-major
        rem_c = [(s, k) for s in range(r) for k in (1, 3)]                  # (B, Dd) cols
        # order pivot rows/cols so that the pivot block is lower triangular: interleave per dancer (B_s, Dd_s) x (A_s, C_s)
        piv_r = [(s, k) for s in range(r) for k in (1, 3)]
        piv_c = [(s, k) for s in range(r) for k in (0, 2)]
        ent = lambda rr, cc: B[rr[0]][cc[0]][rr[1]][cc[1]]
        P = [[ent(a, b) for b in piv_c] for a in piv_r]
        Bm = [[ent(a, b) for b in piv_c] for a in rem_r]
        Cm = [[ent(a, b) for b in rem_c] for a in piv_r]
        Dm = [[ent(a, b) for b in rem_c] for a in rem_r]
        newr = 2 * r
    Pi = minv_lower(P)
    # explicit check: the pivot block and its inverse are integral (=> invertible over Z_2)
    vP = min((v2(v) for row in P + Pi for e in row for t in e.c.values() for v in t if v != 0), default=10 ** 9)
    if vP < 0: return None, -1
    S = madd(Dm, mmul(mmul(Bm, Pi), Cm), -1)
    mv2 = min((v2(v) for row in S for e in row for t in e.c.values() for v in t if v != 0), default=10 ** 9)
    return [[smul(Fraction(1, 2), e) for e in row] for row in S], mv2

def v2(x):
    x = Fraction(x)
    if x == 0: return 10 ** 9
    a, b = x.numerator, x.denominator
    return ((abs(a) & -abs(a)).bit_length() - 1) - ((b & -b).bit_length() - 1)

def run_dance(G, l, record=None):
    """G: system on T(l) (floors 0..l). Returns (final matrix of Fractions, tray list, per-level systems if record)."""
    moves = tree(l); L = l; tray = []; levels = [G]
    for mv in moves:
        Lp = (L - 1) // 2 if mv == 'phi' else (L - 2) // 2
        G, t = step(G, mv, Lp); tray.append(t); L = Lp
        if G is None: return None, tray, levels
        levels.append(G)
        if t < 1: return None, tray, levels
    M = [[e.get(0, 0) for e in row] for row in G]
    return M, tray, levels

def sigma_elem(l, alpha, c, zeta=None):
    x = E(l, {1: [Fraction(1)] * (l + 1), 0: [Fraction(2 ** alpha * (f + c)) for f in range(l + 1)]})
    if zeta:
        for m, z in zeta.items():
            if m <= l and z: x = add(x, E(l, {m: [Fraction(z)] * (l + 1)}))
    return x
