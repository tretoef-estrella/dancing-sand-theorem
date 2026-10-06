# kclass_test.py — «Grepy el lector frío del cubo 2», checks 2 and 3 of MISSION §3.  Own code.
# Formal Borel algebra: an element is a table x[m, f] = coefficient of F^(m) at TARGET floor f (f >= m).
#   product (x y)[m, f] = sum_{a+b=m} C(m,a) x[a, f] y[b, f-a].
# Systems: arrays G[s, t, m, f] (dancers s, t).  Two backends: 'u64' (numpy uint64, exact mod 2^64, precision
# tracked through divisions by 2) and 'frac' (numpy object arrays of Fractions, exact).
# Slot matrices of F^(m) on Phi(N') and on V (x) Phi(N') are DERIVED as powers of F_Phi = [[0, 2F'], [1, 0]] and of
# F_V (x) 1 + 1 (x) F_Phi, divided by m! (exact), never copied from printed formulas.
import sys, random, itertools
import numpy as np
from fractions import Fraction
from math import comb, factorial

MOD = 1 << 64
MASK = MOD - 1
U = np.uint64
BIGV = 10 ** 6


# ---------------------------------------------------------------- scalars
def v2int(x):
    x = int(x)
    if x == 0:
        return BIGV
    return (x & -x).bit_length() - 1


def v2q(q):
    q = Fraction(q)
    if q == 0:
        return BIGV
    return v2int(q.numerator) - v2int(q.denominator)


def q2u(q):
    q = Fraction(q)
    assert q.denominator % 2 == 1, q
    return (q.numerator * pow(q.denominator, -1, MOD)) & MASK


class Ring:
    def __init__(self, kind):
        self.kind = kind
        self.dtype = np.uint64 if kind == 'u64' else object

    def zeros(self, shape):
        if self.kind == 'u64':
            return np.zeros(shape, dtype=np.uint64)
        a = np.empty(shape, dtype=object)
        a.fill(Fraction(0))
        return a

    def const(self, q):
        return U(q2u(q)) if self.kind == 'u64' else Fraction(q)

    def scal_mul(self, q, arr):
        if self.kind == 'u64':
            return arr * U(q2u(q))
        return arr * Fraction(q)

    def from_int_func(self, vals):
        if self.kind == 'u64':
            return np.array([int(v) & MASK for v in vals], dtype=np.uint64)
        return np.array([Fraction(v) for v in vals], dtype=object)

    def val(self, x, prec):
        """2-adic valuation of a scalar; >= prec counts as prec (u64)."""
        if self.kind == 'u64':
            x = int(x) & ((1 << prec) - 1)
            return prec if x == 0 else v2int(x)
        return v2q(x)

    def is_odd(self, x):
        if self.kind == 'u64':
            return int(x) & 1 == 1
        return v2q(x) == 0

    def inv_odd_vec(self, x):
        if self.kind == 'u64':
            z = x.copy()
            for _ in range(6):
                z = z * (U(2) - x * z)
            return z
        return np.array([Fraction(1) / v for v in x], dtype=object)

    def half(self, arr):
        if self.kind == 'u64':
            return arr >> U(1)
        return arr / 2

    def all_even(self, arr):
        if self.kind == 'u64':
            return not (arr & U(1)).any()
        return all(v2q(v) >= 1 for v in arr.flat)


# ---------------------------------------------------------------- formal algebra
def mask_lower(R, G):
    """zero the meaningless entries f < m."""
    L = G.shape[-1] - 1
    for m in range(1, L + 1):
        G[..., m, :m] = R.zeros(G[..., m, :m].shape)
    return G


def smul_sys(R, G, H):
    """product of systems G (r x q) and H (q x p), each entry an element table (L+1, L+1)."""
    r, q, L1, _ = G.shape
    p = H.shape[1]
    L = L1 - 1
    out = R.zeros((r, p, L1, L1))
    for a in range(L1):
        Ga = G[:, :, a, :]
        if not Ga.any():
            continue
        for b in range(L1 - a):
            m = a + b
            Hb = H[:, :, b, :]
            if not Hb.any():
                continue
            A = np.transpose(Ga[:, :, m:], (2, 0, 1))
            B = np.transpose(Hb[:, :, b:L1 - a], (2, 0, 1))
            P = np.matmul(A, B)
            c = comb(m, a)
            if R.kind == 'u64':
                out[:, :, m, m:] += np.transpose(P, (1, 2, 0)) * U(c & MASK)
            else:
                out[:, :, m, m:] += np.transpose(P, (1, 2, 0)) * c
    return out


def elem_inv(R, x):
    """inverse of one element with odd constant term at every floor."""
    L1 = x.shape[0]
    y = R.zeros(x.shape)
    x0 = x[0, :]
    for f in range(L1):
        assert R.is_odd(x0[f]), 'even constant term in an element to invert'
    i0 = R.inv_odd_vec(x0)
    y[0, :] = i0
    for m in range(1, L1):
        s = R.zeros((L1 - m,))
        for a in range(1, m + 1):
            c = comb(m, a)
            term = x[a, m:] * y[m - a, m - a:L1 - a]
            s = s + (term * (U(c & MASK) if R.kind == 'u64' else c))
        y[m, m:] = (R.zeros(s.shape) - s) * i0[m:]
    return y


def sys_inv_lower(R, P):
    r = P.shape[0]
    for i in range(r):
        for j in range(i + 1, r):
            assert not P[i, j].any(), 'pivot block not lower triangular'
    X = R.zeros(P.shape)
    D = [elem_inv(R, P[i, i]) for i in range(r)]
    for j in range(r):
        X[j, j] = D[j]
        for i in range(j + 1, r):
            acc = smul_sys(R, P[i:i + 1, j:i], X[j:i, j:j + 1])[0, 0]
            X[i, j] = R.zeros(acc.shape) - smul_sys(R, D[i][None, None], acc[None, None])[0, 0]
    return X


# ---------------------------------------------------------------- derived slot matrices
def poly_mat_mul(A, B):
    n, k, p = len(A), len(B), len(B[0])
    C = [[{} for _ in range(p)] for _ in range(n)]
    for i in range(n):
        for j in range(p):
            acc = {}
            for t in range(k):
                for e1, c1 in A[i][t].items():
                    for e2, c2 in B[t][j].items():
                        acc[e1 + e2] = acc.get(e1 + e2, 0) + c1 * c2
            C[i][j] = {e: c for e, c in acc.items() if c != 0}
    return C


def divided(Mpow, m):
    """Mpow = (F_gen)^m with entries polynomials in ordinary powers of F'; return entries dict q -> coeff of F'^(q)."""
    out = []
    for row in Mpow:
        orow = []
        for ent in row:
            d = {}
            for e, c in ent.items():
                q = Fraction(c) * factorial(e) / factorial(m)
                assert q.denominator % 2 == 1, ('even denominator in a slot', m, e, q)
                d[e] = q
            orow.append(d)
        out.append(orow)
    return out


_SLOT2, _SLOT4 = {}, {}


def slot2(m):
    if m not in _SLOT2:
        FP = [[{}, {1: 2}], [{0: 1}, {}]]
        Mp = [[{0: 1}, {}], [{}, {0: 1}]]
        for _ in range(m):
            Mp = poly_mat_mul(FP, Mp)
        _SLOT2[m] = divided(Mp, m)
    return _SLOT2[m]


def slot4(m):
    """index 2v + sigma; rows = output."""
    if m not in _SLOT4:
        FP = [[{}, {1: 2}], [{0: 1}, {}]]
        F4 = [[{} for _ in range(4)] for _ in range(4)]
        for v in range(2):
            for so in range(2):
                for si in range(2):
                    if FP[so][si]:
                        F4[2 * v + so][2 * v + si] = dict(FP[so][si])
        for s in range(2):
            F4[2 + s][s] = {0: 1}
        Mp = [[({0: 1} if i == j else {}) for j in range(4)] for i in range(4)]
        for _ in range(m):
            Mp = poly_mat_mul(F4, Mp)
        _SLOT4[m] = divided(Mp, m)
    return _SLOT4[m]


def closed_slot2(m):
    def dfo(s):
        r = 1
        for t in range(1, 2 * s, 2):
            r *= t
        return r
    if m % 2 == 0:
        q = m // 2
        e = {q: Fraction(1, dfo(q))}
        return [[e, {}], [{}, e]]
    q = (m - 1) // 2
    return [[{}, {q + 1: Fraction(2 * q + 2, dfo(q + 1))}], [{q: Fraction(1, dfo(q + 1))}, {}]]


# ---------------------------------------------------------------- moves
def split_elem2(R, x, Lp):
    """element on Phi(N') (floors 0..>=2Lp+1) -> blocks[so][si] tables over N' (floors 0..Lp)."""
    L1 = x.shape[0]
    blk = [[R.zeros((Lp + 1, Lp + 1)) for _ in range(2)] for _ in range(2)]
    for m in range(L1):
        if not x[m].any():
            continue
        S = slot2(m)
        for so in range(2):
            tgt = [2 * f + so for f in range(Lp + 1)]
            coef = np.array([x[m, t] if t < L1 else (U(0) if R.kind == 'u64' else Fraction(0)) for t in tgt], dtype=R.dtype)
            for si in range(2):
                for q, cq in S[so][si].items():
                    if q <= Lp:
                        blk[so][si][q, :] += R.scal_mul(cq, coef)
    for so in range(2):
        for si in range(2):
            mask_lower(R, blk[so][si])
    return blk


def split_elem4(R, x, Lp):
    """element on V (x) Phi(N') (floors 0..>=2Lp+2) -> 4x4 blocks over N' (index 2v+sigma)."""
    L1 = x.shape[0]
    blk = [[R.zeros((Lp + 1, Lp + 1)) for _ in range(4)] for _ in range(4)]
    for m in range(L1):
        if not x[m].any():
            continue
        S = slot4(m)
        for io in range(4):
            vo, so = divmod(io, 2)
            tgt = [2 * f + so + vo for f in range(Lp + 1)]
            coef = np.array([x[m, t] if t < L1 else (U(0) if R.kind == 'u64' else Fraction(0)) for t in tgt], dtype=R.dtype)
            for ii in range(4):
                for q, cq in S[io][ii].items():
                    if q <= Lp:
                        blk[io][ii][q, :] += R.scal_mul(cq, coef)
    for io in range(4):
        for ii in range(4):
            mask_lower(R, blk[io][ii])
    return blk


def schur(R, P, Bm, Cm, Dm, prec):
    """returns (G_next, info) ; info['clean'] etc."""
    r = P.shape[0]
    info = {}
    for i in range(r):
        if not all(R.is_odd(v) for v in P[i, i, 0, :]):
            info['clean'] = False; info['why'] = 'pivot diagonal not odd'
            return None, info
    Pi = sys_inv_lower(R, P)
    S = Dm - smul_sys(R, smul_sys(R, Bm, Pi), Cm)
    mask_lower(R, S)
    if R.kind == 'u64':
        ok = R.all_even(S)
    else:
        ok = R.all_even(S)
    if not ok:
        info['clean'] = False; info['why'] = 'Schur complement not even'
        return None, info
    info['clean'] = True
    return R.half(S), info


def move_doblar(R, G, Lp, prec):
    r = G.shape[0]
    blks = [[split_elem2(R, G[s, t], Lp) for t in range(r)] for s in range(r)]
    sh = (r, r, Lp + 1, Lp + 1)
    P, Bm, Cm, Dm = R.zeros(sh), R.zeros(sh), R.zeros(sh), R.zeros(sh)
    for s in range(r):
        for t in range(r):
            b = blks[s][t]
            P[s, t] = b[1][0]; Bm[s, t] = b[0][0]; Cm[s, t] = b[1][1]; Dm[s, t] = b[0][1]
    return schur(R, P, Bm, Cm, Dm, prec)


def vsplit(R, G):
    """system on V (x) M (floors 0..L) -> system on M (floors 0..L-1), dancers [(s,0) all] + [(s,1) all]."""
    r, _, L1, _ = G.shape
    LM1 = L1 - 1
    H = R.zeros((2 * r, 2 * r, LM1, LM1))
    for s in range(r):
        for t in range(r):
            x = G[s, t]
            H[s, t] = x[:LM1, :LM1]                     # (0,0): x_m at floor g
            H[r + s, r + t] = x[:LM1, 1:L1]             # (1,1): x_m at floor g+1
            y = R.zeros((LM1, LM1))
            # (1,0): coefficient of F^(m-1) at M-floor g is x_m(g+1)
            for m in range(1, L1):
                if m - 1 < LM1:
                    y[m - 1, :] = x[m, 1:L1]
            H[r + s, t] = y
    mask_lower(R, H)
    return H


def move_paso_split(R, G, Lp, prec):
    H = vsplit(R, G)
    return move_doblar(R, H, Lp, prec)


def move_paso_abcd(R, G, Lp, prec):
    r = G.shape[0]
    blks = [[split_elem4(R, G[s, t], Lp) for t in range(r)] for s in range(r)]
    # basis change: row C = row10 + row01 ; col B = col01 - col10   (indices 00:0, 01:1, 10:2, 11:3)
    for s in range(r):
        for t in range(r):
            b = blks[s][t]
            for j in range(4):
                b[2][j] = b[2][j] + b[1][j]
            for i in range(4):
                b[i][1] = b[i][1] - b[i][2]
    piv_r = [(s, k) for s in range(r) for k in (1, 3)]
    piv_c = [(s, k) for s in range(r) for k in (0, 2)]
    rem_r = [(s, k) for s in range(r) for k in (0, 2)]
    rem_c = [(s, k) for s in range(r) for k in (1, 3)]
    n2 = 2 * r
    sh = (n2, n2, Lp + 1, Lp + 1)
    P, Bm, Cm, Dm = R.zeros(sh), R.zeros(sh), R.zeros(sh), R.zeros(sh)
    for i, a in enumerate(piv_r):
        for j, b in enumerate(piv_c):
            P[i, j] = blks[a[0]][b[0]][a[1]][b[1]]
        for j, b in enumerate(rem_c):
            Cm[i, j] = blks[a[0]][b[0]][a[1]][b[1]]
    for i, a in enumerate(rem_r):
        for j, b in enumerate(piv_c):
            Bm[i, j] = blks[a[0]][b[0]][a[1]][b[1]]
        for j, b in enumerate(rem_c):
            Dm[i, j] = blks[a[0]][b[0]][a[1]][b[1]]
    return schur(R, P, Bm, Cm, Dm, prec)


def abcd_to_split_order(r):
    """ABCD output order [(s,A),(s,C) for s] -> split order [(s,0) all] + [(s,1) all]: perm[i_abcd] = i_split."""
    perm = []
    for s in range(r):
        perm.append(s)
        perm.append(r + s)
    return perm


def tree(l):
    out = []
    while l > 0:
        if l % 2 == 1:
            out.append('phi'); l = (l - 1) // 2
        else:
            out.append('vphi'); l = (l - 2) // 2
    return out


# ---------------------------------------------------------------- the class K: functions and tests
def kfunc(a, cs):
    """phi(y) = a + 2 * sum_k c_k (2y)^k  (cs = [c_1, c_2, ...])."""
    def phi(y):
        return a + 2 * sum(c * (2 * y) ** (k + 1) for k, c in enumerate(cs))
    return phi


def rD(D):
    return sum(1 << t for t in D)


def ktest_points(R, pts, h, prec):
    """pts: list of (y, value, dancer_key, f). Returns (ok_pair, ok_mahler, n_skipped)."""
    okp = True; okm = True; skipped = 0
    n = len(pts)
    for i in range(n):
        yi, xi = pts[i][0], pts[i][1]
        for j in range(i + 1, n):
            yj, xj = pts[j][0], pts[j][1]
            need = 2 + v2int(yi - yj)
            if need >= prec:
                skipped += 1; continue
            d = (xi - xj) if R.kind == 'frac' else ((int(xi) - int(xj)) & MASK)
            if R.val(d, prec) < need:
                okp = False
    # Mahler along each dancer's progression (consecutive floors, step 2^h in y)
    bykey = {}
    for (y, x, key, f) in pts:
        bykey.setdefault(key, []).append((f, x))
    for key, lst in bykey.items():
        lst.sort()
        fs = [f for f, _ in lst]
        if fs != list(range(fs[0], fs[0] + len(fs))):
            continue
        seq = [x for _, x in lst]
        diffs = seq
        for j in range(1, len(seq)):
            if R.kind == 'frac':
                diffs = [diffs[i + 1] - diffs[i] for i in range(len(diffs) - 1)]
            else:
                diffs = [(int(diffs[i + 1]) - int(diffs[i])) & MASK for i in range(len(diffs) - 1)]
            need = 1 + j * (h + 1) + v2int(factorial(j))
            if need >= prec:
                skipped += 1; continue
            if R.val(diffs[0], prec) < need:
                okm = False
    return okp, okm, skipped


def check_class(R, G, dancers, h, c, prec, want_ab=True):
    """G: system at level h with dancers (frozensets). Checks Boolean triangularity, K-test per (Delta, m), (a), (b)."""
    r, _, L1, _ = G.shape
    res = {'tri': True, 'pair': True, 'mahler': True, 'a': True, 'b': True, 'skipped': 0}
    groups = {}
    for s in range(r):
        for t in range(r):
            Ds, Dt = dancers[s], dancers[t]
            if not Dt <= Ds:
                if G[s, t].any():
                    res['tri'] = False
                continue
            Delta = frozenset(Ds - Dt)
            for m in range(L1):
                for f in range(m, L1):
                    y = (1 << h) * f + rD(Ds) + c
                    groups.setdefault((Delta, m), []).append((y, G[s, t, m, f], s, f))
    for key, pts in groups.items():
        okp, okm, sk = ktest_points(R, pts, h, prec)
        res['pair'] &= okp; res['mahler'] &= okm; res['skipped'] += sk
    if want_ab:
        for s in range(r):
            for f in range(L1):
                if R.val(G[s, s, 0, f], prec) < 2:
                    res['a'] = False
            for f in range(1, L1):
                if not R.is_odd(G[s, s, 1, f]):
                    res['b'] = False
    return res


# ---------------------------------------------------------------- random systems in T_h
def random_system(R, rng, h, P_h, L, c, ctrl=None):
    dancers = sorted([frozenset(S) for k in range(len(P_h) + 1) for S in itertools.combinations(P_h, k)], key=rD)
    r = len(dancers)
    funcs = {}
    deltas = set()
    for s in range(r):
        for t in range(r):
            if dancers[t] <= dancers[s]:
                deltas.add(frozenset(dancers[s] - dancers[t]))
    for Delta in deltas:
        for m in range(L + 1):
            K = rng.randint(1, 4)
            cs = [rng.randint(-20, 20) for _ in range(K)]
            a = rng.randint(-20, 20)
            if not Delta and m == 0:
                a = 4 * rng.randint(-5, 5)
            if not Delta and m == 1:
                a = 2 * rng.randint(-10, 10) + 1
            funcs[(Delta, m)] = kfunc(a, cs)
    if ctrl == 'pay2y':
        u = kfunc(2 * rng.randint(-5, 5) + 1, [rng.randint(-5, 5)])
        funcs[(frozenset(), 0)] = (lambda u: (lambda y: 2 * y * u(y)))(u)
    G = R.zeros((r, r, L + 1, L + 1))
    bad_key = None
    if ctrl == 'nonK':
        cand = [k for k in funcs if k[0] and k[1] <= 2]
        if cand:
            bad_key = rng.choice(sorted(cand, key=lambda k: (rD(k[0]), k[1])))
    for s in range(r):
        for t in range(r):
            if not dancers[t] <= dancers[s]:
                continue
            Delta = frozenset(dancers[s] - dancers[t])
            for m in range(L + 1):
                phi = funcs[(Delta, m)]
                vals = []
                for f in range(L + 1):
                    if f < m:
                        vals.append(0); continue
                    y = (1 << h) * f + rD(dancers[s]) + c
                    v = phi(y)
                    if bad_key is not None and (Delta, m) == bad_key and y % 2 != 0:
                        v += 2
                    vals.append(v)
                G[s, t, m, :] = R.from_int_func(vals)
    return G, dancers


# ---------------------------------------------------------------- level-0 operators
def bernoulli(N):
    B = [Fraction(0)] * (N + 1)
    B[0] = Fraction(1)
    for n in range(1, N + 1):
        B[n] = -sum(comb(n + 1, k) * B[k] for k in range(n)) / (n + 1)
    return B


_BER = bernoulli(140)


def dfo(s):
    r = 1
    for t in range(1, 2 * s, 2):
        r *= t
    return r


def weights(kind, L, rng=None):
    """constant coefficients of F^(n), n >= 1."""
    w = {}
    for n in range(1, L + 1):
        if kind == 'tanh':
            w[n] = Fraction(2 * (2 ** (2 * n) - 1)) * _BER[2 * n] / dfo(n)
        elif kind == 'coth':
            w[n] = Fraction(2) * _BER[2 * n] / dfo(n)
        elif kind == 'cothN':
            w[n] = Fraction(2) * _BER[2 * n] / dfo(n) * 3 ** n
        elif kind == 'rand':
            w[n] = Fraction(1) if n == 1 else Fraction(rng.randint(-9, 9))
        elif kind == 'sigma':
            w[n] = Fraction(1) if n == 1 else Fraction(0)
        elif kind == 'sigma3':
            w[n] = Fraction(1, 3) if n == 1 else Fraction(0)
        else:
            raise ValueError(kind)
    return w


def level0(R, L, c, wts, alpha=2, payshift=0, Fodd=None):
    G = R.zeros((1, 1, L + 1, L + 1))
    G[0, 0, 0, :] = R.from_int_func([(2 ** alpha) * (f + c) + payshift for f in range(L + 1)])
    for n, q in wts.items():
        if n <= L and q != 0:
            G[0, 0, n, n:] = R.const(q)
    if Fodd is not None:
        G[0, 0, 1, 1:] = R.from_int_func(Fodd[1:L + 1])
    mask_lower(R, G)
    return G


def run_dance(R, G0, l, c, check=True, compare=True):
    """dance along tree(l). Returns dict with final matrix, per-level class results, first break."""
    word = tree(l)
    G, dancers, h, L, prec = G0, [frozenset()], 0, l, 64
    rep = {'levels': [], 'break': None, 'paso_equal': True}
    for mv in word:
        if mv == 'phi':
            Lp = (L - 1) // 2
            Gn, info = move_doblar(R, G, Lp, prec)
            nd = dancers
        else:
            Lp = (L - 2) // 2
            Gn, info = move_paso_split(R, G, Lp, prec)
            if compare and Gn is not None:
                Ga, infoa = move_paso_abcd(R, G, Lp, prec)
                if Ga is None:
                    rep['paso_equal'] = False
                else:
                    r = len(dancers)
                    perm = abcd_to_split_order(r)
                    inv = [0] * len(perm)
                    for i, p in enumerate(perm):
                        inv[p] = i
                    Gp = Ga[np.ix_(inv, inv)]
                    if R.kind == 'u64':
                        mk = U((1 << (prec - 1)) - 1)
                        same = np.array_equal(Gp & mk, Gn & mk)
                    else:
                        same = all(a == b for a, b in zip(Gp.flat, Gn.flat))
                    if not same:
                        rep['paso_equal'] = False
            nd = dancers + [d | {h} for d in dancers]
        if Gn is None:
            rep['break'] = (h, mv, info.get('why'))
            return rep
        prec -= 1
        h += 1; L = Lp; G = Gn
        order = sorted(range(len(nd)), key=lambda i: rD(nd[i]))
        G = G[np.ix_(order, order)]
        dancers = [nd[i] for i in order]
        if check:
            res = check_class(R, G, dancers, h, c, prec)
            rep['levels'].append(res)
    rep['M'] = G[:, :, 0, 0].copy()
    rep['dancers'] = dancers
    rep['prec'] = prec
    rep['k'] = h
    return rep


def class_ok(res):
    return res['tri'] and res['pair'] and res['mahler'] and res['a'] and res['b']


# ---------------------------------------------------------------- modes
def mode_slots():
    bad = 0
    for m in range(0, 31):
        a, b = slot2(m), closed_slot2(m)
        for i in range(2):
            for j in range(2):
                if {q: c for q, c in a[i][j].items() if c} != b[i][j]:
                    bad += 1
                    print('  slot mismatch', m, i, j, a[i][j], b[i][j])
    print(f'S2.0a derived slot matrices (powers of F_Phi / m!) vs FLIGHT2 A.1(b) closed formulas, m = 0..30: {"ALL EQUAL" if bad == 0 else f"{bad} MISMATCHES"}')
    # V (x) Phi slots: compare with (1 (x) F_Phi^(m) + F_V (x) F_Phi^(m-1)) built from slot2
    bad4 = 0
    for m in range(0, 21):
        S4 = slot4(m)
        for io in range(4):
            vo, so = divmod(io, 2)
            for ii in range(4):
                vi, si = divmod(ii, 2)
                exp = {}
                if vo == vi:
                    exp = dict(slot2(m)[so][si])
                elif vo == 1 and vi == 0 and m >= 1:
                    exp = dict(slot2(m - 1)[so][si])
                got = {q: cq for q, cq in S4[io][ii].items() if cq}
                exp = {q: cq for q, cq in exp.items() if cq}
                if got != exp:
                    bad4 += 1
    print(f'S2.0a V(x)Phi slots from (F_V(x)1 + 1(x)F_Phi)^m/m! vs 1(x)F_Phi^(m) + F_V(x)F_Phi^(m-1), m = 0..20: {"ALL EQUAL" if bad4 == 0 else f"{bad4} MISMATCHES"}')


def mode_ktest():
    R = Ring('frac')
    cases = [('4y (real payment)', lambda y: 4 * y, True), ('2y(y-1) = 4C(y,2)', lambda y: 2 * y * (y - 1), False),
             ('2y (alpha = 1)', lambda y: 2 * y, False), ('3 + 8y^2 + 4y', lambda y: 3 + 8 * y * y + 4 * y, True),
             ('4y + 2[y odd]', lambda y: 4 * y + 2 * (y % 2), False), ('1/(1+4y) (odd unit in K)', lambda y: Fraction(1, 1 + 4 * y), True)]
    allok = True
    for name, phi, expect in cases:
        pts = [(f + 3, Fraction(phi(f + 3)), 0, f) for f in range(0, 12)]
        okp, okm, sk = ktest_points(R, pts, 0, 10 ** 9)
        acc = okp and okm
        allok &= (acc == expect)
        print(f'S2.0c K-test on {name}: pair {okp}, Mahler {okm} -> {"accepted" if acc else "rejected"} (expected {"accept" if expect else "reject"})')
    print(f'S2.0c the K-test separates as expected: {allok}')


# explicit lattices ------------------------------------------------
def explicit_T(l):
    """returns (floors list, list Fd[m] of Fraction matrices for F^(m), m = 0..l)."""
    if l == 0:
        return [0], None
    word = tree(l)
    # build bottom-up: list of moves from the bottom
    seq = []
    x = l
    while x > 0:
        if x % 2 == 1:
            seq.append('phi'); x = (x - 1) // 2
        else:
            seq.append('vphi'); x = (x - 2) // 2
    seq.reverse()
    floors = [0]
    Fmat = np.zeros((1, 1), dtype=object); Fmat[0, 0] = Fraction(0)
    for mv in seq:
        d = len(floors)
        # Phi
        Fp = np.empty((2 * d, 2 * d), dtype=object); Fp.fill(Fraction(0))
        Fp[d:, :d] = np.eye(d, dtype=int).astype(object)
        Fp[:d, d:] = 2 * Fmat
        fl = [2 * g for g in floors] + [2 * g + 1 for g in floors]
        Fmat, floors = Fp, fl
        if mv == 'vphi':
            d = len(floors)
            Fv = np.empty((2 * d, 2 * d), dtype=object); Fv.fill(Fraction(0))
            Fv[:d, :d] = Fmat; Fv[d:, d:] = Fmat
            Fv[d:, :d] = np.eye(d, dtype=int).astype(object)
            Fmat = Fv
            floors = floors + [g + 1 for g in floors]
    d = len(floors)
    Fd = []
    P = np.empty((d, d), dtype=object); P.fill(Fraction(0))
    for i in range(d):
        P[i, i] = Fraction(1)
    top = max(floors)
    for m in range(0, top + 1):
        if m > 0:
            P = P.dot(Fmat)
        Fd.append(P / factorial(m))
    return floors, Fd


def explicit_operator(floors, Fd, coeff):
    """coeff(m, target_floor) -> Fraction. Returns the matrix of sum_m coeff(m, D) F^(m)."""
    d = len(floors)
    A = np.empty((d, d), dtype=object); A.fill(Fraction(0))
    for m, Fm in enumerate(Fd):
        for j in range(d):
            for i in range(d):
                if Fm[i, j] != 0:
                    A[i, j] += coeff(m, floors[i]) * Fm[i, j]
    return A


def smith_frac(A):
    sys.path.insert(0, 'engines')
    from law_direct import smith2
    M = np.zeros(A.shape, dtype=np.uint64)
    for i in range(A.shape[0]):
        for j in range(A.shape[1]):
            M[i, j] = q2u(A[i, j])
    return smith2(M)


def mode_lattice(lmax):
    R = Ring('u64')
    tot = ok = 0
    bad_int = 0
    for l in range(1, lmax + 1):
        floors, Fd = explicit_T(l)
        for Fm in Fd:
            for v in Fm.flat:
                if Fraction(v).denominator % 2 == 0:
                    bad_int += 1
        for kind in ('sigma', 'tanh', 'coth'):
            for j in range(0, 5):
                c = (j + 1) // 2
                if kind == 'sigma':
                    wts = weights('sigma', l); pay = lambda f: 4 * (f + c)
                elif kind == 'tanh':
                    if j % 2: continue
                    wts = weights('tanh', l); pay = lambda f: 4 * (f + c)
                else:
                    if j % 2 == 0: continue
                    wts = weights('coth', l); pay = lambda f: 4 * (f + c)
                coeff = lambda m, f: Fraction(pay(f)) if m == 0 else wts.get(m, Fraction(0))
                A = explicit_operator(floors, Fd, coeff)
                ex_direct = sorted(e for e in smith_frac(A))
                G0 = level0(R, l, c, wts)
                rep = run_dance(R, G0, l, c, check=False, compare=False)
                if rep['break'] is not None:
                    print(f'  l={l} {kind} j={j}: dance broke {rep["break"]}'); tot += 1; continue
                k = rep['k']
                # small clocks: at move h, number of pivots = half the dimension at that level
                small = []
                dim = len(floors)
                for hh in range(k):
                    small += [hh] * (dim // 2)
                    dim //= 2
                Mm = rep['M']
                from law_direct import smith2
                exM = smith2(Mm.copy())
                prec = rep['prec']
                big = [k + e if e < prec else 64 for e in exM]
                ex_dance = sorted(small + big)
                ex_direct = [e if e < prec + k else 64 for e in ex_direct]
                tot += 1
                same = ex_dance == sorted(ex_direct)
                ok += same
                if not same:
                    print(f'  MISMATCH l={l} {kind} j={j}: direct {sorted(ex_direct)} dance {ex_dance}')
    print(f'S2.0b explicit T(l) divided powers 2-adically integral: {"yes" if bad_int == 0 else f"NO ({bad_int} entries)"}')
    print(f'S2.0b direct Smith on explicit T(l) = small clocks + (k + Smith of my final matrix), l <= {lmax}: {ok}/{tot}')


def mode_onemove(ntr, seed):
    R = Ring('u64')
    rng = random.Random(seed)
    stats = {}
    def bump(key, good):
        a = stats.setdefault(key, [0, 0]); a[0] += 1; a[1] += good
    for trial in range(ntr):
        h = rng.randint(0, 3)
        P_h = sorted(rng.sample(range(h), rng.randint(0, min(2, h)))) if h > 0 else []
        c = rng.randint(-7, 20)
        for mv in ('phi', 'vphi'):
            Lp = rng.randint(3, 5)
            L = 2 * Lp + 1 if mv == 'phi' else 2 * Lp + 2
            for ctrl in (None, 'pay2y', 'nonK'):
                G, dancers = random_system(R, rng, h, P_h, L, c, ctrl=ctrl)
                inres = check_class(R, G, dancers, h, c, 64)
                if ctrl is None and not class_ok(inres):
                    bump('input-not-in-class (generator bug)', 0)
                if mv == 'phi':
                    Gn, info = move_doblar(R, G, Lp, 64)
                    nd = dancers
                else:
                    Gn, info = move_paso_split(R, G, Lp, 64)
                    nd = dancers + [d | {h} for d in dancers]
                if Gn is not None and mv == 'vphi':
                    Ga, _ = move_paso_abcd(R, G, Lp, 64)
                    r = len(dancers)
                    perm = abcd_to_split_order(r)
                    inv = [0] * len(perm)
                    for i, p in enumerate(perm):
                        inv[p] = i
                    mk = U((1 << 63) - 1)
                    same = Ga is not None and np.array_equal(Ga[np.ix_(inv, inv)] & mk, Gn & mk)
                    bump(f'S2.2 paso split == paso ABCD [{ctrl}]', same)
                if Gn is None:
                    bump(f'clean+class [{mv}] [{ctrl}]', 0)
                    bump(f'clean [{mv}] [{ctrl}]', 0)
                    continue
                bump(f'clean [{mv}] [{ctrl}]', 1)
                order = sorted(range(len(nd)), key=lambda i: rD(nd[i]))
                Gn = Gn[np.ix_(order, order)]
                ndd = [nd[i] for i in order]
                res = check_class(R, Gn, ndd, h + 1, c, 63)
                bump(f'clean+class [{mv}] [{ctrl}]', class_ok(res))
                if ctrl is not None:
                    bump(f'  input in class [{mv}] [{ctrl}]', class_ok(inres))
                    for kk in ('a', 'b', 'pair', 'mahler'):
                        bump(f'  output passes {kk} [{mv}] [{ctrl}]', res[kk])
                if ctrl is None and not class_ok(res) and stats.get('_shown', 0) < 5:
                    stats['_shown'] = stats.get('_shown', 0) + 1
                    print(f'  in-class FAILURE trial {trial} {mv} h={h} P={P_h} c={c}: {res}')
    for k in sorted(x for x in stats if not x.startswith('_')):
        n, g = stats[k]
        print(f'{k}: {g}/{n}')


def mode_depth(lmin, lmax, cmax, seed):
    R = Ring('u64')
    rng = random.Random(seed)
    stats = {}
    first_break = {}
    for l in range(lmin, lmax + 1):
        for c in range(0, cmax + 1):
            for kind in ('tanh', 'coth', 'cothN', 'rand', 'C2b_alpha1_z2odd', 'C2c_oddF_weights', 'C2e_oddF_noweights'):
                if kind in ('tanh', 'coth', 'cothN'):
                    G0 = level0(R, l, c, weights(kind, l))
                elif kind == 'rand':
                    G0 = level0(R, l, c, weights('rand', l, rng))
                elif kind == 'C2b_alpha1_z2odd':
                    w = weights('rand', l, rng)
                    if l >= 2: w[2] = Fraction(2 * rng.randint(-4, 4) + 1)
                    G0 = level0(R, l, c, w, alpha=1)
                elif kind == 'C2c_oddF_weights':
                    w = weights('rand', l, rng)
                    if l >= 2 and w[2] == 0: w[2] = Fraction(1)
                    Fodd = [2 * rng.randint(-50, 50) + 1 for _ in range(l + 1)]
                    G0 = level0(R, l, c, w, Fodd=Fodd)
                else:
                    Fodd = [2 * rng.randint(-50, 50) + 1 for _ in range(l + 1)]
                    G0 = level0(R, l, c, weights('sigma', l), Fodd=Fodd)
                is_ctrl = kind.startswith('C2')
                rep = run_dance(R, G0, l, c, check=not is_ctrl, compare=not is_ctrl)
                clean = rep['break'] is None
                a = stats.setdefault(kind, [0, 0, 0, 0])
                a[0] += 1; a[1] += clean
                if not is_ctrl:
                    allcls = clean and all(class_ok(x) for x in rep['levels'])
                    a[2] += allcls
                    a[3] += rep['paso_equal']
                    if not allcls and a[0] - a[2] <= 3:
                        print(f'  {kind} l={l} c={c}: break={rep["break"]} levels={[ {k:v for k,v in x.items() if v is not True} for x in rep["levels"]]}')
                else:
                    if not clean and kind not in first_break:
                        first_break[kind] = (l, c, rep['break'])
    for kind, (n, cl, cls, pe) in stats.items():
        if kind.startswith('C2'):
            print(f'{kind}: clean in {cl}/{n} dances (control: breaks in {n - cl}); first break {first_break.get(kind)}')
        else:
            print(f'{kind}: clean {cl}/{n}; clean AND in class at every level {cls}/{n}; paso split == ABCD at every paso {pe}/{n}')


# ---------------------------------------------------------------- check 3: Lemma B (exact rationals)
def elem_inv_q(x):
    """inverse over Q of one element (object array of Fractions) with non-zero constant terms."""
    L1 = x.shape[0]
    y = np.empty(x.shape, dtype=object); y.fill(Fraction(0))
    for f in range(L1):
        assert x[0, f] != 0
        y[0, f] = Fraction(1) / x[0, f]
    for m in range(1, L1):
        for f in range(m, L1):
            sm = Fraction(0)
            for a in range(1, m + 1):
                xa = x[a, f]
                if xa:
                    sm += comb(m, a) * xa * y[m - a, f - a]
            y[m, f] = -sm * y[0, f]
    return y


def mat_inv_q(M):
    n = M.shape[0]
    A = [[Fraction(M[i, j]) for j in range(n)] + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next(i for i in range(col, n) if A[i][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [v / pv for v in A[col]]
        for i in range(n):
            if i != col and A[i][col] != 0:
                fct = A[i][col]
                A[i] = [a - fct * b for a, b in zip(A[i], A[col])]
    out = np.empty((n, n), dtype=object)
    for i in range(n):
        for j in range(n):
            out[i, j] = A[i][n + j]
    return out


def mat_mul_q(A, B):
    n, k = A.shape; p = B.shape[1]
    out = np.empty((n, p), dtype=object)
    for i in range(n):
        for j in range(p):
            out[i, j] = sum((A[i, t] * B[t, j] for t in range(k)), Fraction(0))
    return out


def vmin(M):
    return min((v2q(v) for v in M.flat if v != 0), default=BIGV)


def delta_cost(Delta, k):
    if not Delta:
        return 0
    return k - len(Delta) - min(Delta)


def route2(Minv_sigma, inv_plus, inv_sigma, dancers, k):
    """Lemma IB directly: N[D', D''] = (M_Sigma^-1)[D', D''] * y^{Psi+-}_{c-r}(c) / y^Sigma_{c-r}(c)."""
    r = len(dancers)
    N = np.empty((r, r), dtype=object); N.fill(Fraction(0))
    for a in range(r):          # D' : column dancer of M (domain)
        for b in range(r):      # D'': row dancer of M (codomain)
            Dp, Dpp = dancers[a], dancers[b]
            if not Dpp <= Dp:
                continue
            f = rD(Dp) + (1 << k) - 1
            mm = f - rD(Dpp)
            ys = inv_sigma[mm, f]
            assert ys != 0
            N[a, b] = Minv_sigma[a, b] * inv_plus[mm, f] / ys
    return N


def mode_lemmaB(lmax, cmax, seed):
    R = Ring('frac')
    rng = random.Random(seed)
    st = {}
    def bump(key, good):
        a = st.setdefault(key, [0, 0]); a[0] += 1; a[1] += bool(good)
    shown = 0
    for l in range(1, lmax + 1):
        for c in range(1, cmax + 1):
            for kind in ('tanh', 'coth', 'rand', 'C3a_alpha1', 'C3b_plus4'):
                alpha = 1 if kind == 'C3a_alpha1' else 2
                if kind in ('tanh', 'coth'):
                    wts = weights(kind, l)
                elif kind == 'C3a_alpha1':
                    wts = weights('sigma', l)
                else:
                    wts = weights('rand', l, rng)
                a1 = wts.get(1, Fraction(1))
                sig = {n: (a1 if n == 1 else Fraction(0)) for n in range(1, l + 1)}
                G0 = level0(R, l, c, wts, alpha=alpha)
                S0 = level0(R, l, c, sig, alpha=alpha)
                repA = run_dance(R, G0, l, c, check=False, compare=False)
                repS = run_dance(R, S0, l, c, check=False, compare=False)
                if repA['break'] is not None or repS['break'] is not None:
                    bump(f'{kind}: dances clean (else skipped)', 0); continue
                bump(f'{kind}: dances clean (else skipped)', 1)
                M, Ms, dancers, k = repA['M'], repS['M'], repA['dancers'], repA['k']
                Minv, Msinv = mat_inv_q(M), mat_inv_q(Ms)
                X = G0[0, 0]
                inv_sig = elem_inv_q(S0[0, 0])
                for sign in (+1, -1):
                    shift = 4 if kind == 'C3b_plus4' else 2
                    Xs = X.copy(); Xs[0, :] = Xs[0, :] + sign * shift
                    if any(v == 0 for v in Xs[0, :]):
                        bump(f'{kind} sign {"+" if sign > 0 else "-"}: skipped (Psi +- shift has a zero payment)', 0)
                        continue
                    inv_p = elem_inv_q(Xs)
                    N2 = route2(Msinv, inv_p, inv_sig, dancers, k)
                    MN = mat_mul_q(M, N2)
                    tag = f'{kind} sign {"+" if sign > 0 else "-"}'
                    bump(f'{tag}: M(Psi) N in 2 Mat', vmin(MN) >= 1)
                    if kind in ('C3a_alpha1', 'C3b_plus4'):
                        continue
                    # route (i): dance of Psi(Psi +- 2)/2
                    X2 = smul_sys(R, G0, G0)[0, 0]
                    Y = (X2 + 2 * sign * X) / 2
                    Gy = np.empty((1, 1) + Y.shape, dtype=object); Gy[0, 0] = Y
                    repY = run_dance(R, Gy, l, c, check=False, compare=False)
                    if repY['break'] is not None:
                        bump(f'{tag}: dance of Psi(Psi+-2)/2 clean', 0); continue
                    bump(f'{tag}: dance of Psi(Psi+-2)/2 clean', 1)
                    MY = repY['M']
                    MYinv = mat_inv_q(MY)
                    N1 = (Minv - MYinv) if sign > 0 else (MYinv + Minv)
                    same = all(a == b for a, b in zip(N1.flat, N2.flat))
                    bump(f'{tag}: route (i) == route (ii) exactly', same)
                    W = mat_mul_q(MY, Minv)
                    Iw = np.empty(W.shape, dtype=object); Iw.fill(Fraction(0))
                    for i in range(W.shape[0]):
                        Iw[i, i] = Fraction(sign)
                    bump(f'{tag}: W = M(Psi(Psi+-2)/2) M(Psi)^-1 in {"+" if sign > 0 else "-"}I + 2Mat', vmin(W - Iw) >= 1)
                    # entrywise window bound
                    wv = lambda d: 1 + v2int(d + c)
                    okb = True
                    r = len(dancers)
                    for i in range(r):
                        for j in range(r):
                            D, Dpp = dancers[i], dancers[j]
                            if not Dpp <= D:
                                if MN[i, j] != 0: okb = False
                                continue
                            bound = BIGV
                            for t in range(r):
                                Dp = dancers[t]
                                if Dpp <= Dp <= D:
                                    Wsum = sum(wv(d) for d in range(rD(D), rD(Dp) + (1 << k)))
                                    bound = min(bound, delta_cost(D - Dp, k) + delta_cost(Dp - Dpp, k) + Wsum)
                            if MN[i, j] != 0 and v2q(MN[i, j]) < bound:
                                okb = False
                    bump(f'{tag}: entrywise window bound', okb)
                    if not okb and shown < 3:
                        shown += 1; print(f'  window bound violated: l={l} c={c} {tag}')
    for key in sorted(st):
        n, g = st[key]
        print(f'{key}: {g}/{n}')


# ---------------------------------------------------------------- extra: the family law on my explicit lattices
def mode_family(lmax, imax):
    tot = ok = 0
    c0 = []
    c_sign = [0, 0]
    for lam in range(0, lmax + 1):
        if lam == 0:
            floors = [0]
            I1 = np.empty((1, 1), dtype=object); I1[0, 0] = Fraction(1)
            Fd = [I1]
        else:
            floors, Fd = explicit_T(lam)
        d = len(floors)
        for i in range(0, imax + 1):
            tau = explicit_operator(floors, Fd, lambda m, f: Fraction(2 * (f + i)) if m == 0 else (Fraction(1) if m == 1 else Fraction(0)))
            a = explicit_operator(floors, Fd, lambda m, f: Fraction((-1) ** (f + i)))
            ap = explicit_operator(floors, Fd, lambda m, f: Fraction(1))
            Id = np.empty((d, d), dtype=object); Id.fill(Fraction(0))
            for t in range(d):
                Id[t, t] = Fraction(1)
            X = smith_frac(tau)
            Xb = smith_frac(np.concatenate([tau, a - Id], axis=1))
            Xbp = smith_frac(np.concatenate([tau, ap - Id], axis=1))
            twoX = sorted((e - 1 if e < 64 else 64) for e in X if e >= 1)
            twoX = [e for e in twoX if e >= 1]
            nz = lambda L: sorted(e for e in L if e >= 1)
            law = nz(Xb) == twoX
            lawp = nz(Xbp) == twoX
            if lam == 0:
                c0.append((i, law))
                continue
            tot += 1; ok += law
            c_sign[0] += 1; c_sign[1] += lawp
            if not law:
                print(f'  FAIL lam={lam} i={i}: X={nz(X)} Xbar={nz(Xb)} 2X={twoX}')
            if lam in (6, 12) and i in (2, 4):
                print(f'  example lam={lam} i={i}: X={nz(X)}  Xbar={nz(Xb)}')
    print(f'S4.1 family law Xbar = 2X on my explicit T(lam), lam = 1..{lmax}, i = 0..{imax}: {ok}/{tot}')
    print(f'S4.2 control lam = 0 (T(0) = Z): law holds at i = {[i for i, g in c0 if g]} ; fails at i = {[i for i, g in c0 if not g]}')
    print(f'S4.3 control sign-free fold a\' = exp F: law holds in {c_sign[1]}/{c_sign[0]} cells (fails in {c_sign[0] - c_sign[1]})')


def main():
    mode = sys.argv[1]
    if mode == 'slots':
        mode_slots()
    elif mode == 'ktest':
        mode_ktest()
    elif mode == 'lattice':
        mode_lattice(int(sys.argv[2]))
    elif mode == 'onemove':
        mode_onemove(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == 'lemmaB':
        mode_lemmaB(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
    elif mode == 'family':
        mode_family(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == 'depth':
        mode_depth(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    print('END kclass_test', mode, flush=True)


if __name__ == '__main__':
    main()
