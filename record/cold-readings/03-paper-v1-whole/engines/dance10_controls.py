"""dance10_controls.py — CONTROL dances only (Remark (2) of §10.5), copied from dance10.py.

dance10.py — the formal dance of §10.3 run as explicit block eliminations on T(l) (cold reader, 2026-10-05).

Exact arithmetic modulo 2^E (Python ints, E = 256), odd denominators inverted.
For an operator G on N = T(l) (a matrix), the dance follows the word of l: at each level, N = Phi(N') (doblar) or
N = V ⊗ Phi(N') (paso = V-split, which in my basis ordering is a pure re-indexing of slots, then doblar).
Doblar: coordinates b1-slots are pivot rows, sources b0-slots are pivot columns; P, C, B, Dd as in §10.3;
the move is CLEAN iff P is invertible mod 2 and S = Dd - B P^{-1} C ≡ 0 mod 2; next system S/2.
Checks:
  (i)  Sigma_c = F + 4(D + c): dance clean and final matrix == M^{(2)}(l, c) of Theorem 4.4 (Lemma 10.6(b));
  (ii) Psi_j = 2(2D + j) + (Ch - (-1)^j) Sh^{-1} (§10.2, built from Ch, Sh, NOT from the Bernoulli expansion):
       dance clean (Thm 10.15), final matrix has the support and entry valuations of M^{(2)}(l, ceil(j/2))
       (Thm 10.12, Thm 10.16 at c = 0), and the same Smith form;
  (iii) the Bernoulli expansion of §10.2: Psi_{2c} - 4(D+c) = sum eta_m F^(m), Psi_{2c-1} - 4(D+c) = sum eta'_m F^(m);
  (iv) CONTROLS (Remark (2) of §10.5): Xi = 4(D+c) + u(D)F with floor-dependent odd units u, and
       4 q(D) + F with generic payments q: report the first l where the dance is NOT clean.
Usage: python3 engines/dance10.py LMAX JMAX
"""
import sys
import random
from fractions import Fraction
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lattices import T as Tnp
from smithpy import qpoly, smith_exps
import numpy as np

LS = [int(x) for x in sys.argv[1].split(",")]; TRIALS = int(sys.argv[2])
E = 256
MOD = 1 << E


def inv_int(x, mod=MOD):
    return pow(x % mod, -1, mod)


def dfact(n):
    r = 1
    while n > 1:
        r *= n; n -= 2
    return r


def mat(n, m=None):
    m = n if m is None else m
    return [[0] * m for _ in range(n)]


def mmul(A, B, mod):
    if not A or not B:
        return [[0] * (len(B[0]) if B else 0) for _ in A]
    R = (np.array(A, dtype=object).dot(np.array(B, dtype=object))) % mod
    return R.tolist()


def madd(A, B, mod, s=1):
    return [[(a + s * b) % mod for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def minv(A, mod):
    """inverse modulo 2^e of a matrix invertible mod 2; returns None if not invertible mod 2."""
    n = len(A)
    M = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(A)]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if M[r][col] & 1:
                piv = r; break
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        iv = inv_int(M[col][col], mod)
        M[col] = [(x * iv) % mod for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [(x - f * y) % mod for x, y in zip(M[r], M[col])]
    return [row[n:] for row in M]


def family(l):
    N = l + 1
    k = N.bit_length() - 1
    I = [t for t in range(k) if (N >> t) & 1]
    return k, I


def lattice(l):
    F, w = Tnp(l)
    F = [[int(x) for x in row] for row in F.tolist()]
    return F, w


_dpc = {}


def divpowers_rec(l, mod):
    """[F^(0..l)] on T(l) modulo `mod`, from Prop. 3.1(b) on Phi and the coproduct on V ⊗ M (object arrays)."""
    if l in _dpc:
        return _dpc[l]
    if l == 0:
        res = [np.array([[1]], dtype=object)]
    elif l % 2 == 1:
        res = _phi((l - 1) // 2, l, mod)
    else:
        res = _v(_phi((l - 2) // 2, l - 1, mod), l)
    _dpc[l] = res
    return res


def _phi(lp, top, mod):
    dpN = divpowers_rec(lp, mod)
    n = dpN[0].shape[0]
    Z = np.zeros((n, n), dtype=object)
    get = lambda s: dpN[s] if s < len(dpN) else Z
    out = []
    for r in range(top + 1):
        M = np.zeros((2 * n, 2 * n), dtype=object)
        if r % 2 == 0:
            s = r // 2
            M[:n, :n] = (get(s) * inv_int(dfact(2 * s - 1), mod)) % mod
            M[n:, n:] = M[:n, :n]
        else:
            s = (r - 1) // 2
            M[n:, :n] = (get(s) * inv_int(dfact(2 * s + 1), mod)) % mod
            M[:n, n:] = (get(s + 1) * ((2 * s + 2) * inv_int(dfact(2 * s + 1), mod))) % mod
        out.append(M)
    return out


def _v(dpM, top):
    n = dpM[0].shape[0]
    Z = np.zeros((n, n), dtype=object)
    get = lambda s: dpM[s] if 0 <= s < len(dpM) else Z
    out = []
    for r in range(top + 1):
        M = np.zeros((2 * n, 2 * n), dtype=object)
        M[:n, :n] = get(r); M[n:, n:] = get(r); M[n:, :n] = get(r - 1)
        out.append(M)
    return out


def dance(G, l, mod):
    """returns (clean, final_matrix, mod_final, slot_order_info). G is a list-matrix on T(l)^{⊕r}."""
    r_slots = len(G) // len(lattice(l)[1])
    cur_l = l
    while cur_l > 0:
        if cur_l % 2 == 1:
            lp = (cur_l - 1) // 2
        else:
            lp = (cur_l - 2) // 2
            r_slots *= 2     # V-split: pure re-indexing in my basis ordering
        n1 = len(lattice(lp)[1])  # dim N'
        rowsB1 = [s * 2 * n1 + n1 + j for s in range(r_slots) for j in range(n1)]
        rowsB0 = [s * 2 * n1 + j for s in range(r_slots) for j in range(n1)]
        P = [[G[a][b] for b in rowsB0] for a in rowsB1]
        C = [[G[a][b] for b in rowsB1] for a in rowsB1]
        B = [[G[a][b] for b in rowsB0] for a in rowsB0]
        Dd = [[G[a][b] for b in rowsB1] for a in rowsB0]
        Pi = minv(P, mod)
        if Pi is None:
            return False, None, mod, "pivot not invertible mod 2 at l=%d" % cur_l
        S = madd(Dd, mmul(mmul(B, Pi, mod), C, mod), mod, -1)
        if any(x & 1 for row in S for x in row):
            return False, None, mod, "Schur complement not ≡ 0 mod 2 at l=%d" % cur_l
        mod //= 2
        G = [[(x // 2) % mod for x in row] for row in S]
        cur_l = lp
    return True, G, mod, None


def v2(x, mod):
    x %= mod
    if x == 0:
        return 10**9
    return (x & -x).bit_length() - 1


def slot_to_p(slot, s):
    """final slot index -> o-order index p(D): bit-reversal over s bits (first paso = most significant)."""
    return int(format(slot, "0%db" % s)[::-1], 2) if s else 0


def M_thm44(l, c, alpha=2):
    k, I = family(l)
    K = 1 << k; s = len(I); N = 1 << s
    oD = [sum(1 << I[j] for j in range(s) if (p >> j) & 1) for p in range(N)]
    q = qpoly(k, I)
    M = [[0] * N for _ in range(N)]
    for D in range(N):
        for Dp in range(N):
            if Dp & ~D:
                continue
            a = q.get(D & ~Dp, 0)
            prod = 1
            for d in range(oD[D], oD[Dp] + K):
                prod *= (1 << alpha) * (c + d)
            val = Fraction(-a * prod) * Fraction(2) ** (1 - K + oD[D & ~Dp])
            assert val.denominator == 1
            M[D][Dp] = int(val)
    return M


def reorder(Mfin, s):
    N = 1 << s
    perm = [slot_to_p(x, s) for x in range(N)]   # slot -> p
    R = [[0] * N for _ in range(N)]
    for a in range(N):
        for b in range(N):
            R[perm[a]][perm[b]] = Mfin[a][b]
    return R



stats = Counter()
first = {}
for l in LS:
    F, w = lattice(l)
    n = len(w)
    Dfl = [(l - x) // 2 for x in w]
    rnd = random.Random(7000 + l)
    for trial in range(TRIALS):
        for name in ("u(D) random odd, payment 4(D+c)", "payment 4q(D) random, unit 1", "payment 4q(D) random odd q, unit 1", "u(D) random odd AND 4q(D) random"):
            c = rnd.randrange(0, 8)
            if name.startswith("u(D) random odd,"):
                ur = [2 * rnd.randrange(0, 10**6) + 1 for _ in range(l + 2)]; qr = [f + c for f in range(l + 2)]
            elif name == "payment 4q(D) random, unit 1":
                ur = [1] * (l + 2); qr = [rnd.randrange(0, 10**6) for _ in range(l + 2)]
            elif name == "payment 4q(D) random odd q, unit 1":
                ur = [1] * (l + 2); qr = [2 * rnd.randrange(0, 10**6) + 1 for _ in range(l + 2)]
            else:
                ur = [2 * rnd.randrange(0, 10**6) + 1 for _ in range(l + 2)]; qr = [rnd.randrange(0, 10**6) for _ in range(l + 2)]
            Xi = [[0] * n for _ in range(n)]
            for a in range(n):
                for b in range(n):
                    if F[a][b]:
                        Xi[a][b] = (ur[Dfl[a]] * F[a][b]) % MOD
                Xi[a][a] = (Xi[a][a] + 4 * qr[Dfl[a]]) % MOD
            ok, _, _, why = dance(Xi, l, MOD)
            stats[(l, name, "clean" if ok else "NOT clean")] += 1
            if not ok:
                first.setdefault((l, name), why)
for kk in sorted(stats, key=str):
    print(kk, stats[kk])
print("first failure reasons:", first)
