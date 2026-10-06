# gate_t710_mine.py — Grepy el lector frío del cubo 4, 2026-10-05.
# Theorem 7.10 of v2 against the 2-adic Smith form of M^(alpha)(lambda, i), the matrix of Theorem 4.4,
# built from its closed form (q_k, windows, payments 2^alpha (i + d)). Smith exponents by
# min-valuation elimination in Z/2^P (a local PIR), with P above every exponent.
# Predictions: from the rulers of §5 (x_D) and Proposition 5.4 (x^#), pooled by my own PAVA;
# second route for alpha = 1: the raw clocks u_i(D) of §1.2, pooled (Main Theorem rule).
# Usage: python3 gate_t710_mine.py LMAX IMAX
import sys
from fitfast import blocks, int_fit_bl

LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 63
IMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 12


def s2(a):
    return bin(a).count("1")


def v2(a):
    return (a & -a).bit_length() - 1


def kap(a, b):
    return s2(a) + s2(b) - s2(a + b)


def bits(m):
    return [t for t in range(m.bit_length()) if (m >> t) & 1]


def family(lam):
    L = lam + 1
    k = L.bit_length() - 1
    I = L - (1 << k)
    return k, I


def dancers(I):
    out = [0]
    for t in bits(I):
        out = out + [d | (1 << t) for d in out]
    return sorted(out)


def q_coeffs(k, I):
    """q_0 = -1, q_{t+1} = q_t^2 - [t in I] y_t q_t in Z[y_t]/(y_t^2); dict mask -> coefficient."""
    q = {0: -1}
    for t in range(k):
        sq = {}
        for a, ca in q.items():
            for b, cb in q.items():
                if a & b == 0:
                    sq[a | b] = sq.get(a | b, 0) + ca * cb
        if (I >> t) & 1:
            for a, ca in q.items():
                # y_t * y^a, a never contains t at this stage
                sq[a | (1 << t)] = sq.get(a | (1 << t), 0) - ca
        q = sq
    return q


def build_M(lam, i, alpha):
    """M_{DD'} = -2^{1-K+o(D minus D')} a_k(D minus D') prod_{d=o_D}^{o_D'+K-1} 2^alpha (i+d), as exact
    rationals represented by (integer numerator, power of 2 in the denominator)."""
    k, I = family(lam)
    K = 1 << k
    ds = dancers(I)
    a = q_coeffs(k, I)
    M = []
    for D in ds:
        row = []
        for Dp in ds:
            if Dp & ~D:
                row.append(0)
                continue
            Dl = D ^ Dp
            prod = 1
            for d in range(D, Dp + K):        # o_D = D, o_D' = Dp
                prod *= (1 << alpha) * (i + d)
            num = -a.get(Dl, 0) * prod
            e = 1 - K + Dl                     # power of two
            if num == 0:
                row.append(0)
            elif e >= 0:
                row.append(num << e)
            else:
                assert num % (1 << (-e)) == 0, "entry not integral"
                row.append(num >> (-e))
        M.append(row)
    return k, I, ds, M


def smith_exponents(M, P):
    """Exponents of the Smith form over Z_2 of the integer matrix M, computed in Z/2^P.
    Returns the sorted list of exponents < P, and the number of remaining (>= P) ones."""
    mod = 1 << P
    A = [[x % mod for x in row] for row in M]
    rows = list(range(len(A)))
    cols = list(range(len(A[0])))
    ex = []
    while rows and cols:
        best = None
        for r in rows:
            for c in cols:
                x = A[r][c]
                if x:
                    e = v2(x)
                    if best is None or e < best[0]:
                        best = (e, r, c)
        if best is None:
            break
        e, r, c = best
        u = A[r][c] >> e
        uinv = pow(u, -1, mod)
        for r2 in rows:
            if r2 != r and A[r2][c]:
                f = ((A[r2][c] >> e) * uinv) % mod
                Ar, A2 = A[r], A[r2]
                for c2 in cols:
                    if Ar[c2]:
                        A2[c2] = (A2[c2] - f * Ar[c2]) % mod
                assert A2[c] == 0
        ex.append(e)
        rows.remove(r)
        cols.remove(c)
    return sorted(ex), min(len(rows), len(cols)) if rows and cols else 0


def h_of(I, k):
    bs = bits(I) + [k]
    return {t: bs[j + 1] - t for j, t in enumerate(bs[:-1])}


def Rmu(I, h, alpha, mu, E):
    return sum(h[t] - alpha * (1 << t) for t in bits(E)) - kap(mu, E)


def phi(x):
    return x + v2(x)


def main():
    stats = {}

    def bump(key, n=1):
        stats[key] = stats.get(key, 0) + n

    examples = []
    for lam in range(1, LMAX + 1):
        for i in range(0, IMAX + 1):
            for alpha in (1, 2):
                k, I, ds, M = build_M(lam, i, alpha)
                K = 1 << k
                N = len(ds)
                h = h_of(I, k)
                bump("cells")
                if i >= 1:
                    m = i - 1
                    x = [Rmu(I, h, alpha, m, D) - Rmu(I, h, alpha, m + K, I ^ D) for D in ds]
                    bl = blocks(x)
                    yh = int_fit_bl(bl)
                    pred = sorted(alpha * K + kap(m, K) + y for y in yh)
                    raw = sorted(alpha * K + kap(m, K) + y for y in x)
                    # control (i): the real fit rounded half up at every position (a wrong variant;
                    # unlike a re-ordering of the integer fit, it changes the multiset when S mod p != 0)
                    wrong = []
                    for s, p, S in bl:
                        wrong.extend([(2 * S + p) // (2 * p)] * p)
                        if S % p:
                            bump("level_sets_nonintegral_mean")
                    if any(S % p for s, p, S in bl):
                        bump("cells_with_nonintegral_level_set")
                    wrong = sorted(alpha * K + kap(m, K) + y for y in wrong)
                    detv = sum(v2(M[j][j]) for j in range(N))
                    P = detv + 8
                    got, rest = smith_exponents(M, P)
                    if rest or sum(got) != detv:
                        bump("FAIL_det_or_rank")
                    if got != pred:
                        bump("FAIL_t710")
                        if len(examples) < 5:
                            examples.append((lam, i, alpha, got, pred))
                    pooled_acts = (yh != x)
                    if pooled_acts:
                        bump("cells_where_pooling_acts")
                        if got != raw:
                            bump("control_raw_rejected")
                    if wrong != pred:
                        bump("cells_where_rounding_matters")
                        if got != wrong:
                            bump("control_rounded_realfit_rejected")
                    # where the repaired step is exercised: non-zero penalty and a level set of size >= 2
                    l = m % K
                    Pr = v2((m >> k) + 1)
                    Pc = v2(((m + K) >> k) + 1)
                    JH = [1 if l + D >= K else 0 for D in ds]
                    if (Pr or Pc) and any(JH):
                        bump("cells_nonzero_penalty")
                        if any(p >= 2 for s, p, S in bl):
                            bump("cells_nonzero_penalty_and_pooling")
                        # control (ii): base clocks x_H, then the penalty moved one position late
                        xH = [Rmu(I, h, alpha, l, D) - Rmu(I, h, alpha, l, I ^ D) for D in ds]
                        corr = [xH[j] - Pr * JH[j] + Pc * JH[N - 1 - j] for j in range(N)]
                        if corr != x:
                            bump("FAIL_lemma75_cell_is_penalty_cell")
                        pb = JH.index(1)
                        if pb + 1 < N:
                            J2 = [1 if j >= pb + 1 else 0 for j in range(N)]
                            yH = int_fit_bl(blocks(xH))
                            late = [yH[j] - Pr * J2[j] + Pc * J2[N - 1 - j] for j in range(N)]
                            bump("control_late_penalty_tried")
                            if sorted(alpha * K + kap(m, K) + y for y in late) != got:
                                bump("control_late_penalty_rejected")
                    # second route (alpha = 1): the raw clocks of §1.2 and the Main Theorem rule
                    if alpha == 1:
                        u = []
                        for D in ds:
                            xi = lam + 1 - 2 * D
                            hD = sum(h[t] for t in bits(D))
                            u.append(phi(xi) + kap(i + D - 1, xi) + hD)
                        if sorted(k + y for y in got) != sorted(int_fit_bl(blocks(u))):
                            bump("FAIL_rule_route")
                        bump("rule_route_cells")
                else:
                    # i = 0: row 0 (dancer empty set) must vanish; Smith of the other rows
                    if any(M[0]):
                        bump("FAIL_row_empty_not_zero")
                    if N == 1:
                        bump("i0_I_empty")
                        continue
                    Ms = M[1:]
                    xs = [Rmu(I, h, alpha, K - 1, D) - Rmu(I, h, alpha, K - 1, I ^ D) for D in ds[1:]]
                    bl = blocks(xs)
                    pred = sorted(alpha * K + y for y in int_fit_bl(bl))
                    detv = sum(v2(Ms[j - 1][j]) for j in range(1, N))
                    P = detv + 8
                    got, rest = smith_exponents(Ms, P)
                    if rest:
                        bump("FAIL_rank_i0")
                    if got != pred:
                        bump("FAIL_t710_i0")
                        if len(examples) < 5:
                            examples.append((lam, i, alpha, got, pred))
                    bump("cells_i0")
                    if alpha == 1:
                        u = []
                        for D in ds[1:]:
                            xi = lam + 1 - 2 * D
                            hD = sum(h[t] for t in bits(D))
                            u.append(phi(xi) + kap(i + D - 1, xi) + hD)
                        if sorted(k + y for y in got) != sorted(int_fit_bl(blocks(u))):
                            bump("FAIL_rule_route_i0")
        if lam % 16 == 15:
            print(f"lambda <= {lam} done", flush=True)
    for key in sorted(stats):
        print(f"  {key} = {stats[key]}")
    for e in examples:
        print("  example:", e)
    fails = [key for key in stats if key.startswith("FAIL")]
    print("RESULT:", "0 failures" if not fails else f"FAILURES {fails}")


main()
