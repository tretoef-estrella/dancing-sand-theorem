# part2.py — cold reader's machine gates for L3–L7 (2026-10-04). Own code; no flight engine consulted.
#   G-L34 : Smith of sigma on explicit dance lattices T_dance(lam) = small clocks + 2^k coker M(closed form) = rule
#   G-L5  : valuations of the closed-form M = K + kappa(m,K) + R_m(D) - R_{m+K}(D') + gamma(D \ D')
#   G-L6  : Theorem O by exhaustive DP (unique delta-optimal natural matching, value sum of eps)
#   C4    : Theorem F's construction (houses, walk, cut, Lambda, plumber's interval, (E)(M)(G)) and Theorem U on real cells
#   C4b   : brute-force tropical floor T(r) >= Y(r), exact Smith(M) = rule, T(r) <= d_r
#   P-INT : integer splitting antitonic in every cell; counterexample for general sequences
import sys, os, subprocess, itertools, time
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from myrule import s2, kappa, v2, digits, pava_int, dancers, nxt, small_clocks, big_clocks_B, big_clocks_X

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SCR = os.path.join(ROOT, 'scratch')
os.makedirs(SCR, exist_ok=True)
MODE = sys.argv[1]


def o(D):
    return sum(1 << t for t in D)


def v2f(x):
    if x == 0:
        return None
    x = Fraction(x)
    return v2(abs(x.numerator)) - v2(x.denominator)


def smith2(Mat):
    """exact 2-adic Smith exponents of a rational matrix (valuation-ordered pivoting over Z_(2)); None = zero"""
    A = [[Fraction(x) for x in r] for r in Mat]
    nr, nc = len(A), len(A[0]) if A else 0
    rows, cols = list(range(nr)), list(range(nc))
    ex = []
    while rows and cols:
        best = None
        for i in rows:
            for j in cols:
                if A[i][j] != 0:
                    vv = v2f(A[i][j])
                    if best is None or vv < best[0]:
                        best = (vv, i, j)
        if best is None:
            ex += [None] * min(len(rows), len(cols))
            break
        vv, r, c = best
        ex.append(vv)
        piv = A[r][c]
        for i in rows:
            if i != r and A[i][c] != 0:
                f = A[i][c] / piv
                Ai, Ar = A[i], A[r]
                for j in cols:
                    if Ar[j] != 0:
                        Ai[j] -= f * Ar[j]
        rows.remove(r)
        cols.remove(c)
    return ex


def pava_blocks(x):
    """real antitonic PAVA with strict merging: list of [start, end(excl), sum]"""
    bl = []
    for idx, xv in enumerate(x):
        bl.append([idx, idx + 1, Fraction(xv)])
        while len(bl) > 1 and bl[-2][2] / (bl[-2][1] - bl[-2][0]) < bl[-1][2] / (bl[-1][1] - bl[-1][0]):
            s, e, sm = bl.pop()
            bl[-1][1] = e
            bl[-1][2] += sm
    return bl


def int_sep_ok(x):
    """antitonic integer fit and floor(mu_A) >= ceil(mu_B) for adjacent real blocks"""
    bl = pava_blocks(x)
    y = pava_int(x)
    mono = all(y[i] >= y[i + 1] for i in range(len(y) - 1))
    sep = True
    for A, B in zip(bl, bl[1:]):
        muA = A[2] / (A[1] - A[0])
        muB = B[2] / (B[1] - B[0])
        fl = muA.numerator // muA.denominator
        ce = -((-muB.numerator) // muB.denominator)
        if fl < ce:
            sep = False
    return mono, sep


# ------------------------------------------------------------------ closed-form M (Theorem D)
def qpoly(lam):
    k, I = digits(lam)
    q = {frozenset(): -1}
    for t in range(k):
        sq = {}
        for S, a in q.items():
            for T, b in q.items():
                if S & T:
                    continue
                U = S | T
                sq[U] = sq.get(U, 0) + a * b
        if t in I:
            for S, a in q.items():
                if t in S:
                    continue
                U = S | {t}
                sq[U] = sq.get(U, 0) - a
        q = {S: a for S, a in sq.items() if a != 0}
    return q


def Mmatrix(lam, i, alpha=1):
    k, I = digits(lam)
    K = 1 << k
    q = qpoly(lam)
    Ds = dancers(I)
    M = []
    for D in Ds:
        row = []
        for Dp in Ds:
            if not set(Dp) <= set(D):
                row.append(Fraction(0))
                continue
            Delta = frozenset(D) - frozenset(Dp)
            a = q.get(Delta, 0)
            prod = 1
            for d in range(o(D), o(Dp) + K):
                prod *= (1 << alpha) * (i + d)
            row.append(-Fraction(2) ** (1 - K) * a * (1 << (o(D) - o(Dp))) * prod)
        M.append(row)
    return M


# ------------------------------------------------------------------ explicit dance lattices (F and floors only)
def lat_T(l, memo={}):
    if l in memo:
        return memo[l]
    if l == 0:
        res = ([0], [[0]])
    elif l % 2 == 1:
        res = Phi(lat_T((l - 1) // 2))
    else:
        res = VxN(Phi(lat_T((l - 2) // 2)))
    memo[l] = res
    return res


def Phi(N):
    fl, F = N
    n = len(fl)
    nfl = [0] * (2 * n)
    G = [[0] * (2 * n) for _ in range(2 * n)]
    for j in range(n):
        nfl[2 * j] = 2 * fl[j]
        nfl[2 * j + 1] = 2 * fl[j] + 1
        G[2 * j + 1][2 * j] = 1                     # F(b0 n) = b1 n
        for i in range(n):
            if F[i][j]:
                G[2 * i][2 * j + 1] += 2 * F[i][j]  # F(b1 n) = 2 b0 (F n)
    return (nfl, G)


def VxN(N):
    fl, F = N
    n = len(fl)
    nfl = [0] * (2 * n)
    G = [[0] * (2 * n) for _ in range(2 * n)]
    for j in range(n):
        nfl[2 * j] = fl[j]
        nfl[2 * j + 1] = fl[j] + 1
        G[2 * j + 1][2 * j] += 1                    # F(b0 x n) = b1 x n + b0 x F n
        for i in range(n):
            if F[i][j]:
                G[2 * i][2 * j] += F[i][j]
                G[2 * i + 1][2 * j + 1] += F[i][j]  # F(b1 x n) = b1 x F n
    return (nfl, G)


def engine_smith(S):
    p = os.path.join(SCR, 'p2_mat.txt')
    N = len(S)
    with open(p, 'w') as f:
        f.write(f'{N}\n')
        for r in S:
            f.write(' '.join(map(str, r)) + '\n')
    out = subprocess.run([os.path.join(HERE, 'mysmith'), 'file', p], capture_output=True, text=True).stdout.strip().split('\n')
    G = {}
    for tok in out[0].split()[1:]:
        e, c = tok.split(':')
        if int(e) > 0:
            G[int(e)] = int(c)
    z = int(out[1].split()[1])
    if z:
        G['Z'] = z
    return G


def add(G, e, c=1):
    key = 'Z' if e is None else e
    G[key] = G.get(key, 0) + c


# ------------------------------------------------------------------ cost data of a family
def hvals(I, k):
    return {t: nxt(t, list(I), k) - t for t in I}


def gamma(Delta, I, h):
    if not Delta:
        return 0
    md = min(Delta)
    return sum(h[u] for u in I if u not in Delta and u > md)


def Rmu(mu, D, h, alpha):
    return sum(h[t] - alpha * (1 << t) for t in D) - kappa(mu, o(D))


def run_ones(m, t):
    r = 0
    while (m >> (t + r)) & 1:
        r += 1
    return r


# ================================================================== G-L34
if MODE == 'L34':
    tot = ok_a = ok_b = 0
    bad = []
    for lam in range(1, 31):
        k, I = digits(lam)
        fl, F = lat_T(lam)
        assert len(fl) == 1 << (k + len(I)) and min(fl) == 0 and max(fl) == lam
        for i in range(0, 41):
            S = [[F[r][c] + (2 * (i + fl[c]) if r == c else 0) for c in range(len(fl))] for r in range(len(fl))]
            direct = engine_smith(S)
            # Theorem D side
            Gd = {}
            for a, e in small_clocks(lam).items():
                add(Gd, a, e)
            for e in smith2(Mmatrix(lam, i)):
                add(Gd, None if e is None else e + k)
            # rule side
            Gr = {}
            for a, e in small_clocks(lam).items():
                add(Gr, a, e)
            for e in (big_clocks_B(lam, i)):
                add(Gr, e)
            tot += 1
            ok_a += (Gd == direct)
            ok_b += (Gr == direct)
            if Gd != direct or Gr != direct:
                bad.append((lam, i, direct, Gd, Gr))
    print(f'G-L34 dance lattice = small clocks + 2^k coker M(closed form): {ok_a}/{tot}; = rule: {ok_b}/{tot}')
    for b in bad[:5]:
        print('  MISMATCH', b)
    # control: drop the factor 2^(o_D - o_D') in M (changes valuations) — must differ somewhere
    diff = 0
    for lam in range(1, 31):
        k, I = digits(lam)
        for i in range(1, 9):
            M = Mmatrix(lam, i)
            Ds = dancers(I)
            M2 = [[M[r][c] / (1 << (o(Ds[r]) - o(Ds[c]))) if M[r][c] != 0 else 0 for c in range(len(Ds))] for r in range(len(Ds))]
            diff += sorted(map(str, smith2(M))) != sorted(map(str, smith2(M2)))
    print('G-L34 control (factor 2^(o_D-o_D\') dropped) changes Smith(M) in', diff, 'cells (lam<=30, i=1..8)')

# ================================================================== G-L5
if MODE == 'L5':
    tot = ok = nonint = 0
    for lam in range(1, 64):
        k, I = digits(lam)
        K = 1 << k
        h = hvals(I, k)
        Ds = dancers(I)
        for i in range(1, 65):
            m = i - 1
            M = Mmatrix(lam, i)
            for r, D in enumerate(Ds):
                for c, Dp in enumerate(Ds):
                    if not set(Dp) <= set(D):
                        continue
                    x = M[r][c]
                    if x.denominator != 1:
                        nonint += 1
                    pred = K + kappa(m, K) + Rmu(m, D, h, 1) - Rmu(m + K, Dp, h, 1) + gamma(set(D) - set(Dp), I, h)
                    tot += 1
                    ok += (v2f(x) == pred)
    print(f'G-L5 valuations = K + kappa(m,K) + R_m(D) - R_(m+K)(D\') + gamma: {ok}/{tot}; non-integer entries: {nonint}')

# ================================================================== G-L6
if MODE == 'L6':
    tot = ok = 0
    for k in range(1, 7):
        for size in range(1, 5):
            for I in itertools.combinations(range(k), size):
                h = hvals(I, k)
                Ds = dancers(list(I))
                N = len(Ds)
                G = lambda D: sum(h[t] - 1 for t in D)
                eps = {D: G(D) - G(tuple(t for t in I if t not in D)) for D in Ds}

                def delta(Delta):
                    return 0 if not Delta else k - len(Delta) - min(Delta)
                for r in range(1, N + 1):
                    rows = Ds[N - r:]
                    cols = Ds[:r]
                    dp = {0: (0, 1)}
                    for D in rows:
                        nd = {}
                        for mask, (cst, cnt) in dp.items():
                            for ci, Dp in enumerate(cols):
                                if (mask >> ci) & 1 or not set(Dp) <= set(D):
                                    continue
                                nm = mask | (1 << ci)
                                nc_ = cst + delta(set(D) - set(Dp))
                                if nm not in nd or nc_ < nd[nm][0]:
                                    nd[nm] = (nc_, cnt)
                                elif nc_ == nd[nm][0]:
                                    nd[nm] = (nc_, nd[nm][1] + cnt)
                        dp = nd
                    full = (1 << r) - 1
                    tot += 1
                    if full in dp and dp[full][1] == 1 and dp[full][0] == sum(eps[D] for D in rows):
                        ok += 1
                    else:
                        print('  G-L6 FAIL', I, k, r, dp.get(full), sum(eps[D] for D in rows))
    print(f'G-L6 Theorem O (unique optimum, value sum eps): {ok}/{tot}')

# ================================================================== C4 : Theorem F construction (bitmask version: D <-> o_D)
def submasks_sorted(Im):
    out = []
    sm = Im
    while True:
        out.append(sm)
        if sm == 0:
            break
        sm = (sm - 1) & Im
    return sorted(out)


def house(ts_j, kj, mj, alpha):
    Im = sum(1 << t for t in ts_j)
    Ds = submasks_sorted(Im)
    h = {t: nxt(t, list(ts_j), kj) - t for t in ts_j}
    base = {}
    R, J, gam = {}, {}, {}
    for D in Ds:
        R[D] = sum(h[t] - alpha * (1 << t) for t in ts_j if (D >> t) & 1) - kappa(mj, D)
        J[D] = int(mj + D >= (1 << kj))
        if D == 0:
            gam[D] = 0
        else:
            md = (D & -D).bit_length() - 1
            gam[D] = sum(h[u] for u in ts_j if not (D >> u) & 1 and u > md)
    x = [R[D] - R[Im ^ D] for D in Ds]
    return Im, Ds, h, R, J, gam, x


def check_GEM(Im, Ds, V, yhat, R, gam, gold=True):
    E = all(V[D] - V[Im ^ D] == yhat[idx] for idx, D in enumerate(Ds))
    Mo = all(V[Ds[a]] >= V[Ds[a + 1]] for a in range(len(Ds) - 1))
    Gok = True
    for a in Ds:
        e = (a - 1) & a
        while True:
            if e != a:
                g = gam[a ^ e] if gold else 0
                if V[a] - V[e] > R[a] - R[e] + g:
                    Gok = False
                    break
            if e == 0:
                break
            e = (e - 1) & a
        if not Gok:
            break
    return E, Mo, Gok


def theoremF(I, k, alpha, mlow, price, stats, ctrl=None):
    ts = list(I)
    n = len(ts)
    kk = ts[1:] + [k]
    k0 = ts[0]
    V = {0: 0}
    yprev = [0]
    Imp, Dprev, hprev, Rprev, Jprev, gprev, xprev = house((), k0, mlow % (1 << k0), alpha)
    for j in range(1, n + 1):
        c = ts[j - 1]
        kj = kk[j - 1]
        mj = mlow % (1 << kj)
        Im, Ds, h, R, J, gam, x = house(tuple(ts[:j]), kj, mj, alpha)
        hh = kj - c
        T = (mj >> c) & 1
        kap = min(run_ones(mj, c), hh) if T == 1 else 1 + min(run_ones(mj, c + 1), hh - 1)
        sig = int(kap == hh)
        tau = hh - alpha * (1 << c) - (kap if T == 1 else 0)
        C = 1 << c
        rec = True
        for D0 in Dprev:
            Dc = D0 | C
            rec &= R[D0] == Rprev[D0] - (kap if T == 1 else 0) * Jprev[D0]
            rec &= R[Dc] == tau + Rprev[D0] - (kap if T == 0 else 0) * Jprev[D0]
            rec &= J[D0] == (sig * Jprev[D0] if T == 1 else 0)
            rec &= J[Dc] == (sig if T == 1 else sig * Jprev[D0])
        # gold recursion: same-half arrows gain h, arrows dropping c keep the child's gold
        for D in Ds:
            if D & C:
                rec &= gam[D] == gprev[D ^ C]
            elif D:
                rec &= gam[D] == gprev[D] + hh
        stats['rec'][rec] += 1
        yhat = pava_int(x)
        mono, sep = int_sep_ok(x)
        stats['int'][mono and sep] += 1
        X1 = {}
        for idx, D0 in enumerate(Dprev):
            X1[D0] = yprev[idx] - tau - (kap if T == 1 else 0) * Jprev[D0] + (kap if T == 0 else 0) * Jprev[Imp ^ D0]
        X2 = {D0: -X1[Imp ^ D0] for D0 in Dprev}
        walk = [max(X1[D0], 0) for D0 in Dprev] + [min(X2[D0], 0) for D0 in Dprev]
        stats['walk'][walk == yhat] += 1
        if any(J.values()):
            b = next(idx for idx, D in enumerate(Ds) if J[D])
            starts = {blk[0] for blk in pava_blocks(x)} | {len(Ds)}
            stats['cut'][(b in starts) and ((len(Ds) - b) in starts)] += 1
        stats['lam'][max(abs(t) for t in yhat) <= alpha * ((1 << kj) - 1)] += 1
        vp = {}
        for D0 in Dprev:
            vp[D0] = V[D0] - (kap if T == 1 else 0) * Jprev[D0]
            vp[D0 | C] = tau + V[D0] - (kap if T == 0 else 0) * Jprev[D0]
        if X1[Imp] > 0:
            Vn = vp
        else:
            F1 = [D0 for D0 in Dprev if X1[D0] <= 0]
            idxs = [Dprev.index(D0) for D0 in F1]
            stats['seg'][idxs == list(range(len(Dprev) - len(F1), len(Dprev)))] += 1
            F2 = [D0 for D0 in Dprev if X2[D0] >= 0]
            f = F1[0]
            fi = Dprev.index(f)
            lo, hi = vp[f], vp[Im ^ f]
            if fi > 0:
                pp = Dprev[fi - 1]
                lo = max(lo, vp[Im ^ pp])
                hi = min(hi, vp[pp])
            stats['win'][lo <= hi] += 1
            if lo > hi:
                return None
            cF = {'lo': lo, 'hi': hi, 'mid': (lo + hi) // 2}[price]
            if ctrl == 'natural':
                cF = vp[Imp]
            Vn = dict(vp)
            for D0 in F1:
                Vn[D0] = cF
            for D0 in F2:
                Vn[D0 | C] = cF
        E, Mo, Gk = check_GEM(Im, Ds, Vn, yhat, R, gam, gold=(ctrl != 'nogold'))
        stats['E'][E] += 1
        stats['M'][Mo] += 1
        stats['G'][Gk] += 1
        V, yprev = Vn, yhat
        Imp, Dprev, hprev, Rprev, Jprev, gprev, xprev = Im, Ds, h, R, J, gam, x
    return V, (Imp, Dprev, hprev, Rprev, Jprev, gprev, xprev)


def real_cells(I, k, alpha, mlow, V, hd, imax, stats):
    Im, Ds, h, R, J, gam, x = hd
    K = 1 << k
    for Q in range(0, imax // K + 2):
        m = mlow + K * Q
        if m + 1 > imax:
            break
        Rm, RmK = {}, {}
        for D in Ds:
            base = sum(h[t] - alpha * (1 << t) for t in I if (D >> t) & 1)
            Rm[D] = base - kappa(m, D)
            RmK[D] = base - kappa(m + K, D)
        Pr, Pc = run_ones(m, k), run_ones(m + K, k)
        stats['pen'][all(Rm[D] == R[D] - Pr * J[D] and RmK[D] == R[D] - Pc * J[D] for D in Ds)] += 1
        xc = [Rm[D] - RmK[Im ^ D] for D in Ds]
        yc = pava_int(xc)
        mono, sep = int_sep_ok(xc)
        stats['int'][mono and sep] += 1
        v = {D: V[D] - Pr * J[D] for D in Ds}
        w = {D: V[D] - Pc * J[D] for D in Ds}
        ok = all(v[Ds[a]] >= v[Ds[a + 1]] and w[Ds[a]] >= w[Ds[a + 1]] for a in range(len(Ds) - 1))
        ok &= all(v[D] - w[Im ^ D] == yc[idx] for idx, D in enumerate(Ds))
        if ok:
            for a in Ds:
                b = a
                while True:
                    if v[a] - w[b] > Rm[a] - RmK[b] + gam[a ^ b]:
                        ok = False
                        break
                    if b == 0:
                        break
                    b = (b - 1) & a
                if not ok:
                    break
        stats['U'][ok] += 1


def new_stats():
    keys = ['rec', 'int', 'walk', 'cut', 'lam', 'seg', 'win', 'E', 'M', 'G', 'pen', 'U', 'U0']
    return {kk: {True: 0, False: 0} for kk in keys}


if MODE == 'C4':
    lammin, lammax = int(sys.argv[2]), int(sys.argv[3])
    alphas = [int(a) for a in sys.argv[4].split(',')]
    prices = sys.argv[5].split(',')
    imax_small = int(sys.argv[6])
    big_mult = int(sys.argv[7])  # i range beyond 63: big_mult*K + 1
    st = new_stats()
    ctrl_nogold = {True: 0, False: 0}
    ctrl_nat = {True: 0, False: 0}
    t0 = time.time()
    houses = 0
    for lam in range(lammin, lammax + 1):
        k, I = digits(lam)
        if not I:
            continue
        K = 1 << k
        imax = imax_small if lam <= 63 else big_mult * K + 1
        for alpha in alphas:
            for mlow in range(K):
                for price in prices:
                    res = theoremF(I, k, alpha, mlow, price, st)
                    houses += 1
                    if res is None:
                        continue
                    real_cells(I, k, alpha, mlow, res[0], res[1], imax if alpha == 1 else 2 * K + 1, st)
                if lam <= 63:
                    s1 = new_stats()
                    theoremF(I, k, alpha, mlow, 'mid', s1, ctrl='nogold')
                    ctrl_nogold[s1['G'][False] == 0] += 1
                    s2_ = new_stats()
                    theoremF(I, k, alpha, mlow, 'mid', s2_, ctrl='natural')
                    ctrl_nat[(s2_['G'][False] + s2_['M'][False]) == 0] += 1
    print(f'C4 lam in [{lammin},{lammax}], alpha in {alphas}, prices {prices}: {houses} house constructions, {time.time() - t0:.0f} s')
    for kk, d in st.items():
        print(f'   {kk:5s}: pass {d[True]}  FAIL {d[False]}')
    print(f'   control nogold (lam<=63): houses where (G) still holds at every level {ctrl_nogold[True]}, where it fails {ctrl_nogold[False]}')
    print(f'   control natural price (lam<=63): houses still fine {ctrl_nat[True]}, broken {ctrl_nat[False]}')

# ================================================================== C4-i0 : the i = 0 cell
if MODE == 'C4i0':
    st = new_stats()
    tot = okv = okc = 0
    for lam in range(1, int(sys.argv[2]) + 1):
        k, I = digits(lam)
        if not I:
            continue
        K = 1 << k
        M = Mmatrix(lam, 0)
        Dt = dancers(I)                      # tuples, o-order (same order as masks)
        res = theoremF(I, k, 1, K - 1, 'mid', st)
        V, (Im, Ds, h, R, J, gam, x) = res
        assert [o(D) for D in Dt] == Ds
        consts = set()
        for r, D in enumerate(Ds):
            if D == 0:
                assert all(e == 0 for e in M[r])
                continue
            for c, Dp in enumerate(Ds):
                if (Dp & ~D) == 0:
                    consts.add(v2f(M[r][c]) - (R[D] - R[Dp] + gam[D ^ Dp]))
        tot += 1
        okv += (len(consts) == 1)
        C = min(consts)
        rule = big_clocks_B(lam, 0)[1:]
        yh = pava_int(x)
        okc += (sorted(rule) == sorted(k + C + t for t in yh[1:])) and (pava_int(x[1:]) == yh[1:])
        ok = True
        for a in Ds[1:]:
            for b in Ds:
                if (b & ~a) == 0 and V[a] - V[b] > R[a] - R[b] + gam[a ^ b]:
                    ok = False
        st['U0'][ok] += 1
    print(f'C4-i0: i=0 valuations = one constant + base ruler of house 2^k-1: {okv}/{tot}; rule i=0 clocks = k + C + pooled base clocks and Cut at 1: {okc}/{tot}; Theorem U on the i=0 cell: {st["U0"]}; construction checks E {st["E"]} M {st["M"]} G {st["G"]}')

# ================================================================== C4b : brute-force floor
if MODE == 'C4b':
    lammax = int(sys.argv[2])
    tot = okT = okS = okTd = 0
    pooled_needed = 0
    for lam in range(1, lammax + 1):
        k, I = digits(lam)
        Ds = dancers(I)
        N = len(Ds)
        imax = 64 if N <= 8 else 12
        for i in range(0, imax + 1):
            M = Mmatrix(lam, i)
            val = [[v2f(M[r][c]) for c in range(N)] for r in range(N)]
            # T(r): min over r-matchings in the support (rows processed in order, mask of used columns)
            INF = 10 ** 9
            dp = {0: 0}
            for r in range(N):
                supp = [(c, val[r][c]) for c in range(N) if val[r][c] is not None]
                nd = dict(dp)
                for mask, cst in dp.items():
                    for c, vv in supp:
                        if (mask >> c) & 1:
                            continue
                        nm = mask | (1 << c)
                        v = cst + vv
                        if v < nd.get(nm, INF):
                            nd[nm] = v
                dp = nd
            T = [0] + [min((cst for mask, cst in dp.items() if bin(mask).count('1') == rr), default=None) for rr in range(1, N + 1)]
            sm = smith2(M)
            fin = sorted(e for e in sm if e is not None)
            d = [0]
            for e in fin:
                d.append(d[-1] + e)
            rule = big_clocks_B(lam, i)
            rf = sorted(e - k for e in rule if e is not None)
            Y = [0]
            for e in rf:
                Y.append(Y[-1] + e)
            unp = big_clocks_B(lam, i, pool=False)
            # unpooled partial sums in o-order from the end (natural minors)
            Ul = [0]
            for e in reversed([e for e in unp if e is not None]):
                Ul.append(Ul[-1] + e - k)
            tot += 1
            okS += (sorted(map(str, sm)) == sorted(map(str, [None if e is None else e - k for e in rule])))
            nr = len(fin)
            okT += all(T[rr] is not None and T[rr] >= Y[rr] for rr in range(1, nr + 1))
            okTd += all(T[rr] <= d[rr] for rr in range(1, nr + 1))
            pooled_needed += any(T[rr] is not None and T[rr] < Ul[rr] for rr in range(1, nr + 1))
    print(f'C4b lam<={lammax}: exact Smith(M) = rule {okS}/{tot}; T(r) >= Y(r) all r {okT}/{tot}; T(r) <= d_r {okTd}/{tot}; cells with T(r) < U(r) (unpooled) somewhere: {pooled_needed}')

# ================================================================== P-INT
if MODE == 'PINT':
    x = [1, 2, 0, 1, 2, 2]
    print('P-INT example', x, '-> real blocks', [(b[0], b[1], str(b[2] / (b[1] - b[0]))) for b in pava_blocks(x)], '-> integer split', pava_int(x), 'antitonic:', int_sep_ok(x))
