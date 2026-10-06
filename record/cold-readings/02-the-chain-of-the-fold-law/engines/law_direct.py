# law_direct.py — «Grepy el lector frío del cubo 2», check 1 of MISSION §3.
# Own code, nothing imported from the flights' engines.
# Local Smith form at the prime 2 of integer matrices, computed modulo 2^64 (numpy uint64 wraps exactly),
# minimal-valuation pivots. Exponents < 64 are exact; 64 means "free or >= 64".
# Laplacians in the VERTEX basis: cube Q_n and the folded cube (Cayley multigraph of G/<a>).
import sys, random
import numpy as np

U64 = np.uint64
BIG = 64


def inv_odd(u):
    """inverse of an odd uint64 modulo 2^64 (Newton)."""
    u = U64(u)
    x = u
    for _ in range(6):
        x = x * (U64(2) - u * x)
    assert (u * x) == U64(1)
    return x


def val_array(S):
    """2-adic valuations of a uint64 array (64 for zero)."""
    low = S & (U64(0) - S)
    v = np.full(S.shape, BIG, dtype=np.int64)
    nz = low != 0
    v[nz] = np.log2(low[nz].astype(np.float64)).astype(np.int64)
    return v


def smith2(M):
    """M: square or rectangular numpy uint64 array (copied). Returns list of exponents (len = min dims)."""
    M = np.array(M, dtype=np.uint64, copy=True)
    r, c = M.shape
    ex = []
    for k in range(min(r, c)):
        S = M[k:, k:]
        odd = (S & U64(1)) != 0
        if odd.any():
            idx = int(np.argmax(odd))
            v = 0
        else:
            V = val_array(S)
            idx = int(np.argmin(V))
            v = int(V.flat[idx])
            if v >= BIG:
                ex.extend([BIG] * (min(r, c) - k))
                return ex
        i, j = divmod(idx, S.shape[1])
        i += k; j += k
        if i != k:
            M[[k, i], k:] = M[[i, k], k:]
        if j != k:
            M[k:, [k, j]] = M[k:, [j, k]]
        p = M[k, k]
        u = p >> U64(v)
        ui = inv_odd(u)
        col = M[k + 1:, k]
        f = (col >> U64(v)) * ui
        if f.any():
            M[k + 1:, k + 1:] -= np.outer(f, M[k, k + 1:])
        ex.append(v)
    return ex


def cube_lap(n):
    N = 1 << n
    L = np.zeros((N, N), dtype=np.uint64)
    for v in range(N):
        L[v, v] = U64(n)
        for i in range(n):
            w = v ^ (1 << i)
            L[v, w] = L[v, w] - U64(1)
    return L


def quotient_lap(n, u):
    """Laplacian n*I - sum_i P_{x_i} on Z[G/<u>], u a bitmask != 0 (u = all ones: the folded cube)."""
    N = 1 << n
    reps = sorted({min(v, v ^ u) for v in range(N)})
    pos = {r: t for t, r in enumerate(reps)}
    M = len(reps)
    L = np.zeros((M, M), dtype=np.uint64)
    for r in reps:
        a = pos[r]
        L[a, a] = L[a, a] + U64(n)
        for i in range(n):
            w = r ^ (1 << i)
            b = pos[min(w, w ^ u)]
            L[a, b] = L[a, b] - U64(1)
    return L


def v2(x):
    x = abs(x)
    if x == 0:
        return 10 ** 9
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c


def comb(n, k):
    from math import comb as C
    return C(n, k)


def v2_trees_cube(n):
    return 2 ** n - n - 1 + sum(comb(n, k) * v2(k) for k in range(1, n + 1))


def v2_trees_fold(n):
    return -(n - 1) + sum(comb(n, k) * (1 + v2(k)) for k in range(2, n + 1, 2))


def tally(ex):
    d = {}
    for e in ex:
        if 0 < e < BIG:
            d[e] = d.get(e, 0) + 1
    return dict(sorted(d.items()))


def nbig(ex):
    return sum(1 for e in ex if e >= BIG)


# ---------- slow exact integer Smith form (different algorithm), for small matrices ----------
def snf_int(A):
    A = [list(map(int, row)) for row in A]
    m, n = len(A), len(A[0])
    diag = []
    t = 0
    while t < min(m, n):
        # find nonzero entry with smallest |value|
        best = None
        for i in range(t, m):
            for j in range(t, n):
                if A[i][j] != 0 and (best is None or abs(A[i][j]) < abs(A[best[0]][best[1]])):
                    best = (i, j)
        if best is None:
            break
        i, j = best
        A[t], A[i] = A[i], A[t]
        for row in A:
            row[t], row[j] = row[j], row[t]
        done = False
        while not done:
            done = True
            p = A[t][t]
            for i in range(t + 1, m):
                q = A[i][t] // p
                if q:
                    A[i] = [a - q * b for a, b in zip(A[i], A[t])]
                if A[i][t] != 0:
                    A[t], A[i] = A[i], A[t]; done = False; break
            if not done:
                continue
            p = A[t][t]
            for j in range(t + 1, n):
                q = A[t][j] // p
                if q:
                    for row in A:
                        row[j] -= q * row[t]
                if A[t][j] != 0:
                    for row in A:
                        row[t], row[j] = row[j], row[t]
                    done = False; break
            if not done:
                continue
            # divisibility condition
            p = A[t][t]
            for i in range(t + 1, m):
                for j in range(t + 1, n):
                    if A[i][j] % p != 0:
                        A[t] = [a + b for a, b in zip(A[t], A[i])]
                        done = False; break
                if not done:
                    break
        diag.append(abs(A[t][t]))
        t += 1
    return diag


def to_signed(L):
    return [[int(x) if int(x) < 2 ** 63 else int(x) - 2 ** 64 for x in row] for row in L.tolist()]


def selftests(log):
    rng = np.random.default_rng(20261005)
    ok = 0
    T = 300
    for t in range(T):
        d = int(rng.integers(2, 13))
        exps = [int(rng.integers(0, 20)) if rng.random() < 0.9 else BIG for _ in range(d)]
        D = np.zeros((d, d), dtype=np.uint64)
        for i, e in enumerate(exps):
            if e < BIG:
                D[i, i] = U64(2 ** e) * U64(2 * int(rng.integers(0, 1000)) + 1)
        def unimod():
            Lw = np.tril(rng.integers(0, 2 ** 62, size=(d, d), dtype=np.uint64), -1) + np.eye(d, dtype=np.uint64)
            Up = np.triu(rng.integers(0, 2 ** 62, size=(d, d), dtype=np.uint64), 1)
            Up = Up + np.diag((2 * rng.integers(0, 2 ** 30, size=d) + 1).astype(np.uint64))
            P = np.eye(d, dtype=np.uint64)[rng.permutation(d)]
            return P @ Lw @ Up
        A = unimod() @ D @ unimod()
        got = sorted(smith2(A))
        if got == sorted(exps):
            ok += 1
        elif t < 5:
            log(f"  selftest mismatch {sorted(exps)} got {got}")
    log(f"S1.0a random known Smith forms mod 2^64: {ok}/{T}")
    # (b) exact integer SNF for n <= 4
    okb = 0
    for n in range(2, 5):
        for name, L in (("cube", cube_lap(n)), ("fold", quotient_lap(n, (1 << n) - 1))):
            ex = smith2(L)
            dg = snf_int(to_signed(L))
            dg = dg + [0] * (L.shape[0] - len(dg))
            ex_int = [v2(x) if x != 0 else BIG for x in dg]
            same = tally(ex) == tally(ex_int) and nbig(ex) == nbig(ex_int)
            okb += same
            log(f"S1.0b n={n} {name}: smith2 {tally(ex)} big={nbig(ex)} | exact SNF diag {dg} -> {tally(ex_int)} big={nbig(ex_int)} | {'OK' if same else 'MISMATCH'}")
    log(f"S1.0b exact-SNF agreement: {okb}/6")


def main():
    nmin, nmax = int(sys.argv[1]), int(sys.argv[2])
    out = []
    def log(s):
        print(s, flush=True)
    if nmin <= 2:
        selftests(log)
    for n in range(nmin, nmax + 1):
        A = (1 << n) - 1
        exK = smith2(cube_lap(n))
        exF = smith2(quotient_lap(n, A))
        K, F = tally(exK), tally(exF)
        an = 2 ** (n - 2) - 2 ** ((n - 2) // 2)
        sK = sum(e * m for e, m in K.items()); sF = sum(e * m for e, m in F.items())
        okord = (sK == v2_trees_cube(n)) and (sF == v2_trees_fold(n))
        lowered = {}
        for e, m in K.items():
            if e >= 2:
                lowered[e - 1] = lowered.get(e - 1, 0) + m
        lowered = dict(sorted(lowered.items()))
        law = lowered == F
        nz2 = K.get(1, 0)
        bai = (nz2 == an) and (sum(K.values()) == 2 ** (n - 1) - 1)
        # controls
        def law_with(a):
            # Syl2 K =? (Z/2)^a + (F raised by one)
            raised = {1: a}
            for e, m in F.items():
                raised[e + 1] = raised.get(e + 1, 0) + m
            raised = {e: m for e, m in sorted(raised.items()) if m}
            return raised == K
        c_plus, c_minus = law_with(an + 1), law_with(an - 1)
        noshift = {1: an}
        for e, m in F.items():
            noshift[e] = noshift.get(e, 0) + m
        noshift = {e: m for e, m in sorted(noshift.items()) if m}
        c_noshift = noshift == K
        exW = smith2(quotient_lap(n, 3))  # wrong fold u = x1 x2
        W = tally(exW)
        c_wrong = W == lowered
        # order control: remove one edge from the cube
        Lbad = cube_lap(n); Lbad[0, 1] = Lbad[0, 1] + U64(1); Lbad[1, 0] = Lbad[1, 0] + U64(1)
        Lbad[0, 0] = Lbad[0, 0] - U64(1); Lbad[1, 1] = Lbad[1, 1] - U64(1)
        exB = smith2(Lbad); sB = sum(e for e in exB if e < BIG)
        c_ord = (sB == v2_trees_cube(n))
        log(f"n={n}: K2={K} free={nbig(exK)} | Kbar2={F} free={nbig(exF)}")
        log(f"   order v2: K {sK} vs formula {v2_trees_cube(n)}; Kbar {sF} vs {v2_trees_fold(n)} -> {'OK' if okord else 'FAIL'}; edge-removed control order {sB} -> {'(control did NOT fire)' if c_ord else 'fires'}")
        log(f"   LAW Kbar == K lowered: {'HOLDS' if law else 'FAILS'} | Bai a_n={an} #Z/2={nz2} #factors={sum(K.values())} -> {'OK' if bai else 'FAIL'}")
        log(f"   controls (True = control did NOT fire): a_n+1 {c_plus}, a_n-1 {c_minus}, no-shift {c_noshift}, wrong fold x1x2 {c_wrong} (Kwrong={W}, free={nbig(exW)})")
    print("END law_direct", flush=True)


if __name__ == "__main__":
    main()
