# M2: independent Smith forms, from the definition of the graphs only.
# Q_n: vertices {0,1}^n (ints < 2^n), edges x ~ x xor 2^i.  Laplacian L = n I - A.
# Folded cube Q_n/<1>: vertices = classes {x, x xor (2^n-1)}, representative with top bit 0;
#   it is the Cayley (multi)graph of F_2^n/<1> with the images of the n unit vectors:
#   Lbar[x][x] += n, Lbar[x][rep(x xor 2^i)] -= 1 for each i (multiplicities counted).
# Smith form over Z_(p): elimination mod p^M with a pivot of least p-adic valuation (local PIR).
# Output: the multiset of exponents e >= 1 of the p-part of coker, and the count of exponents >= M
# (these are the free part: rank of the kernel).
import numpy as np, sys, json, time
def lap_cube(n):
    N = 1 << n
    L = np.zeros((N, N), dtype=np.int64)
    for x in range(N):
        L[x, x] = n
        for i in range(n): L[x, x ^ (1 << i)] -= 1
    return L
def lap_fold(n):
    full = (1 << n) - 1
    rep = lambda x: x if x < (1 << (n - 1)) else x ^ full
    N = 1 << (n - 1) if n >= 1 else 1
    L = np.zeros((N, N), dtype=np.int64)
    for x in range(N):
        L[x, x] += n
        for i in range(n): L[x, rep(x ^ (1 << i))] -= 1
    return L
def val(a, p, M):
    # p-adic valuation of each entry of a (entries reduced mod p^M), M for 0
    v = np.full(a.shape, M, dtype=np.int64); b = a.copy(); nz = b != 0
    cur = np.zeros(a.shape, dtype=np.int64)
    for e in range(M):
        m = nz & (b % p != 0) & (v == M)
        v[m] = e
        b = np.where(nz, b // p, b)
    return v
def smith_local(L, p, M):
    q = p ** M
    A = np.mod(L.astype(np.int64), q)
    exps = []
    N = A.shape[0]
    while A.shape[0] > 0:
        V = val(A, p, M)
        r, c = np.unravel_index(np.argmin(V), V.shape); v = int(V[r, c])
        if v >= M:
            exps += [M] * A.shape[0]; break
        exps.append(v)
        piv = int(A[r, c]); u = piv // (p ** v); uinv = pow(u, -1, q)
        # rows: R_s -= (A[s,c]/p^v) * uinv * R_r   (A[s,c] divisible by p^v)
        col = (A[:, c] // (p ** v)) % q
        f = (col * uinv) % q
        f[r] = 0
        rowr = A[r, :].copy()
        # avoid overflow: q < 2^31 so products < 2^62
        A = (A - (f[:, None] * rowr[None, :]) % q) % q
        A = np.delete(np.delete(A, r, axis=0), c, axis=1)
    return exps
def part(exps, M):
    d = {}
    for e in exps:
        if e >= 1: d[e if e < M else 'inf'] = d.get(e if e < M else 'inf', 0) + 1
    return dict(sorted(d.items(), key=lambda kv: (kv[0] == 'inf', kv[0] if kv[0] != 'inf' else 0)))
if __name__ == '__main__':
    nmax = int(sys.argv[1]); out = {}
    for n in range(1, nmax + 1):
        res = {}
        for name, Lf in (('cube', lap_cube), ('fold', lap_fold)):
            L = Lf(n); res[name] = {}
            for p, M in ((2, 30), (3, 19), (5, 13), (7, 11), (11, 8), (13, 8)):
                if p > 2 and p > n: continue  # odd primes up to n suffice for Bai / C5 (checked: listed primes)
                t = time.time(); e = smith_local(L, p, M)
                res[name][p] = part(e, M)
        out[n] = res
        print(n, json.dumps(res), flush=True)
    json.dump(out, open('checks/m2_smith_out.json', 'w'))
