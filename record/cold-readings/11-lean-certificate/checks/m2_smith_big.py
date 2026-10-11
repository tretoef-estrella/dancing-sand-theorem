# M2: as m2_smith.py, p = 2 only, for larger n, with a fast 2-adic valuation (lowest set bit).
import numpy as np, sys, json
sys.path.insert(0, 'checks')
from m2_smith import lap_cube, lap_fold, part
def smith2(L, M=30):
    q = 1 << M
    A = np.mod(L.astype(np.int64), q); exps = []
    while A.shape[0] > 0:
        low = A & (-A)
        V = np.where(A == 0, M, np.log2(np.where(A == 0, 1, low)).astype(np.int64))
        r, c = np.unravel_index(np.argmin(V), V.shape); v = int(V[r, c])
        if v >= M: exps += [M] * A.shape[0]; break
        exps.append(v)
        u = int(A[r, c]) >> v; uinv = pow(u, -1, q)
        f = ((A[:, c] >> v) * uinv) % q; f[r] = 0
        A = (A - (f[:, None] * A[r, :][None, :]) % q) % q
        A = np.delete(np.delete(A, r, axis=0), c, axis=1)
    return exps
out = json.load(open('checks/m2_smith_out.json'))
for n in map(int, sys.argv[1:]):
    res = {'cube': {'2': part(smith2(lap_cube(n)), 30)}, 'fold': {'2': part(smith2(lap_fold(n)), 30)}}
    # consistency with the slow routine where both exist
    if str(n) in out: print('n', n, 'same as slow routine:', res['cube']['2'] == out[str(n)]['cube']['2'] if False else None)
    out[str(n)] = res; print(n, json.dumps(res), flush=True)
json.dump(out, open('checks/m2_smith_out_big.json', 'w'))
