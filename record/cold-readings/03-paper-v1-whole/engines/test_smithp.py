"""control for smithp: (a) vs sympy smith_normal_form on small Laplacians; (b) Bai's odd part of K(Q_n), n <= 9;
(c) negative: a deliberately wrong expectation must be rejected."""
import sys
from collections import Counter
from math import comb
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from smithp import smithp, BIG
from smith2 import cube_laplacian, folded_laplacian
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
def vp(x, p):
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
ok = True
for L in [cube_laplacian(3), cube_laplacian(4), folded_laplacian(4), folded_laplacian(5)]:
    S = smith_normal_form(Matrix(L.tolist()), domain=ZZ)
    for p in (3, 5):
        exp = Counter()
        for i in range(S.shape[0]):
            d = int(S[i, i]); exp[BIG if d == 0 else vp(abs(d), p)] += 1
        got = smithp(L, p)
        ok &= (got == exp)
print("vs sympy:", "PASS" if ok else "FAIL")
ok2 = True; neg = True
for n in range(2, 10):
    for p in (3, 5, 7):
        got = Counter({e: c for e, c in smithp(cube_laplacian(n), p).items() if e not in (0, BIG)})
        pred = Counter()
        for j in range(1, n + 1):
            if vp(j, p): pred[vp(j, p)] += comb(n, j)
        ok2 &= (got == pred)
        wrong = Counter(pred); wrong[1] += 1
        neg &= (got != wrong)
print("Bai odd part n<=9:", "PASS" if ok2 else "FAIL", "| negative control rejected:", "PASS" if neg else "FAIL")
