"""test_smith2.py — controls for engines/smith2.py (it must be able to fail).

1. Known diagonals diag(2^a_j * odd_j, ..., 0) scrambled by random unimodular integer matrices (Python ints,
   exact), reduced mod 2^E: smith2 must return exactly the multiset {a_j} ∪ {BIG}.
   NEGATIVE control: a deliberately wrong expected multiset must be reported as a mismatch.
2. Small Laplacians against sympy's smith_normal_form over ZZ.
3. E = 32 against E = 64 on the cube Laplacians.
"""
import random
import sys
import numpy as np
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from smith2 import smith2, BIG, cube_laplacian, folded_laplacian, x1x2_quotient_laplacian

random.seed(20261005)


def scramble(diag):
    n = len(diag)
    A = [[0] * n for _ in range(n)]
    for i, d in enumerate(diag):
        A[i][i] = d
    for _ in range(6 * n):
        i, j = random.sample(range(n), 2)
        c = random.randint(-3, 3)
        if random.random() < 0.5:
            A[i] = [a + c * b for a, b in zip(A[i], A[j])]   # row op
        else:
            for r in range(n):
                A[r][i] += c * A[r][j]                        # column op
    for _ in range(2):  # random permutations
        perm = list(range(n)); random.shuffle(perm)
        A = [A[p] for p in perm]
        perm = list(range(n)); random.shuffle(perm)
        A = [[row[p] for p in perm] for row in A]
    return A


def reduce_signed(A, E):
    M = 1 << E
    return np.array([[((a % M) - M if (a % M) >= (M >> 1) else (a % M)) for a in row] for row in A], dtype=np.int64)


ok = True
for E in (32, 64):
    for trial in range(40):
        n = random.randint(2, 14)
        exps = [random.randint(0, 12) for _ in range(n - 1)]
        diag = [(1 << a) * random.choice([1, 3, 5, 7, -1, -3, 9, 11]) for a in exps] + [0]
        A = scramble(diag)
        got = smith2(reduce_signed(A, E), E)
        exp = Counter(exps); exp[BIG] += 1
        if got != exp:
            ok = False
            print("FAIL diag", E, trial, exps, dict(got))
        # negative control: wrong expectation must not match
        wrong = Counter(exps); wrong[BIG] += 1; wrong[exps[0]] -= 1; wrong[exps[0] + 1] += 1
        wrong = +wrong
        if got == wrong:
            ok = False
            print("NEGATIVE CONTROL DID NOT FAIL", E, trial)
print("diag-scramble tests:", "PASS" if ok else "FAIL")

# 2. sympy
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form


def sympy_val(L):
    S = smith_normal_form(Matrix(L.tolist()), domain=ZZ)
    c = Counter()
    for i in range(S.shape[0]):
        d = int(S[i, i])
        if d == 0:
            c[BIG] += 1
        else:
            d = abs(d); v = 0
            while d % 2 == 0:
                d //= 2; v += 1
            c[v] += 1
    return c


ok2 = True
for name, Lf, ns in (("cube", cube_laplacian, range(1, 5)), ("folded", folded_laplacian, range(1, 6)),
                     ("x1x2", x1x2_quotient_laplacian, range(2, 6))):
    for n in ns:
        L = Lf(n)
        a = smith2(L, 32); b = sympy_val(L)
        print(name, n, "smith2", dict(sorted(a.items())), "sympy", dict(sorted(b.items())), "OK" if a == b else "MISMATCH")
        ok2 &= (a == b)
print("sympy comparison:", "PASS" if ok2 else "FAIL")

ok3 = True
for n in range(1, 10):
    L = cube_laplacian(n)
    a, b = smith2(L, 32), smith2(L, 64)
    ok3 &= (a == b)
    print("E32 vs E64 cube", n, "OK" if a == b else "MISMATCH")
print("E32 vs E64:", "PASS" if ok3 else "FAIL")
print("ALL:", "PASS" if (ok and ok2 and ok3) else "FAIL")
