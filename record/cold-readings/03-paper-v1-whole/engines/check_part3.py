"""check_part3.py — (1) Corollary 1.4 odd part (p = 3,5,7) on the folded Laplacian; (2) §11 Q2 turned lid.
Cold reader, 2026-10-05.  Usage: python3 engines/check_part3.py NMAX_ODD NMAX_LID"""
import sys
from collections import Counter
from math import comb
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from smith2 import smith2, cayley_laplacian, folded_laplacian, cube_laplacian, syl2_from_smith, BIG
from smithp import smithp
import rule

N1, N2 = int(sys.argv[1]), int(sys.argv[2])

def vp(x, p):
    v = 0
    while x % p == 0:
        x //= p; v += 1
    return v

bad = 0; ctrl = 0
for n in range(2, N1 + 1):
    L = folded_laplacian(n)
    for p in (3, 5, 7):
        got = Counter({e: c for e, c in smithp(L, p).items() if e != 0 and e != BIG})
        pred = Counter(); wrong = Counter()
        for j in range(1, n + 1):
            e = vp(2 * j, p)
            if e:
                wrong[e] += comb(n, j)
                if j % 2 == 0:
                    pred[e] += comb(n, j)
        if got != pred:
            bad += 1; print("Cor1.4 odd FAIL", n, p, dict(got), dict(pred))
        if got != wrong:
            ctrl += 1
        print(f"n={n} p={p} Syl_p Kbar = {dict(sorted(got.items()))}  pred {dict(sorted(pred.items()))}", flush=True)
print(f"Corollary 1.4 odd part: {bad} failures over n=2..{N1}, p=3,5,7; control (all j) differs in {ctrl} cases", flush=True)

def lid(a, b):
    d = a + b - 1
    gens = [1 << i for i in range(a)]
    if b == 1:
        gens.append(0)
    else:
        gens += [1 << (a + i) for i in range(b - 1)] + [((1 << (b - 1)) - 1) << a]
    return cayley_laplacian(d, gens)

bad2 = 0; only = 0; badonly = 0
for n in range(3, N2 + 1):
    G = {}
    for b in range(1, n + 1):
        a = n - b
        G[(a, b)] = syl2_from_smith(smith2(lid(a, b), 32))
    for b in range(1, n):
        a = n - b
        if a >= 1 and G[(a, b)] != G[(b, a)]:
            bad2 += 1; print("LID symmetry FAIL", n, a, b)
    half = rule.fold(syl2_from_smith(smith2(cube_laplacian(n), 32)))
    hits = [b for b in range(1, n + 1) if G[(n - b, b)] == half]
    if hits != [n]:
        badonly += 1; print("2·Syl2 K(Q_n) equals lid for b in", hits, "n =", n)
    print(f"n={n}: symmetry pairs ok; 2·Syl2K(Q_n) matches b in {hits}", flush=True)
print(f"turned lid: {bad2} symmetry failures (n=3..{N2}); 'only b = n' failures: {badonly}", flush=True)
