"""check31.py — mission check 3.1: the rule of §1.2 (engines/rule.py, from §1 alone) against the 2-adic Smith
form of the Laplacians (engines/smith2.py). Usage: python3 engines/check31.py N_MIN N_MAX [E]

Per n:
  A. rule(n) == Syl_2(L(Q_n)) ⊕ Z_2                                   (Main Theorem)
  B. exactly one free summand; sum of finite exponents == v_2(#spanning trees) (Kirchhoff, product formula)
  C. Syl_2(L(folded n-cube)) == 2·Syl_2(L(Q_n))                        (Theorem DW), and its order check
  D. (Z/2)^{a_n} ⊕ (folded raised by one) == Syl_2 K(Q_n)              (the "equivalently" form)
CONTROLS (each must FAIL for some n):
  c1. rule with the lowest digit of I dropped  != Smith form
  c2. a_n ± 1 in the form D                    != Syl_2 K(Q_n)
  c3. Q_n/<x1 x2> in place of the folded cube  != 2·Syl_2 K(Q_n)
"""
import sys
import time
import json
from collections import Counter
from math import comb
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import rule
from rule import INF, fmt
from smith2 import smith2, BIG, cube_laplacian, folded_laplacian, x1x2_quotient_laplacian, syl2_from_smith

assert INF == BIG


def v2(x):
    return (x & -x).bit_length() - 1


def v2_tau_cube(n):
    return 2 ** n - n - 1 + sum(comb(n, j) * v2(j) for j in range(1, n + 1))


def v2_tau_folded(n):
    # eigenvalues 2|J| for J ⊆ [n] of even size; tau = prod_{J != ∅} 2|J| / 2^(n-1)
    return sum(comb(n, j) * (1 + v2(j)) for j in range(2, n + 1, 2)) - (n - 1)


def finite_sum(g):
    return sum(e * c for e, c in g.items() if e != INF)


def raise1(g):
    return Counter({(e if e == INF else e + 1): c for e, c in g.items()})


nmin, nmax = int(sys.argv[1]), int(sys.argv[2])
E = int(sys.argv[3]) if len(sys.argv) > 3 else 32
out = {}
allok = True
ctrl_fail = {"c1": [], "c2": [], "c3": []}
for n in range(nmin, nmax + 1):
    t0 = time.time()
    cube = syl2_from_smith(smith2(cube_laplacian(n), E))
    t1 = time.time()
    fold = syl2_from_smith(smith2(folded_laplacian(n), E))
    t2 = time.time()
    x12 = syl2_from_smith(smith2(x1x2_quotient_laplacian(n), E)) if n >= 2 else None
    t3 = time.time()
    r = rule.syl2_plus_free(n)
    A = (r == cube)
    B = (cube[INF] == 1 and finite_sum(cube) == v2_tau_cube(n) and fold[INF] == 1
         and finite_sum(fold) == v2_tau_folded(n))
    C = (fold == rule.fold(cube))
    an = 2 ** (n - 2) - 2 ** ((n - 2) // 2) if n >= 2 else 0
    Dform = lambda a: raise1(fold) + Counter({1: a}) if a > 0 else raise1(fold)
    D = (Dform(an) == cube) if n >= 2 else True
    ok = A and B and C and D
    allok &= ok
    # controls
    rd = rule.syl2_plus_free(n, drop_digit_mode="lowest")
    if rd != cube:
        ctrl_fail["c1"].append(n)
    if n >= 2 and Dform(an + 1) != cube and (an - 1 < 0 or Dform(an - 1) != cube):
        ctrl_fail["c2"].append(n)
    if x12 is not None and x12 != rule.fold(cube):
        ctrl_fail["c3"].append(n)
    print(f"n={n:2d} A(rule==Smith)={A} B(free=1,orders)={B} C(DW)={C} D(a_n form)={D} "
          f"| t_cube={t1-t0:.1f}s t_fold={t2-t1:.1f}s t_x12={t3-t2:.1f}s", flush=True)
    print(f"      Syl2 K(Q_{n}) = {fmt(cube)}", flush=True)
    print(f"      Syl2 Kbar({n}) = {fmt(fold)}", flush=True)
    if x12 is not None:
        print(f"      Syl2 K(Q_{n}/<x1x2>) = {fmt(x12)}   2·Syl2K(Q_n) = {fmt(rule.fold(cube))}", flush=True)
    if not A:
        print(f"      RULE  = {fmt(r)}", flush=True)
    out[n] = {"cube": {str(k): v for k, v in cube.items()}, "fold": {str(k): v for k, v in fold.items()},
              "x1x2": ({str(k): v for k, v in x12.items()} if x12 is not None else None)}
print("CONTROLS failed (as they must) at n =", ctrl_fail, flush=True)
print("ALL MAIN CHECKS:", "PASS" if allok else "FAIL", flush=True)
json.dump(out, open(f"scratch/smith_results_{nmin}_{nmax}.json", "w"), indent=0)
