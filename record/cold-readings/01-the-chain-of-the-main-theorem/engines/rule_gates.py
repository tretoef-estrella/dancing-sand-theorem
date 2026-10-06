# rule_gates.py — C-R0 (two forms of the rule agree) and C-M0 (fusion = character peeling).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from myrule import *

# C-M0
okm = 0
for n in range(1, 65):
    a = mult_fusion(n)
    b = mult_peel(n)
    if a == b:
        okm += 1
    else:
        print('C-M0 MISMATCH n', n, a[:5], b[:5])
    # dimension check: sum m * dim = 2^n
    assert sum(c * (1 << (digits(l)[0] + len(digits(l)[1]))) for l, c in a) == 2 ** n
print(f'C-M0 fusion = peeling: {okm}/64 (dimension check 2^n passed for every n)')

# C-R0
ok_naive = ok_pool = tot = 0
first_bad = None
pooled_cells = 0
for lam in range(1, 64):
    for i in range(1, 41):
        tot += 1
        uB = big_clocks_B(lam, i, pool=False)
        uX = big_clocks_X(lam, i, pool=False)
        if uB == uX:
            ok_naive += 1
        elif first_bad is None:
            first_bad = (lam, i, uB, uX)
        pB = big_clocks_B(lam, i)
        pX = big_clocks_X(lam, i)
        if sorted(pB) == sorted(pX):
            ok_pool += 1
        if pB != uB:
            pooled_cells += 1
print(f'C-R0 naive clocks equal value by value: {ok_naive}/{tot}; pooled multisets equal: {ok_pool}/{tot}')
print('first naive mismatch:', first_bad)
print('cells (lam<=63, 1<=i<=40) where pooling changes something:', pooled_cells)
# control for C-R0: the constant without kappa(m,K) must fail somewhere
fails = 0
for lam in range(1, 64):
    k, I = digits(lam)
    for i in range(1, 41):
        m = i - 1
        wrong = [e - kappa(m, 1 << k) for e in big_clocks_X(lam, i)]
        if sorted(wrong) != sorted(big_clocks_B(lam, i)):
            fails += 1
print('C-R0 control (constant without kappa(m,K)) differs in', fails, 'cells')
# where does pooling first enter the cube? smallest n with a pooled family cell
for n in range(1, 41):
    hit = []
    for lam, c in mult_fusion(n):
        i = (n - lam) // 2
        u = big_clocks_B(lam, i, pool=False)
        p = big_clocks_B(lam, i)
        if u != p:
            hit.append((lam, i))
    if hit:
        print('first n with a pooled cell:', n, hit)
        break
