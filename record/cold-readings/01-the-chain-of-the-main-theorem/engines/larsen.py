# larsen.py — P-LARSEN: Larsen's V^{(x)2} fusion rule (arXiv:2405.16015 §2, as quoted) vs the flights' fusion recursion.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from myrule import mult_fusion, v2

def V2T(two_n):
    n = two_n // 2
    r = v2(n + 1)
    out = {2 * n + 2: 1}
    top = r + 1 if n != 2 ** r - 1 else r
    for i in range(1, top + 1):
        lam = 2 * n + 2 - 2 ** i
        out[lam] = out.get(lam, 0) + 2
    return out

ok = 0
cur = {0: 1}
for k in range(1, 33):
    new = {}
    for lam, c in cur.items():
        for mu, e in V2T(lam).items():
            new[mu] = new.get(mu, 0) + c * e
    cur = new
    ok += (tuple(sorted(cur.items())) == mult_fusion(2 * k))
    if tuple(sorted(cur.items())) != mult_fusion(2 * k):
        print('MISMATCH n =', 2 * k)
print(f'P-LARSEN: Larsen V^2 rule = flights fusion recursion at n = 2..64 even: {ok}/32')
# control: drop the exception (keep T(0) terms) -> must differ
cur = {0: 1}; diff = 0
for k in range(1, 33):
    new = {}
    for lam, c in cur.items():
        n = lam // 2; r = v2(n + 1)
        d = {2 * n + 2: 1}
        for i in range(1, r + 2):
            d[2 * n + 2 - 2 ** i] = d.get(2 * n + 2 - 2 ** i, 0) + 2
        for mu, e in d.items():
            new[mu] = new.get(mu, 0) + c * e
    cur = new
    diff += tuple(sorted(cur.items())) != mult_fusion(2 * k)
print('control (exception dropped) differs at', diff, 'of 32 even n')
