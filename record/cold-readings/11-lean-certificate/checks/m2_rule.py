# M2: the right-hand side of the Main Theorem from the paper's rule (§1.2), written from the paper only,
# compared with the Smith forms of checks/m2_smith_out.json; then Theorem DW, Corollaries 1.4-1.7,
# Bai's odd part, against the same Smith forms.
import json, sys
from fractions import Fraction
from math import comb, floor, ceil
from functools import lru_cache
def s2(x): return bin(x).count('1')
def v2(x):
    c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)
def phi(x): return x + v2(x)
@lru_cache(None)
def Vdot(lam):
    # V.[0]=[1], V.[2l+1]=[2l+2], V.[2l+2]=2[2l+1]+Phi(V.[l]), Phi[nu]=[2nu+1]; formal sums as dicts
    if lam == 0: return {1: 1}
    if lam % 2 == 1: return {lam + 1: 1}
    l = (lam - 2) // 2
    d = {lam - 1: 2}
    for nu, c in Vdot(l).items(): d[2 * nu + 1] = d.get(2 * nu + 1, 0) + c
    return d
@lru_cache(None)
def mult(n):
    d = {0: 1}
    for _ in range(n):
        e = {}
        for lam, c in d.items():
            for mu, c2 in Vdot(lam).items(): e[mu] = e.get(mu, 0) + c * c2
        d = e
    return d
def family(lam):
    x = lam + 1; k = x.bit_length() - 1
    I = [t for t in range(k) if (x >> t) & 1]
    return k, I
def nxt(t, I, k): return min([u for u in I + [k] if u > t])
def dancers_in_o_order(I):
    from itertools import combinations
    ds = [frozenset(c) for r in range(len(I) + 1) for c in combinations(I, r)]
    return sorted(ds, key=lambda D: sum(2 ** t for t in D))
def raw_clock(lam, i, D, I, k):
    oD = sum(2 ** t for t in D); xi = lam + 1 - 2 * oD
    assert xi >= 1
    assert i + oD - 1 >= 0
    hD = sum(nxt(t, I, k) - t for t in D)
    return phi(xi) + kappa(i + oD - 1, xi) + hD
def int_antitonic_fit(x):
    # PAV for a non-increasing fit: merge while previous mean <= current mean (equal means merged).
    blocks = []  # [sum, count]
    for v in x:
        blocks.append([v, 1])
        while len(blocks) > 1 and Fraction(blocks[-2][0], blocks[-2][1]) <= Fraction(blocks[-1][0], blocks[-1][1]):
            s, c = blocks.pop(); blocks[-1][0] += s; blocks[-1][1] += c
    out = []; rounding_acted = False
    for S, p in blocks:
        r = S % p
        if r: rounding_acted = True
        out += [-(-S // p)] * r + [S // p] * (p - r)
    return out, rounding_acted
ROUNDING = []
def X(lam, i):
    k, I = family(lam)
    exps = {}
    for a in range(1, k):
        exps[a] = exps.get(a, 0) + 2 ** (len(I) + k - 1 - a)
    Ds = dancers_in_o_order(I)
    if i == 0:
        u = [raw_clock(lam, 0, D, I, k) for D in Ds[1:]]
        y, ra = int_antitonic_fit(u); exps['inf'] = exps.get('inf', 0) + 1
    else:
        u = [raw_clock(lam, i, D, I, k) for D in Ds]
        y, ra = int_antitonic_fit(u)
    if ra: ROUNDING.append((lam, i))
    assert all(y[j] >= y[j + 1] for j in range(len(y) - 1))
    for e in y: exps[e] = exps.get(e, 0) + 1
    return exps
def rhs(n):
    tot = {}
    for lam, c in mult(n).items():
        if c == 0: continue
        assert 1 <= lam <= n and lam % 2 == n % 2, (n, lam)
        for e, m in X(lam, (n - lam) // 2).items(): tot[e] = tot.get(e, 0) + c * m
    tot.pop(0, None)
    return tot
def norm(d):
    return {str(k): v for k, v in d.items() if k not in (0, '0') and v}
def lower(d):  # 2*A: drop exponent 1, lower the others by one
    out = {}
    for e, c in d.items():
        if e == 'inf': out['inf'] = out.get('inf', 0) + c
        elif int(e) >= 2: out[str(int(e) - 1)] = out.get(str(int(e) - 1), 0) + c
    return out
def aN(n): return 2 ** (n - 2) - 2 ** ((n - 2) // 2)
def g(N): return max(phi(x) for x in range(1, N))
def cr(d, r):
    l = sorted([int(e) for e, c in d.items() if e != 'inf' for _ in range(c)], reverse=True)
    return l[r - 1] if r <= len(l) else 0
def odd_bai(n, p):
    # Syl_p of (+)_{j=1}^n (Z/j)^{C(n,j)}
    d = {}
    for j in range(1, n + 1):
        e = 0; x = j
        while x % p == 0: x //= p; e += 1
        if e: d[str(e)] = d.get(str(e), 0) + comb(n, j)
    return d
def odd_fold(n, p):
    d = {}
    for j in range(2, n + 1, 2):
        e = 0; x = 2 * j
        while x % p == 0: x //= p; e += 1
        if e: d[str(e)] = d.get(str(e), 0) + comb(n, j)
    return d
if __name__ == '__main__':
    S = json.load(open(sys.argv[1]))
    fails = 0
    def chk(label, a, b):
        global fails
        ok = a == b
        if not ok: fails += 1
        print(('OK  ' if ok else 'FAIL'), label, '' if ok else f'{a} != {b}')
    for n_s, res in sorted(S.items(), key=lambda kv: int(kv[0])):
        n = int(n_s)
        cube2 = {k: v for k, v in res['cube']['2'].items()}; fold2 = res['fold']['2']
        cube2_noinf = {k: v for k, v in cube2.items() if k != 'inf'}
        fold2_noinf = {k: v for k, v in fold2.items() if k != 'inf'}
        chk(f'n={n} cube has exactly one free summand', cube2.get('inf'), 1)
        chk(f'n={n} fold has exactly one free summand', fold2.get('inf'), 1)
        R = norm(rhs(n))
        chk(f'n={n} Main Theorem: Syl2 K(Q_n) + Z_2 = RHS of the rule  {R}', cube2, R)
        chk(f'n={n} DW: Syl2 Kbar(n) = 2*Syl2 K(Q_n)', fold2_noinf, {k: v for k, v in lower(cube2_noinf).items() if k != 'inf'})
        chk(f'n={n} Cor 1.5 number of factors 2^(n-1)-1', sum(cube2_noinf.values()), 2 ** (n - 1) - 1)
        if n >= 2:
            chk(f'n={n} Cor 1.5 factors Z/2 = a_n={aN(n)}', cube2_noinf.get('1', 0), aN(n))
            # DW equivalent form: Syl2 K = (Z/2)^{a_n} + (Kbar raised by one)
            raised = {str(int(e) + 1): c for e, c in fold2_noinf.items()}
            if aN(n): raised['1'] = raised.get('1', 0) + aN(n)
            chk(f'n={n} DW equivalent form', cube2_noinf, raised)
            chk(f'n={n} L1 cyclic factors of Syl2 Kbar = 2^(n-1)-1-a_n', sum(fold2_noinf.values()), 2 ** (n - 1) - 1 - aN(n))
        if n >= 3:
            chk(f'n={n} G1 c_1', cr(cube2_noinf, 1), max(g(n), v2(n) + n - 1))
            chk(f'n={n} G1 c_2..c_(n-1)', [cr(cube2_noinf, r) for r in range(2, n)], [g(n)] * (n - 2))
            chk(f'n={n} G2 c_n', cr(cube2_noinf, n), max(g(n - 1), v2(n - 1) + n - 3))
        if n >= 4:
            chk(f'n={n} G3 c_(n+1)', cr(cube2_noinf, n + 1), g(n - 1))
            G = g(n - 1); c = [None] + [cr(cube2_noinf, r) for r in range(1, n + 2)]
            if n % 2 == 0:
                chk(f'n={n} P1', c[1:], [max(G, phi(n) - 1)] + [G] * n)
            elif phi(n - 1) <= G:
                chk(f'n={n} P2', c[1:], [G] * (n + 1))
            else:
                chk(f'n={n} P3', c[1:], [phi(n - 1)] * (n - 1) + [max(G, phi(n - 1) - 2), G])
        for p_s, d in res['cube'].items():
            if p_s == '2': continue
            chk(f'n={n} Bai odd part p={p_s}', {k: v for k, v in d.items() if k != 'inf'}, odd_bai(n, int(p_s)))
        for p_s, d in res['fold'].items():
            if p_s == '2': continue
            chk(f'n={n} C5 odd part of Kbar p={p_s}', {k: v for k, v in d.items() if k != 'inf'}, odd_fold(n, int(p_s)))
    # Corollary 1.7 where both sides are available
    for e in (1, 2, 3):
        a, b = str(2 ** e), str(2 ** e - 1)
        if a in S and (b in S or b == '0'):
            A = {k: v for k, v in S[a]['cube']['2'].items() if k != 'inf'}
            B = {k: v for k, v in S[b]['cube']['2'].items() if k != 'inf'} if b in S else {}
            rhs7 = {k: 2 * v for k, v in B.items()}; t = str(2 ** e + e - 1); rhs7[t] = rhs7.get(t, 0) + 1
            chk(f'Cor 1.7 e={e}', A, rhs7)
    print('rule rounding acted in (lam,i):', sorted(set(ROUNDING)))
    print('FAILS', fails)
