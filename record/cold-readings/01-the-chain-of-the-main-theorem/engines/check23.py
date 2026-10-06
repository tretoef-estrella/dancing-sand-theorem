# check23.py — checks 2 (Bai 2003) and 3 (Gao–Marx-Kuo–McDonald–Yuen, JMM poster) against the rule (my code).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from myrule import group_rule, fmt, v2

# Bai, LAA 369 (2003) p. 260, transcribed by me from the rendered page (no superscript = multiplicity 1).
# Each entry: list of (order, multiplicity)
BAI = {
    2: [(4, 1)],
    3: [(2, 1), (8, 2)],
    4: [(2, 2), (8, 4), (32, 1)],
    5: [(2, 6), (8, 4), (16, 1), (64, 4)],
    6: [(2, 12), (4, 4), (8, 1), (32, 4), (64, 10)],
    7: [(2, 28), (4, 1), (16, 8), (32, 6), (64, 14), (128, 6)],
    8: [(2, 56), (4, 2), (16, 16), (32, 12), (64, 28), (128, 12), (1024, 1)],
    9: [(2, 120), (4, 10), (16, 16), (32, 26), (64, 48), (128, 26), (512, 1), (2048, 8)],
    10: [(2, 240), (4, 36), (8, 26), (32, 16), (64, 148), (256, 1), (1024, 26), (2048, 18)],
    11: [(2, 496), (4, 66), (8, 32), (16, 100), (64, 164), (128, 1), (512, 100), (2048, 64)],
}


def finite(G):
    return {e: c for e, c in G.items() if e != 'Z' and c}


def kth_largest(G, j):
    """exponent of the j-th largest cyclic 2-factor (1-based), from multiplicities"""
    acc = 0
    for e in sorted(finite(G), reverse=True):
        acc += G[e]
        if acc >= j:
            return e
    return 0


def mx(n_upper):
    """max_{1 <= x < n_upper} (v2(x) + x)"""
    return max(v2(x) + x for x in range(1, n_upper))


ctrl = {'none': None, 'nopool': dict(pool=False), 'carries_m': dict(form='X', ctrl='m_only')}

# ---- check 2
ok = 0
for n, lst in BAI.items():
    G = finite(group_rule(n))
    B = {v2(order): mult for order, mult in lst}
    ok += (G == B)
    if G != B:
        print('C2-table MISMATCH n', n, G, B)
print(f'C2-table: Bai p.260 = rule {ok}/{len(BAI)}')

okc = oka = okf = 0
gf = [0] * 64  # a_{n+3} = coefficient of x^n in 1/((1-2x)(1-2x^2))
for nn in range(64):
    gf[nn] = sum(2 ** (nn - 2 * j) * 2 ** j for j in range(nn // 2 + 1))
for n in range(1, 61):
    G = group_rule(n)
    nf = sum(finite(G).values())
    okc += (nf == 2 ** (n - 1) - 1) and G.get('Z') == 1
    a = G.get(1, 0)
    if n >= 3:
        oka += (a == gf[n - 3])
    if n >= 2:
        okf += (a == 2 ** (n - 2) - 2 ** ((n - 2) // 2))
print(f'C2-count: 2^(n-1)-1 factors and one Z, n=1..60: {okc}/60')
print(f'C2-a_n: Z/2 count = generating function, n=3..60: {oka}/58; = 2^(n-2) - 2^floor((n-2)/2), n=2..60: {okf}/59')

# ---- check 3
for name, kw in ctrl.items():
    ok41 = ok42 = tot = 0
    ok414 = okp = 0
    first_bad = None
    for n in range(2, 65):
        G = group_rule(n, **kw) if kw else group_rule(n)
        c1 = kth_largest(G, 1)
        p41 = max(mx(n), v2(n) + n - 1)
        t41 = (c1 == p41)
        t42 = all(kth_largest(G, j) == mx(n) for j in range(2, n)) if n >= 3 else True
        if n <= 30:
            tot += 1
            ok41 += t41
            ok42 += t42
            if not (t41 and t42) and first_bad is None:
                first_bad = n
        if name == 'none':
            if n >= 3:
                p414 = max(mx(n - 1), v2(n - 1) + n - 3)
                ok414 += (kth_largest(G, n) == p414)
            if n >= 4:
                okp += (kth_largest(G, n + 1) == mx(n - 1))
            if n == 64 or n == 30:
                print(f'   (n={n}: c1={c1}, c2..c(n-1)={mx(n)}, cn={kth_largest(G, n)}, c(n+1)={kth_largest(G, n + 1)})')
    print(f'C3[{name}] n=2..30: Thm 4.1 {ok41}/{tot}, Thm 4.2 {ok42}/{tot}; first n failing: {first_bad}')
    if name == 'none':
        # n = 31..64 for information
        e41 = e42 = 0
        for n in range(31, 65):
            G = group_rule(n)
            e41 += kth_largest(G, 1) == max(mx(n), v2(n) + n - 1)
            e42 += all(kth_largest(G, j) == mx(n) for j in range(2, n))
        print(f'C3 n=31..64: Thm 4.1 {e41}/34, Thm 4.2 {e42}/34')
        print(f'C3-conj: Conj 4.14 (n-th factor) n=3..64: {ok414}/62; poster (n+1)-th n=4..64: {okp}/61')
        ok54 = 0
        for kk in range(2, 7):
            n = 2 ** kk
            A = finite(group_rule(n))
            B = finite(group_rule(n - 1))
            C = {e: 2 * c for e, c in B.items()}
            top = 2 ** kk + kk - 1
            C[top] = C.get(top, 0) + 1
            ok54 += (A == C)
        print(f'C3-conj: Conj 5.4, n = 4, 8, 16, 32, 64: {ok54}/5')
