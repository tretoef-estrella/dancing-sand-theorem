# g9_explore.py — «Grepy el volador 9». Exploration of the CLEANLINESS of the dance (what invariant keeps every move clean).
# E1: compare, level by level, the dance of A = payments + h(F) with the dance of its payment-free part A0 = h(F):
#     min valuation of G_h(A) - G_h(A0) over every coefficient, entry and floor; and whether G_h(A0) is floor-constant.
import sys, random
sys.path.insert(0, 'engines'); sys.dont_write_bytecode = True
from fractions import Fraction
from fdance import E, step, tree, v2, add, smul, mul, inv, sigma_elem
from tilt_dp import dfact_odd

INF = 10 ** 9

def weights(kind, mmax, rnd=None):
    """F^(m) coefficients h_m, m = 1..mmax (h_1 included)."""
    if kind == 'sigma': return {1: Fraction(1)}
    if kind == 'rand': d = {m: Fraction(rnd.randint(-5, 5)) for m in range(2, mmax + 1)}; d[1] = Fraction(1); return d
    # tanh / coth: from Ch, Sh series
    L = mmax
    Ch = E(L, {s: [Fraction(1, dfact_odd(s))] * (L + 1) for s in range(L + 1)})
    Sh = E(L, {s: [Fraction(1, dfact_odd(s + 1))] * (L + 1) for s in range(L + 1)})
    one = E(L, {0: [Fraction(1)] * (L + 1)})
    eps = 1 if kind == 'tanh' else -1
    W = mul(add(Ch, one, -eps), inv(Sh))
    if kind == 'coth': W = smul(Fraction(3), W)
    return {m: W.get(m, L) for m in range(1, mmax + 1) if W.get(m, L) != 0}

def elem(l, h, pay):
    """element on T(l): pay(f) + sum_m h_m F^(m)."""
    c = {m: [Fraction(v)] * (l + 1) for m, v in h.items() if m <= l}
    if pay is not None: c[0] = [Fraction(pay(f)) for f in range(l + 1)]
    return E(l, {m: t for m, t in c.items() if any(t)})

def levels(G, l):
    L = l; out = []
    for mv in tree(l):
        Lp = (L - 1) // 2 if mv == 'phi' else (L - 2) // 2
        try:
            G, t = step(G, mv, Lp); L = Lp
        except ZeroDivisionError:
            return out, 'pivot0'
        if G is None: return out, 'pivot'
        out.append((mv, G, L, t))
        if t < 1: return out, 'tray'
    return out, 'ok'

def minval_diff(G1, G2):
    mv = INF
    for r1, r2 in zip(G1, G2):
        for a, b in zip(r1, r2):
            d = add(a, b, -1)
            for t in d.c.values():
                for v in t:
                    if v != 0: mv = min(mv, v2(v))
    return mv

def floor_const_val(G):
    """min valuation of g_m(f+1) - g_m(f) over every entry, m >= 1 (how floor-dependent the F-terms are)."""
    mv = INF
    for row in G:
        for e in row:
            for m, t in e.c.items():
                if m == 0: continue
                vals = [t[f] for f in range(m, e.L + 1)]
                for a, b in zip(vals, vals[1:]):
                    if a != b: mv = min(mv, v2(b - a))
    return mv

def e1(lmax, alpha, cs, kinds, seed=5, mmax=None):
    rnd = random.Random(seed)
    for l in range(2, lmax + 1):
        for kind in kinds:
            h = weights(kind, l, rnd)
            for c in cs:
                pay = lambda f, c=c: 2 ** alpha * (f + c)
                LA, sA = levels([[elem(l, h, pay)]], l)
                L0, s0 = levels([[elem(l, h, None)]], l)
                row = []
                for (mv, GA, L, t), (_, G0, _, t0) in zip(LA, L0):
                    row.append('%s:d%s,fc0=%s,fcA=%s' % (mv[0], fmt(minval_diff(GA, G0)), fmt(floor_const_val(G0)), fmt(floor_const_val(GA))))
                print('l', l, kind, 'c', c, 'A:', sA, 'A0:', s0, ' '.join(row), flush=True)

def fmt(x): return 'inf' if x >= INF else str(x)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'e1':
        e1(int(sys.argv[2]), int(sys.argv[3]), (1, 2, 3), sys.argv[4].split(','))
    print('END')

# ---------- E2: cleanliness on deep words; payment structures ----------
def elem_general(l, h, pay, ucoef=None):
    """pay(f) + U(f) F + sum_{m>=2} h_m F^(m); ucoef(f) multiplies the F coefficient."""
    c = {m: [Fraction(v)] * (l + 1) for m, v in h.items() if m <= l and m >= 2}
    c[1] = [Fraction(h.get(1, 1)) * (ucoef(f) if ucoef else 1) for f in range(l + 1)]
    if pay is not None: c[0] = [Fraction(pay(f)) for f in range(l + 1)]
    return E(l, {m: t for m, t in c.items() if any(t)})

def e2(lmax, kind, alpha, seed=11, lmin=2):
    rnd = random.Random(seed); tot = clean = modok = 0; bad = []
    for l in range(lmin, lmax + 1):
        for c in (1, 2, 3, 4):
            if kind in ('tanh', 'coth'):
                h = weights(kind, l)
                if kind == 'coth':
                    j = 2 * c - 1; pay = lambda f, j=j: 3 * (2 * (2 * f + j) + 2) * 2 ** (alpha - 2)
                else:
                    j = 2 * c; pay = lambda f, j=j: 2 * (2 * f + j) * 2 ** (alpha - 2)
                uc = None
            else:
                h = weights('rand', l, rnd)
                if kind == 'alpha1z2odd':
                    if h[2] % 2 == 0: h[2] += 1
                if kind == 'generic':
                    qs = [rnd.randint(-9, 9) or 1 for _ in range(l + 1)]
                    pay = lambda f, qs=qs: 4 * qs[f]
                elif kind.startswith('genpar'):
                    sh = 2 ** int(kind[6:])
                    qs = [f + c + sh * rnd.randint(-9, 9) for f in range(l + 1)]
                    pay = lambda f, qs=qs: 4 * qs[f]
                elif kind == 'oddW':
                    Ws = [2 * rnd.randint(-9, 9) + 1 for _ in range(l + 1)]
                    pay = lambda f, Ws=Ws, c=c: 2 ** alpha * (f + c) * Ws[f]
                elif kind == 'oddunits':
                    Ws = [2 * rnd.randint(-9, 9) + 1 for _ in range(l + 1)]
                    pay = lambda f, Ws=Ws, c=c: 2 ** alpha * (f + c) * Ws[f]
                else:
                    pay = lambda f, c=c: 2 ** alpha * (f + c)
                uc = None
                if kind == 'oddU':
                    Us = [2 * rnd.randint(-9, 9) + 1 for _ in range(l + 1)]
                    uc = lambda f, Us=Us: Us[f]
                if kind == 'oddunits':
                    Us = [2 * rnd.randint(-9, 9) + 1 for _ in range(l + 1)]
                    uc = lambda f, Us=Us: Us[f]
            A = elem_general(l, h, pay, uc)
            LA, sA = levels([[A]], l)
            tot += 1; clean += (sA == 'ok')
            if sA != 'ok' and len(bad) < 6: bad.append((l, c, sA, len(LA)))
            if kind in ('tanh', 'coth', 'rand'):
                A0 = elem_general(l, h, None, uc)
                L0, s0 = levels([[A0]], l)
                ok = (s0 == 'ok') and all(minval_diff(GA, G0) >= 1 for (_, GA, _, _), (_, G0, _, _) in list(zip(LA, L0))[:-1])
                modok += ok
                if not ok and len(bad) < 6: bad.append((l, c, 'mod2-differs', s0))
    print('E2', kind, 'alpha', alpha, 'cells', tot, 'clean', clean, 'G_h(A)=G_h(A0) mod 2', modok, 'first bad', bad, flush=True)

if __name__ == '__main__' and sys.argv[1] == 'e2':
    e2(int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), seed=int(sys.argv[5]) if len(sys.argv) > 5 else 11)
    print('END-e2')

# ---------- E4: the structure of D_h = G_h(A) - G_h(A0), entry by entry, coefficient by coefficient ----------
def fdiff_vals(t, lo, hi):
    """valuations of the values, first and second floor-differences of a coefficient table on floors lo..hi."""
    vals = [t[f] for f in range(lo, hi + 1)]
    d1 = [b - a for a, b in zip(vals, vals[1:])]
    d2 = [b - a for a, b in zip(d1, d1[1:])]
    mv = lambda xs: min((v2(x) for x in xs if x != 0), default=INF)
    return mv(vals), mv(d1), mv(d2)

def e4(l, kind, alpha, c, mmax=4):
    h = weights(kind, l)
    j = 2 * c
    pay = (lambda f: 2 ** alpha * (f + c)) if kind != 'coth' else (lambda f: 3 * 2 ** alpha * (f + c))
    LA, sA = levels([[elem_general(l, h, pay)]], l)
    L0, s0 = levels([[elem_general(l, h, None)]], l)
    print('E4', kind, 'l', l, 'alpha', alpha, 'c', c, 'status', sA, s0, 'word', tree(l))
    for lev, ((mv, GA, L, t), (_, G0, _, _)) in enumerate(zip(LA, L0)):
        r = len(GA)
        out = []
        for s in range(r):
            for u in range(r):
                d = add(GA[s][u], G0[s][u], -1)
                for m in range(0, mmax + 1):
                    tt = [d.get(m, f) for f in range(L + 1)]
                    if m > L: continue
                    a, b, cc = fdiff_vals(tt, m, L)
                    if a < INF or m == 0:
                        out.append('(%d%d)m%d:%s/%s/%s' % (s, u, m, fmt(a), fmt(b), fmt(cc)))
        print('  level', lev + 1, 'after', mv, 'r', r, 'L', L, ' '.join(out[:40]))

if __name__ == '__main__' and sys.argv[1] == 'e4':
    e4(int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    print('END-e4')

# ---------- E5: sensitivity — perturb A_tanh by 2^j phi(D) F^(m), phi an ARBITRARY integer floor function ----------
def e5(lmax, alpha=2, seed=21, js=(1, 2, 3, 4, 5, 6), ms=(0, 1, 2, 3, 4)):
    rnd = random.Random(seed)
    for m in ms:
        for j in js:
            tot = clean = 0; first = None
            for l in range(2, lmax + 1):
                h = weights('tanh', l)
                for c in (1, 2, 3, 4):
                    pay = lambda f, c=c: 2 ** alpha * (f + c)
                    A = elem_general(l, h, pay)
                    if m <= l:
                        phi = [Fraction(2 ** j * rnd.randint(-9, 9)) for _ in range(l + 1)]
                        A = add(A, E(l, {m: [phi[f] if f >= m else Fraction(0) for f in range(l + 1)]}))
                    LA, sA = levels([[A]], l)
                    tot += 1; clean += (sA == 'ok')
                    if sA != 'ok':
                        lev = len(LA)
                        if first is None or lev < first[0]: first = (lev, l, c, sA)
            print('E5 m', m, 'j', j, 'cells', tot, 'clean', clean, 'earliest failure (move, l, c, kind)', first, flush=True)

if __name__ == '__main__' and sys.argv[1] == 'e5':
    e5(int(sys.argv[2]))
    print('END-e5')

# ---------- E6: translation invariance in the dancer index (the Boolean structure) ----------
def dancer_sets(r):
    """dancer index i -> frozenset of paso positions where C was chosen (bit p of the index, MSB = first paso)."""
    k = r.bit_length() - 1
    return [frozenset(p for p in range(k) if (i >> (k - 1 - p)) & 1) for i in range(r)]

def ti_defect(G, L):
    """min valuation of differences between entries with the same D minus D' (D' subset of D), per m (F-index)."""
    r = len(G); S = dancer_sets(r); groups = {}
    for i in range(r):
        for j in range(r):
            if not S[j] <= S[i]:
                assert not G[i][j].c, 'entry outside the Boolean order'
                continue
            groups.setdefault(S[i] - S[j], []).append((i, j))
    out = {}
    for delta, prs in groups.items():
        i0, j0 = prs[0]
        for (i, j) in prs[1:]:
            d = add(G[i][j], G[i0][j0], -1)
            for m, t in d.c.items():
                for f in range(m, L + 1):
                    if t[f] != 0:
                        out[m] = min(out.get(m, INF), v2(t[f]))
    return out

def e6(l, kind, alpha, c):
    h = weights(kind, l)
    pay = (lambda f: 2 ** alpha * (f + c))
    LA, sA = levels([[elem_general(l, h, pay)]], l)
    L0, s0 = levels([[elem_general(l, h, None)]], l)
    LS, sS = levels([[elem_general(l, {1: Fraction(1)}, pay)]], l)
    print('E6', kind, 'l', l, 'alpha', alpha, 'c', c, 'status', sA, s0, sS, 'word', tree(l))
    for lev, ((mv, GA, L, t), (_, G0, _, _), (_, GS, _, _)) in enumerate(zip(LA, L0, LS)):
        dA = ti_defect(GA, L); d0 = ti_defect(G0, L); dS = ti_defect(GS, L)
        f = lambda d: ' '.join('m%d:%s' % (m, fmt(v)) for m, v in sorted(d.items())[:6])
        print('  level', lev + 1, mv, 'r', len(GA), '| A:', f(dA), '| A0:', f(d0), '| Sigma:', f(dS))

if __name__ == '__main__' and sys.argv[1] == 'e6':
    e6(int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]))
    print('END-e6')
