#!/usr/bin/env python3
"""Brute force for piece C18 (DP-lattices, V, V⊗M, V^{⊗n}, Weyl lattices, the dictionary).
Grepy Escribano, 7 Oct 2026. Exact integers. Each lattice: dict with
  'wt': list of weights, 'F'(r, i) -> dict j->coef, 'E'(s, i) -> dict j->coef.
Checks (W), (P0), (P1), (K) for r, s, a, b <= RMAX on every basis vector.
Controls must fail (reported as FIRES)."""
from math import comb
import itertools

def gchoose(a, b):
    """generalized binomial C(a, b), a in Z, b >= 0 (Ring.choose)"""
    num = 1
    for t in range(b): num *= (a - t)
    den = 1
    for t in range(1, b + 1): den *= t
    assert num % den == 0
    return num // den

def addv(u, v, c=1):
    w = dict(u)
    for k, x in v.items(): w[k] = w.get(k, 0) + c * x
    return {k: x for k, x in w.items() if x}

def apply(L, op, r, vec):
    out = {}
    for i, x in vec.items():
        out = addv(out, L[op](r, i), x)
    return out

def unit(i): return {i: 1}

RMAX = 5
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", m)

def check_lattice(L, name, record=True):
    bad = 0
    n = len(L['wt'])
    for i in range(n):
        w = L['wt'][i]
        for r in range(RMAX + 1):
            for j in L['F'](r, i): bad += L['wt'][j] != w - 2 * r
            for j in L['E'](r, i): bad += L['wt'][j] != w + 2 * r
        bad += L['F'](0, i) != unit(i)
        bad += L['E'](0, i) != unit(i)
        for a in range(RMAX + 1):
            for b in range(RMAX + 1):
                for op in 'FE':
                    lhs = apply(L, op, a, L[op](b, i))
                    rhs = {k: comb(a + b, a) * x for k, x in L[op](a + b, i).items()}
                    bad += lhs != rhs
        for r in range(RMAX + 1):
            for s in range(RMAX + 1):
                lhs = apply(L, 'E', s, L['F'](r, i))
                rhs = {}
                for j in range(min(r, s) + 1):
                    c = gchoose(w + s - r, j)
                    rhs = addv(rhs, apply(L, 'F', r - j, L['E'](s - j, i)), c)
                bad += lhs != rhs
    if record: ok(bad == 0, f"{name}: {bad} relation failures")
    return bad

triv = {'wt': [0], 'F': lambda r, i: {0: 1} if r == 0 else {}, 'E': lambda r, i: {0: 1} if r == 0 else {}}
def VF(r, i):
    if r == 0: return {i: 1}
    if r == 1 and i == 0: return {1: 1}
    return {}
def VE(r, i):
    if r == 0: return {i: 1}
    if r == 1 and i == 1: return {0: 1}
    return {}
V = {'wt': [1, -1], 'F': VF, 'E': VE}

def tensorV(M, wrong=None):
    m = len(M['wt'])
    idx = lambda e, i: e * m + i
    wt = [1 + M['wt'][i] for i in range(m)] + [-1 + M['wt'][i] for i in range(m)]
    def F(r, k):
        e, i = divmod(k, m)
        out = {idx(e, j): x for j, x in M['F'](r, i).items()}
        if e == 0 and r >= 1 and wrong != 'F':
            out = addv(out, {idx(1, j): x for j, x in M['F'](r - 1, i).items()})
        return out
    def E(r, k):
        e, i = divmod(k, m)
        out = {idx(e, j): x for j, x in M['E'](r, i).items()}
        if e == (1 if wrong != 'E' else 0) and r >= 1:
            out = addv(out, {idx(1 - e, j): x for j, x in M['E'](r - 1, i).items()})
        return out
    return {'wt': wt, 'F': F, 'E': E}

def weyl(lam):
    return {'wt': [lam - 2 * r for r in range(lam + 1)],
            'F': lambda t, r: {r + t: comb(r + t, t)} if r + t <= lam else {},
            'E': lambda s, r: {r - s: comb(lam - r + s, s)} if s <= r else {}}
def dweyl(lam):
    return {'wt': [lam - 2 * r for r in range(lam + 1)],
            'F': lambda t, r: {r + t: comb(lam - r, t)} if r + t <= lam and comb(lam - r, t) else {},
            'E': lambda s, r: {r - s: comb(r, s)} if s <= r else {}}

# (T1)
check_lattice(triv, "triv"); check_lattice(V, "V")
# (T4)
for lam in range(0, 9):
    check_lattice(weyl(lam), f"Delta({lam})"); check_lattice(dweyl(lam), f"Nabla({lam})")
# (T2) on several M
for lam in range(0, 7):
    check_lattice(tensorV(weyl(lam)), f"V⊗Delta({lam})"); check_lattice(tensorV(dweyl(lam)), f"V⊗Nabla({lam})")
# (T3)
Vt = [triv]
for n in range(1, 6):
    Vt.append(tensorV(Vt[-1])); check_lattice(Vt[-1], f"V^{n}")
# (T5)
ok(weyl(1)['wt'] == V['wt'] and all(weyl(1)['F'](r, i) == V['F'](r, i) and weyl(1)['E'](r, i) == V['E'](r, i)
   for r in range(4) for i in range(2)), "T5 Delta(1)=V")
ok(all(dweyl(1)['F'](r, i) == V['F'](r, i) and dweyl(1)['E'](r, i) == V['E'](r, i) for r in range(4) for i in range(2)), "T5 Nabla(1)=V")

# (L1), (L2): pure tensors of V^{⊗n}: index k = e_1 * 2^{n-1} m + ... ; set S = positions with e = 1
def pure_set(n, k):
    S = set(); m = 2 ** (n - 1)
    for t in range(n):
        e, k = divmod(k, m); m //= 2
        if e: S.add(t)
    return frozenset(S)
for n in range(1, 6):
    L = Vt[n]
    idx = {pure_set(n, k): k for k in range(2 ** n)}
    for S, k in idx.items():
        ok(L['wt'][k] == n - 2 * len(S), f"L1 weight n={n}")
        expect = {idx[S | {j}]: 1 for j in range(n) if j not in S}
        ok(L['F'](1, k) == expect, f"L1 F n={n}")
    # (L2): sigma s_S = sum s_{S+j} + 2|S| s_S  equals (F + n - H) on the pure tensor
    for S, k in idx.items():
        lhs = addv(L['F'](1, k), {k: n - L['wt'][k]})
        rhs = addv({idx[S | {j}]: 1 for j in range(n) if j not in S}, {k: 2 * len(S)})
        ok(lhs == rhs, f"L2 n={n}")

# ---- controls ----
fires = 0; ctrl = 0
def control(cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond)
# 1: Kostant with C(w + r - s) instead of C(w + s - r) fails on Delta(3)
def wrongK(L):
    bad = 0
    for i in range(len(L['wt'])):
        w = L['wt'][i]
        for r in range(4):
            for s in range(4):
                lhs = apply(L, 'E', s, L['F'](r, i)); rhs = {}
                for j in range(min(r, s) + 1):
                    rhs = addv(rhs, apply(L, 'F', r - j, L['E'](s - j, i)), gchoose(w + r - s, j))
                bad += lhs != rhs
    return bad
control(wrongK(weyl(3)) > 0)
# 2: V⊗M without the b_1 term of F fails
control(check_lattice(tensorV(weyl(2), wrong='F'), "ctl", record=False) > 0)
# 3: V⊗M with the E coproduct on the wrong letter fails
control(check_lattice(tensorV(weyl(2), wrong='E'), "ctl", record=False) > 0)
# 4: Delta(λ) with E^{(s)} e_r = C(r, s) e_{r-s} (the Nabla rule) fails
bad = dict(weyl(4)); bad['E'] = lambda s, r: {r - s: comb(r, s)} if s <= r and comb(r, s) else {}
control(check_lattice(bad, "ctl", record=False) > 0)
# 5: the dictionary with D -> (n + H)/2 fails
L = Vt[3]; idx = {pure_set(3, k): k for k in range(8)}
control(any(addv(L['F'](1, k), {k: 3 + L['wt'][k]}) != addv({idx[S | {j}]: 1 for j in range(3) if j not in S}, {k: 2 * len(S)})
            for S, k in idx.items()))

print(f"checks {checks}, failures {fails}; controls {fires}/{ctrl} fire")
print("FIN-OK" if fails == 0 and fires == ctrl else "FIN-BAD")
