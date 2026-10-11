#!/usr/bin/env python3
"""Brute force for piece C20 (§3.1: the doubling functor Φ as a DP-lattice; Prop. 3.1 (a), (b), (d)).
Grepy Escribano, 7 Oct 2026. Exact rationals (Fraction). Lattices as in chkC18.
For N in a list of DP-lattices (Weyl lattices, their duals, V⊗Δ, V^{⊗3}):
  1. The CLOSED FORMULAS of the file for F^{(r)}, E^{(r)} on Φ(N) equal E^r/r!, F^r/r! computed
     from the single operators E, F of Φ(N) (r <= RM) — so the file's formulas are right.
  2. Every value has odd denominator (2-adic integrality), i.e. Φ(N) is a lattice over Z_(2).
  3. Φ(N) satisfies (W), (P0), (P1), (K) of C18 (r, s, a, b <= RM).
  4. (d): the explicit diagonal maps Δ(2μ+1) → Φ(Δ(μ)), ∇(2μ+1) → Φ(∇(μ)) commute with all
     F^{(r)}, E^{(s)}, H and have odd-unit diagonal; Φ(Δ(0)) data = V.
  5. (a): Φ(f) = 1⊗f commutes for the C19 maps f (a morphism goes to a morphism).
Controls must fail (reported as FIRES)."""
import importlib.util, sys, os
from fractions import Fraction as Fr
from math import comb, factorial
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
spec = importlib.util.spec_from_file_location("c18", os.path.join(os.path.dirname(__file__), "chkC18.py"))
c18 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c18)
spec = importlib.util.spec_from_file_location("c19", os.path.join(os.path.dirname(__file__), "chkC19.py"))
c19 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c19)
sys.stdout = _out
weyl, dweyl, tensorV, V, triv, gchoose = c18.weyl, c18.dweyl, c18.tensorV, c18.V, c18.triv, c18.gchoose

RM = 6
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

def addv(u, v, c=1):
    w = dict(u)
    for k, x in v.items(): w[k] = w.get(k, 0) + c * x
    return {k: x for k, x in w.items() if x}
def app(L, op, r, vec):
    out = {}
    for i, x in vec.items(): out = addv(out, L[op](r, i), x)
    return out

def dfact(k):  # k!! for odd k >= -1
    p = 1
    while k > 1: p *= k; k -= 2
    return p

def omega_apply(N, cs, vec):
    for c in cs:
        fe = app(N, 'F', 1, app(N, 'E', 1, vec))
        vec = addv({k: 4 * x for k, x in fe.items()}, {k: c * x for k, x in vec.items()})
    return vec

def Phi(N, wrong=None):
    n = len(N['wt'])
    idx = lambda e, i: e * n + i
    wt = [2 * w + 1 for w in N['wt']] + [2 * w - 1 for w in N['wt']]
    def F(r, k):
        e, i = divmod(k, n)
        if r % 2 == 0:
            s = r // 2
            return {idx(e, j): Fr(x, dfact(2 * s - 1)) for j, x in N['F'](s, i).items()}
        s = (r - 1) // 2
        if e == 0:
            return {idx(1, j): Fr(x, dfact(2 * s + 1)) for j, x in N['F'](s, i).items()}
        c = Fr(2 * s + 2, dfact(2 * s + 1)) if wrong != 'F' else Fr(1, dfact(2 * s + 1))
        return {idx(0, j): c * x for j, x in N['F'](s + 1, i).items()}
    def E(r, k):
        e, i = divmod(k, n); w = N['wt'][i]
        if r % 2 == 0:
            s = r // 2
            v = N['E'](s, i)
            js = range(0, s) if e == 1 else range(1, s + 1)
            if wrong == 'E': js = range(0, s)
            cs = [(w + 2 * s + 1) ** 2 - (w + 2 * j) ** 2 for j in js]
            v = omega_apply(N, cs, v)
            return {idx(e, j): Fr(x, dfact(2 * s - 1)) for j, x in v.items()}
        s = (r - 1) // 2
        if e == 1:
            v = N['E'](s, i)
            cs = [(w + 2 * s + 1) ** 2 - (w + 2 * j) ** 2 for j in range(0, s + 1)]
            v = omega_apply(N, cs, v)
            return {idx(0, j): Fr(x, dfact(2 * s + 1)) for j, x in v.items()}
        v = N['E'](s + 1, i)
        cs = [(w + 2 * s + 3) ** 2 - (w + 2 * j) ** 2 for j in range(1, s + 1)]
        v = omega_apply(N, cs, v)
        return {idx(1, j): Fr(2 * (s + 1), dfact(2 * s + 1)) * x for j, x in v.items()}
    return {'wt': wt, 'F': F, 'E': E}

def single_ops(N):
    """E, F of Φ(N) from the defining formulas of §3.1 (r = 1 only), as dict maps"""
    n = len(N['wt']); idx = lambda e, i: e * n + i
    def F1(k):
        e, i = divmod(k, n)
        if e == 0: return {idx(1, i): 1}
        return {idx(0, j): 2 * x for j, x in N['F'](1, i).items()}
    def E1(k):
        e, i = divmod(k, n); w = N['wt'][i]
        if e == 0: return {idx(1, j): 2 * x for j, x in N['E'](1, i).items()}
        fe = app(N, 'F', 1, N['E'](1, i))
        return {idx(0, j): x for j, x in addv({k2: 4 * y for k2, y in fe.items()}, {i: 2 * w + 1}).items()}
    return F1, E1

def powr(f, r, vec):
    for _ in range(r):
        out = {}
        for i, x in vec.items(): out = addv(out, f(i), x)
        vec = out
    return vec

def odd_den(vec): return all(Fr(x).denominator % 2 == 1 for x in vec.values())

def check_lattice_Q(L, name):
    bad = 0; n = len(L['wt'])
    for i in range(n):
        w = L['wt'][i]
        for r in range(RM + 1):
            for j in L['F'](r, i): bad += L['wt'][j] != w - 2 * r
            for j in L['E'](r, i): bad += L['wt'][j] != w + 2 * r
        bad += L['F'](0, i) != {i: 1}; bad += L['E'](0, i) != {i: 1}
        for a in range(RM + 1):
            for b in range(RM + 1 - a):
                for op in 'FE':
                    bad += app(L, op, a, L[op](b, i)) != {k: comb(a + b, a) * x for k, x in L[op](a + b, i).items()}
        for r in range(RM + 1):
            for s in range(RM + 1):
                lhs = app(L, 'E', s, L['F'](r, i)); rhs = {}
                for j in range(min(r, s) + 1):
                    rhs = addv(rhs, app(L, 'F', r - j, L['E'](s - j, i)), gchoose(w + s - r, j))
                bad += lhs != rhs
    ok(bad == 0, f"{name}: {bad} DP failures")
    return bad

Ns = [(f"Delta({m})", weyl(m)) for m in range(0, 5)] + [(f"Nabla({m})", dweyl(m)) for m in range(0, 5)] \
   + [("V⊗Delta(2)", tensorV(weyl(2))), ("V⊗Nabla(3)", tensorV(dweyl(3))), ("V^3", tensorV(tensorV(V)))]
for name, N in Ns:
    P = Phi(N); F1, E1 = single_ops(N)
    for k in range(len(P['wt'])):
        for r in range(RM + 1):
            ok(P['F'](r, k) == {j: Fr(x, factorial(r)) for j, x in powr(F1, r, {k: 1}).items()}, f"F closed {name} r={r}")
            ok(P['E'](r, k) == {j: Fr(x, factorial(r)) for j, x in powr(E1, r, {k: 1}).items()}, f"E closed {name} r={r}")
            ok(odd_den(P['F'](r, k)) and odd_den(P['E'](r, k)), f"odd denominators {name}")
    check_lattice_Q(P, f"Phi({name})")

# (d) the explicit diagonal maps
def diag_map_check(mu, kind):
    N = weyl(mu) if kind == 'D' else dweyl(mu)
    P = Phi(N); T = weyl(2 * mu + 1) if kind == 'D' else dweyl(2 * mu + 1)
    n = mu + 1
    x = lambda R: (R // 2) if R % 2 == 0 else n + R // 2   # R-th vector of Φ(N): b_0 e_s (R=2s), b_1 e_s (R=2s+1)
    c = [Fr(1)]
    for R in range(2 * mu + 1):
        if kind == 'D':
            c.append(c[-1] / (R + 1) if R % 2 == 0 else c[-1])
        else:
            c.append(c[-1] / (2 * mu + 1 - R) if R % 2 == 0 else c[-1])
    phi = lambda R: {x(R): c[R]}
    bad = 0
    for R in range(2 * mu + 2):
        bad += P['wt'][x(R)] != T['wt'][R]
        for r in range(RM + 1):
            for op in 'FE':
                lhs = {}
                for j, y in T[op](r, R).items(): lhs = addv(lhs, phi(j), y)
                bad += lhs != app(P, op, r, phi(R))
    ok(bad == 0, f"(d) {kind} mu={mu}: {bad}")
    ok(all(Fr(ci).numerator % 2 == 1 and Fr(ci).denominator % 2 == 1 for ci in c), f"(d) odd units {kind} mu={mu}")
    return bad
for mu in range(0, 6):
    diag_map_check(mu, 'D'); diag_map_check(mu, 'N')
# Φ(Δ(0)) has the data of V
P0 = Phi(weyl(0))
ok(P0['wt'] == V['wt'] and all(P0['F'](r, i) == V['F'](r, i) and P0['E'](r, i) == V['E'](r, i)
   for r in range(4) for i in range(2)), "Phi(A) = V")

# (a) Φ(f) = 1⊗f for the four maps of C19 (m = 1..4)
for m in range(1, 5):
    fD, gD, fN, gN = c19.maps(m)
    for f, X, Y in [(fD, weyl(m + 1), tensorV(weyl(m))), (gD, tensorV(weyl(m)), weyl(m - 1)),
                    (fN, dweyl(m - 1), tensorV(dweyl(m))), (gN, tensorV(dweyl(m)), dweyl(m + 1))]:
        PX, PY = Phi(X), Phi(Y); nx, ny = len(X['wt']), len(Y['wt'])
        Pf = lambda k, f=f, nx=nx, ny=ny: {e * ny + j: v for e in [k // nx] for j, v in f(k % nx).items()}
        bad = 0
        for k in range(2 * nx):
            for r in range(RM + 1):
                for op in 'FE':
                    lhs = {}
                    for j, y in PX[op](r, k).items(): lhs = addv(lhs, Pf(j), y)
                    bad += lhs != app(PY, op, r, Pf(k))
        ok(bad == 0, f"(a) Phi(f) m={m}")

# ---- controls ----
fires = 0; ctrl = 0
def control(cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond)
_f = fails; _c = checks
sys.stdout = open(os.devnull, "w")
for w in ['F', 'E']:
    control(check_lattice_Q(Phi(weyl(3), wrong=w), "ctl") > 0)
# the ∇ diagonal with the Δ ratios fails
def wrong_diag(mu):
    N = dweyl(mu); P = Phi(N); T = dweyl(2 * mu + 1); n = mu + 1
    x = lambda R: (R // 2) if R % 2 == 0 else n + R // 2
    c = [Fr(1)]
    for R in range(2 * mu + 1): c.append(c[-1] / (R + 1) if R % 2 == 0 else c[-1])
    bad = 0
    for R in range(2 * mu + 2):
        lhs = {}
        for j, y in T['F'](1, R).items(): lhs = addv(lhs, {x(j): c[j]}, y)
        bad += lhs != app(P, 'F', 1, {x(R): c[R]})
    return bad
control(wrong_diag(3) > 0)
# E with the b_0 product starting at j = 0 (the b_1 range) fails the closed form
N = weyl(3); P = Phi(N, wrong='E'); F1, E1 = single_ops(N)
control(any(P['E'](2, k) != {j: Fr(x, 2) for j, x in powr(E1, 2, {k: 1}).items()} for k in range(8)))
sys.stdout = _out
fails = _f; checks = _c

print(f"checks {checks}, failures {fails}; controls {fires}/{ctrl} fire")
print("FIN-OK" if fails == 0 and fires == ctrl else "FIN-BAD")
