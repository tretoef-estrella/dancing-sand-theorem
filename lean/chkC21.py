#!/usr/bin/env python3
"""Brute force for piece C21 (Prop. 3.1 (c): reduction mod 2 and the Frobenius twist).
Grepy Escribano, 7 Oct 2026. Exact rationals; reduction mod p of a fraction with denominator prime to p.
  1. (T0) Lucas at 2 for integer tops: C(2x,2j) = C(x,j) mod 2, C(2x,2j+1) = 0 mod 2, x in [-40, 40].
  2. (R1) N mod 2 satisfies (W),(P0),(P1),(K) mod 2; also Φ(N) mod 2.
  3. (T1) the twist (N mod 2)^{[1]} satisfies (W),(P0),(P1),(K) mod 2.
  4. (C0) φ(⅟(2s-1)!!) = 1, the c_j are odd.
  5. (C1)/(C2) Φ(N) mod 2 equals V ⊗ (N mod 2)^{[1]} entrywise, every F^{(r)}, E^{(r)}, r <= RM, every basis vector.
  6. (R3) (V⊗M) mod 2 = V⊗(M mod 2).
Controls must fail (reported as FIRES)."""
import importlib.util, sys, os
from fractions import Fraction as Fr
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
c18 = load("chkC18"); c20 = load("chkC20")
sys.stdout = _out
weyl, dweyl, tensorV, V, gchoose = c18.weyl, c18.dweyl, c18.tensorV, c18.V, c18.gchoose
Phi, dfact = c20.Phi, c20.dfact

RM = 7
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

def redp(x, p):
    x = Fr(x); assert x.denominator % p != 0
    return (x.numerator * pow(x.denominator, -1, p)) % p
def redvec(v, p): return {k: y for k, y in ((k, redp(x, p)) for k, x in v.items()) if y}
def red(L, p=2):
    return {'wt': L['wt'], 'F': lambda r, i: redvec(L['F'](r, i), p), 'E': lambda r, i: redvec(L['E'](r, i), p)}
def frob(M, wrong=None):
    wt = [w if wrong == 'wt' else 2 * w for w in M['wt']]
    def F(r, i):
        if r % 2 == 0: return M['F'](r // 2, i)
        return M['F'](r // 2, i) if wrong == 'odd' else {}
    def E(r, i):
        if r % 2 == 0: return M['E'](r // 2, i)
        return {}
    return {'wt': wt, 'F': F, 'E': E}
def addv(u, v, c=1):
    w = dict(u)
    for k, x in v.items(): w[k] = w.get(k, 0) + c * x
    return {k: x for k, x in w.items() if x}
def app(L, op, r, vec):
    out = {}
    for i, x in vec.items(): out = addv(out, L[op](r, i), x)
    return out
def modv(v, p): return {k: x % p for k, x in v.items() if x % p}

def check_dp_mod(L, p=2, rm=RM):
    bad = 0; n = len(L['wt'])
    for i in range(n):
        w = L['wt'][i]
        for r in range(rm + 1):
            for j in L['F'](r, i): bad += L['wt'][j] != w - 2 * r
            for j in L['E'](r, i): bad += L['wt'][j] != w + 2 * r
        bad += modv(L['F'](0, i), p) != {i: 1}; bad += modv(L['E'](0, i), p) != {i: 1}
        for a in range(rm + 1):
            for b in range(rm + 1 - a):
                for op in 'FE':
                    lhs = modv(app(L, op, a, L[op](b, i)), p)
                    rhs = modv({k: gchoose(a + b, a) * x for k, x in L[op](a + b, i).items()}, p)
                    bad += lhs != rhs
        for r in range(rm + 1):
            for s in range(rm + 1):
                lhs = modv(app(L, 'E', s, L['F'](r, i)), p); rhs = {}
                for j in range(min(r, s) + 1):
                    rhs = addv(rhs, app(L, 'F', r - j, L['E'](s - j, i)), gchoose(w + s - r, j))
                bad += lhs != modv(rhs, p)
    return bad

# 1. Lucas at 2
for x in range(-40, 41):
    for j in range(0, 22):
        ok(gchoose(2 * x, 2 * j) % 2 == gchoose(x, j) % 2, f"T0a x={x} j={j}")
        ok(gchoose(2 * x, 2 * j + 1) % 2 == 0, f"T0b x={x} j={j}")

Ns = [(f"Delta({m})", weyl(m)) for m in range(0, 6)] + [(f"Nabla({m})", dweyl(m)) for m in range(0, 6)] \
   + [("V⊗Delta(2)", tensorV(weyl(2))), ("V⊗Nabla(3)", tensorV(dweyl(3))), ("V^3", tensorV(tensorV(V)))]

for name, N in Ns:
    Nb = red(N)
    ok(check_dp_mod(Nb) == 0, f"R1 {name} mod 2")
    ok(check_dp_mod(red(Phi(N)), rm=5) == 0, f"R1 Phi({name}) mod 2")
    ok(check_dp_mod(frob(Nb)) == 0, f"T1 frob({name}) mod 2")
    # (C1)/(C2): Φ(N) mod 2 == V ⊗ Nb^{[1]}
    P = red(Phi(N)); T = tensorV(frob(Nb)); n = len(N['wt'])
    ok(P['wt'] == T['wt'], f"C2 weights {name}")
    for k in range(2 * n):
        for r in range(RM + 1):
            for op in 'FE':
                ok(P[op](r, k) == modv(T[op](r, k), 2), f"C2 {name} {op}{r} k={k}")
    # (R3) (V⊗N) mod 2 = V⊗(N mod 2)
    A1 = red(tensorV(N)); A2 = tensorV(Nb)
    for k in range(2 * n):
        for r in range(RM + 1):
            for op in 'FE':
                ok(A1[op](r, k) == modv(A2[op](r, k), 2), f"R3 {name}")

# 4. (C0)
for s in range(0, 30):
    ok(redp(Fr(1, dfact(2 * s - 1)), 2) == 1, "C0 dfi")
    ok((2 * s + 2) % 2 == 0, "C0 2s+2")
    for w in range(-15, 16):
        for j in range(0, s + 1):
            ok(((w + 2 * s + 1) ** 2 - (w + 2 * j) ** 2) % 2 == 1, "C0 c_j odd")
# (R3) V mod 2 = V
ok(all(red(V)[op](r, i) == V[op](r, i) for op in 'FE' for r in range(4) for i in range(2)), "R3 V")

print(f"chkC21: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond)
    print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
N = weyl(3); Nb = red(N)
# (i) without the twist: Φ(N) mod 2 != V ⊗ (N mod 2)
P = red(Phi(N)); T = tensorV(Nb)
control("no twist", any(P[op](r, k) != modv(T[op](r, k), 2) for op in 'FE' for r in range(RM + 1) for k in range(8)))
# (ii) twist with nonzero odd divided powers is not DP
control("odd F nonzero", check_dp_mod(frob(Nb, wrong='odd')) > 0)
# (iii) twist with weights w instead of 2w is not DP
control("weights not doubled", check_dp_mod(frob(Nb, wrong='wt')) > 0)
# (iv) Lucas over Z (not mod 2) fails
control("Lucas over Z", any(gchoose(2 * x, 2 * j) != gchoose(x, j) for x in range(-5, 6) for j in range(4)))
# (v) the twist over F_3 is not DP
control("twist mod 3", check_dp_mod(frob(red(N, 3)), p=3) > 0)
# (vi) the identity is not an iso Φ(N) mod 3 -> V ⊗ (N mod 3)^{[1]}
P3 = red(Phi(N), 3); T3 = tensorV(frob(red(N, 3)))
control("C2 mod 3", any(P3[op](r, k) != modv(T3[op](r, k), 3) for op in 'FE' for r in range(RM + 1) for k in range(8)))
print(f"controls: {fires}/{ctrl} fire")
