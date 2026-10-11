#!/usr/bin/env python3
"""Brute force for piece C22 (Lemma 3.5, first sentence: over a ring with 2 = 0,
V^{⊗3} ≅ Δ(3) ⊕ V ⊕ V and Δ(3) ≅ V ⊗ V^{[1]}, by explicit 0/1 matrices).
Grepy Escribano, 7 Oct 2026. Basis of V^{⊗3} = tensorV(tensorV V): k = 4 e1 + 2 e2 + e3 (word e1 e2 e3).
Checks mod 2: weights kept; commutation with every F^{(r)}, E^{(r)}, r <= 6; the two composites are the identity.
Controls must fail (reported as FIRES)."""
import importlib.util, sys, os
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
c18 = load("chkC18"); c21 = load("chkC21")
sys.stdout = _out
V, tensorV, weyl, addv = c18.V, c18.tensorV, c18.weyl, c18.addv
frob, red = c21.frob, c21.red
RM = 6
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)
def modv(v, p=2): return {k: x % p for k, x in v.items() if x % p}

def dsum(*Ls):
    offs = []; o = 0
    for L in Ls: offs.append(o); o += len(L['wt'])
    wt = sum((L['wt'] for L in Ls), [])
    def loc(k):
        for t in range(len(Ls) - 1, -1, -1):
            if k >= offs[t]: return t, k - offs[t]
    def op(name):
        def f(r, k):
            t, i = loc(k)
            return {offs[t] + j: x for j, x in Ls[t][name](r, i).items()}
        return f
    return {'wt': wt, 'F': op('F'), 'E': op('E')}

def lin(M, vec):  # M: dict basis index -> vector
    out = {}
    for i, x in vec.items(): out = addv(out, M[i], x)
    return out
def is_hom(M, S, T, p=2, rm=RM):
    bad = 0
    for i in range(len(S['wt'])):
        for j in M[i]: bad += T['wt'][j] != S['wt'][i]
        for r in range(rm + 1):
            for op in 'FE':
                bad += modv(lin(M, S[op](r, i)), p) != modv(apply_vec(T, op, r, M[i]), p)
    return bad
def apply_vec(L, op, r, vec):
    out = {}
    for i, x in vec.items(): out = addv(out, L[op](r, i), x)
    return out
def compose(M2, M1, n):  # M2 ∘ M1 on basis 0..n-1
    return {i: modv(lin(M2, M1[i])) for i in range(n)}
def word(s): return int(s, 2)

V3 = tensorV(tensorV(V)); D3 = weyl(3); D = dsum(D3, V, V)
# --- (a) g : Δ(3) ⊕ V ⊕ V -> V^{⊗3}
x0 = {word('000'): 1}
g = {}
for r in range(4): g[r] = modv(apply_vec(V3, 'F', r, x0))
p1 = {word('100'): 1, word('010'): 1}; p2 = {word('010'): 1, word('001'): 1}
g[4] = p1; g[5] = modv(apply_vec(V3, 'F', 1, p1)); g[6] = p2; g[7] = modv(apply_vec(V3, 'F', 1, p2))
# inverse over F_2 by Gaussian elimination
import itertools
def mat(Mp, n, m):  # columns = images of basis
    return [[Mp[j].get(i, 0) % 2 for j in range(n)] for i in range(m)]
def inv2(A):
    n = len(A); M = [row[:] + [int(i == j) for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c])
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c]: M[r] = [(a + b) % 2 for a, b in zip(M[r], M[c])]
    return [row[n:] for row in M]
G = mat(g, 8, 8); Gi = inv2(G)
h = {i: {j: 1 for j in range(8) if Gi[j][i]} for i in range(8)}  # h(word i)
ok(is_hom(g, D, V3) == 0, "g hom"); ok(is_hom(h, V3, D) == 0, "h hom")
ok(compose(h, g, 8) == {i: {i: 1} for i in range(8)}, "h∘g"); ok(compose(g, h, 8) == {i: {i: 1} for i in range(8)}, "g∘h")
print("g:", {i: sorted(format(k, '03b') for k in g[i]) for i in g})
print("h:", {format(i, '03b'): sorted(h[i]) for i in h})
# --- (b) u : Δ(3) -> V ⊗ V^{[1]}
VV1 = tensorV(frob(V))  # index e*2 + e'
u = {0: {0: 1}, 1: {2: 1}, 2: {1: 1}, 3: {3: 1}}   # e0->b0b0, e1->b1b0, e2->b0b1, e3->b1b1
ui = {0: {0: 1}, 2: {1: 1}, 1: {2: 1}, 3: {3: 1}}
ok(is_hom(u, D3, VV1) == 0, "u hom"); ok(is_hom(ui, VV1, D3) == 0, "u^-1 hom")
ok(all(modv(apply_vec(VV1, 'F', r, {0: 1})) == u[r] for r in range(4)), "u(e_r)=F^(r)(b0b0)")
# integer entries: g, h in {0,1}; also hom holds over Z/4? (not required)
print(f"chkC22: {checks} checks, {fails} failures")
# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
gb = dict(g); gb[4] = {word('100'): 1}; gb[5] = modv(apply_vec(V3, 'F', 1, gb[4]))
control("p1 not in the complement", is_hom(gb, D, V3) > 0)
control("no twist: Δ(3) -> V⊗V", is_hom({0: {0: 1}, 1: {2: 1}, 2: {1: 1}, 3: {3: 1}}, D3, tensorV(V)) > 0)
control("g over F_3", is_hom(g, D, V3, p=3) > 0)
control("u over F_3", is_hom(u, D3, tensorV(frob(red(V, 3))), p=3) > 0)
ub = dict(u); ub[1], ub[2] = {1: 1}, {2: 1}
control("u with e1,e2 swapped", is_hom(ub, D3, VV1) > 0)
print(f"controls: {fires}/{ctrl} fire")
