#!/usr/bin/env python3
"""Brute force for piece C23 (the tensor product M ⊗ N of DP-lattices, over any commutative ring).
Grepy Escribano, 7 Oct 2026. Exact integers. Basis of M ⊗ N: index i*|N| + j for (i, j).
  F^{(r)}(δ_i ⊗ δ_j) = Σ_{a=0}^{r} F^{(a)} δ_i ⊗ F^{(r-a)} δ_j, same for E; weights add.
  1. (P1) M ⊗ N satisfies (W), (P0), (P1), (K) for r, s, a, b <= 5, many pairs.
  2. (P3) tensorV M = V ⊗ M entrywise (same index e*|M| + i).
  3. (P4) (M ⊗ N) ⊗ P = M ⊗ (N ⊗ P) under ((i,j),k) -> (i,(j,k)).
  4. (P5) (M ⊕ N) ⊗ P = (M ⊗ P) ⊕ (N ⊗ P) under (inl i, k) -> inl (i, k), (inr j, k) -> inr (j, k);
     and M ⊗ (N ⊕ P) = (M ⊗ N) ⊕ (M ⊗ P) under (i, inl j) -> inl (i, j), (i, inr k) -> inr (i, k).
  6. (P8) one ⊗ M = M = M ⊗ one.
  5. (P2) f ⊗ g is a Hom for Homs f, g (the canonical Δ(λ) -> ∇(λ), e_r -> C(λ, r) e_r, and identities).
Controls must fail (reported as FIRES)."""
import importlib.util, sys, os
from math import comb
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
c18 = load("chkC18"); c22 = load("chkC22")
sys.stdout = _out
V, tensorV, weyl, dweyl, addv, triv, gchoose = c18.V, c18.tensorV, c18.weyl, c18.dweyl, c18.addv, c18.triv, c18.gchoose
dsum = c22.dsum
RM = 5
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

def apply(L, op, r, vec):
    out = {}
    for i, x in vec.items(): out = addv(out, L[op](r, i), x)
    return out

def check_lattice(L, rm=RM):
    bad = 0; n = len(L['wt'])
    for i in range(n):
        w = L['wt'][i]
        for r in range(rm + 1):
            for j in L['F'](r, i): bad += L['wt'][j] != w - 2 * r
            for j in L['E'](r, i): bad += L['wt'][j] != w + 2 * r
        bad += L['F'](0, i) != {i: 1}; bad += L['E'](0, i) != {i: 1}
        for a in range(rm + 1):
            for b in range(rm + 1 - a):
                for op in 'FE':
                    bad += apply(L, op, a, L[op](b, i)) != {k: comb(a + b, a) * x for k, x in L[op](a + b, i).items() if comb(a + b, a) * x}
        for r in range(rm + 1):
            for s in range(rm + 1):
                lhs = apply(L, 'E', s, L['F'](r, i)); rhs = {}
                for j in range(min(r, s) + 1):
                    rhs = addv(rhs, apply(L, 'F', r - j, L['E'](s - j, i)), gchoose(w + s - r, j))
                bad += lhs != rhs
    return bad

def kronv(u, v, nN):
    out = {}
    for i, x in u.items():
        for j, y in v.items():
            out[i * nN + j] = out.get(i * nN + j, 0) + x * y
    return {k: x for k, x in out.items() if x}

def tensor(M, N, wrong=None):
    nN = len(N['wt'])
    wt = [M['wt'][i] + (N['wt'][j] if wrong != 'wt' else -N['wt'][j]) for i in range(len(M['wt'])) for j in range(nN)]
    def op(name):
        def f(r, k):
            i, j = divmod(k, nN)
            if wrong == 'naive':
                if r == 0: return {k: 1}
                return addv(kronv(M[name](r, i), {j: 1}, nN), kronv({i: 1}, N[name](r, j), nN))
            out = {}
            for a in range(r + 1):
                out = addv(out, kronv(M[name](a, i), N[name](r - a, j), nN))
            return out
        return f
    return {'wt': wt, 'F': op('F'), 'E': op('E')}

def same(L1, L2, perm=None, rm=RM):
    n = len(L1['wt']); perm = perm or (lambda k: k)
    if sorted(L1['wt']) != sorted(L2['wt']): return False
    for k in range(n):
        if L1['wt'][k] != L2['wt'][perm(k)]: return False
        for r in range(rm + 1):
            for op in 'FE':
                if {perm(a): x for a, x in L1[op](r, k).items()} != L2[op](r, perm(k)): return False
    return True

lats = [("triv", triv), ("V", V)] + [(f"D{l}", weyl(l)) for l in range(4)] + [(f"N{l}", dweyl(l)) for l in range(1, 4)] \
     + [("V⊗D2", tensorV(weyl(2)))]
# 1. IsDP of M ⊗ N
for a, M in lats:
    for b, N in lats:
        if len(M['wt']) * len(N['wt']) > 24: continue
        ok(check_lattice(tensor(M, N)) == 0, f"P1 {a}⊗{b}")
# 2. tensorV M = V ⊗ M
for a, M in lats:
    ok(same(tensorV(M), tensor(V, M)), f"P3 {a}")
# 3. associativity: index ((i,j),k) = (i*nN+j)*nP+k = i*(nN*nP)+j*nP+k = (i,(j,k)): the identity
small = [("V", V), ("D2", weyl(2)), ("N2", dweyl(2)), ("D3", weyl(3))]
for a, M in small:
    for b, N in small:
        for c, P in small:
            ok(same(tensor(tensor(M, N), P), tensor(M, tensor(N, P))), f"P4 {a},{b},{c}")
# 4. distributivity
for a, M in small:
    for b, N in small:
        for c, P in small:
            nM, nN, nP = len(M['wt']), len(N['wt']), len(P['wt'])
            ok(same(tensor(dsum(M, N), P), dsum(tensor(M, P), tensor(N, P))), f"P5 right {a},{b},{c}")
            def perm(k, nM=nM, nN=nN, nP=nP):   # (i, s) with s in N ⊕ P  ->  inl (i,j) or inr (i,k)
                i, s = divmod(k, nN + nP)
                return i * nN + s if s < nN else nM * nN + i * nP + (s - nN)
            ok(same(tensor(M, dsum(N, P)), dsum(tensor(M, N), tensor(M, P)), perm), f"P5 left {a},{b},{c}")
# 5. Homs: canonical Δ(λ) -> ∇(λ), e_r -> C(λ,r) e_r
def can(l): return {r: {r: comb(l, r)} for r in range(l + 1)}
def ident(n): return {i: {i: 1} for i in range(n)}
def kronmap(f, g, nN2):
    return {i * len(g) + j: kronv(f[i], g[j], nN2) for i in f for j in g}
def is_hom(Mp, S, T, rm=RM):
    bad = 0
    for i in range(len(S['wt'])):
        for j in Mp[i]: bad += T['wt'][j] != S['wt'][i]
        for r in range(rm + 1):
            for op in 'FE':
                lhs = {}
                for k, x in S[op](r, i).items(): lhs = addv(lhs, Mp[k], x)
                bad += lhs != apply(T, op, r, Mp[i])
    return bad
for l in range(4):
    ok(is_hom(can(l), weyl(l), dweyl(l)) == 0, f"can {l} hom")
for l1 in range(4):
    for l2 in range(4):
        f, g = can(l1), can(l2)
        ok(is_hom(kronmap(f, g, l2 + 1), tensor(weyl(l1), weyl(l2)), tensor(dweyl(l1), dweyl(l2))) == 0, f"P2 can{l1}⊗can{l2}")
        ok(is_hom(kronmap(ident(2), g, l2 + 1), tensorV(weyl(l2)), tensorV(dweyl(l2))) == 0, f"P8 id_V⊗can{l2}")
# 6. (P8) the unit: one ⊗ M = M = M ⊗ one (index 0*n + i = i, i*1 + 0 = i)
for a, M in lats:
    ok(same(tensor(triv, M), M) and same(tensor(M, triv), M), f"P8 {a}")
print(f"chkC23: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
control("naive F⊗1 + 1⊗F is not DP", check_lattice(tensor(V, V, 'naive')) > 0)
control("weights subtracted", check_lattice(tensor(weyl(2), weyl(1), 'wt')) > 0)
control("assoc with the inner pair swapped", not same(tensor(tensor(V, weyl(2)), weyl(1)), tensor(V, tensor(weyl(1), weyl(2)))))
control("kron of a non-Hom (e_r -> e_r, λ = 2)", is_hom(kronmap({r: {r: 1} for r in range(3)}, ident(2), 2),
        tensor(weyl(2), V), tensor(dweyl(2), V)) > 0)
control("tensorV M != M ⊗ V (order matters for the index)", not same(tensorV(weyl(2)), tensor(weyl(2), V)))
print(f"controls: {fires}/{ctrl} fire")
