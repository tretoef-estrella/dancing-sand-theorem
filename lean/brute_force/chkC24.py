#!/usr/bin/env python3
"""Brute force for piece C24 (Lemma 3.5, second sentence), Grepy Escribano, 7 Oct 2026.
Exact rationals, reduced mod 2 (denominators odd). Index conventions as in chkC18/C20/C22/C23:
tensorV M: e*|M| + i; Phi(N): c*|N| + i; tensor M N: i*|N| + j; dsum: blocks in order.
  1. (B1) (M ⊗ N) mod 2 = (M mod 2) ⊗ (N mod 2) entrywise, also for Phi lattices.
  2. (F1) frob(M ⊗ N) = frob M ⊗ frob N entrywise, M, N over F_2.
  3. (L4) the explicit map V^{⊗3} ⊗ X -> (V ⊗ V^{[1]}) ⊗ X ⊕ (V ⊗ X)^2 (h of C22, then u on Δ(3)) is a
     Hom over F_2 and invertible over F_2, for several X.
  4. (L5) the explicit map (V ⊗ V ⊗ Φ(N)) mod 2 -> (Φ(N) ⊕ Φ(N) ⊕ Φ(V ⊗ N)) mod 2 is a Hom over F_2 and
     invertible over F_2, for several N.
Controls must fail (reported as FIRES)."""
import importlib.util, sys, os
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py"))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
c18 = load("chkC18"); c20 = load("chkC20"); c21 = load("chkC21"); c22 = load("chkC22"); c23 = load("chkC23")
sys.stdout = _out
V, tensorV, weyl, dweyl, triv = c18.V, c18.tensorV, c18.weyl, c18.dweyl, c18.triv
Phi = c20.Phi; red, frob, modv = c21.red, c21.frob, c21.modv
dsum, is_hom, h, u, g = c22.dsum, c22.is_hom, c22.h, c22.u, c22.g
tensor = c23.tensor
RM = 6
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

def same_mod2(L1, L2, rm=RM):
    if L1['wt'] != L2['wt']: return False
    for k in range(len(L1['wt'])):
        for r in range(rm + 1):
            for op in 'FE':
                if modv(L1[op](r, k), 2) != modv(L2[op](r, k), 2): return False
    return True

def rank2(Mp, n):
    rows = []
    for i in range(n):
        v = 0
        for j, x in Mp[i].items():
            if x % 2: v |= 1 << j
        rows.append(v)
    r = 0
    for bit in range(n):
        piv = next((t for t in range(r, n) if rows[t] >> bit & 1), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for t in range(n):
            if t != r and rows[t] >> bit & 1: rows[t] ^= rows[r]
        r += 1
    return r

def addto(d, k, x=1): d[k] = (d.get(k, 0) + x) % 2

def L4map(n, hh=h, uu=u, second=6):
    M = {}
    for a in range(2):
        for b in range(2):
            for c in range(2):
                w = a * 4 + b * 2 + c
                for x in range(n):
                    img = {}
                    for j in hh[w]:
                        if j < 4: (q,) = uu[j].keys(); addto(img, q * n + x)
                        elif j < 6: addto(img, 4 * n + (j - 4) * n + x)
                        else: addto(img, second * n + (j - 6) * n + x)
                    M[a * 4 * n + b * 2 * n + c * n + x] = {k: 1 for k, y in img.items() if y}
    return M

def L5map(n, hh=h, uu=u):
    M = {}
    for a in range(2):
        for b in range(2):
            for c in range(2):
                w = a * 4 + b * 2 + c
                for i in range(n):
                    img = {}
                    for j in hh[w]:
                        if j < 4:
                            (q,) = uu[j].keys(); e, e1 = divmod(q, 2)
                            addto(img, 4 * n + e * 2 * n + e1 * n + i)
                        elif j < 6: addto(img, (j - 4) * n + i)
                        else: addto(img, 2 * n + (j - 6) * n + i)
                    M[a * 4 * n + b * 2 * n + c * n + i] = {k: 1 for k, y in img.items() if y}
    return M

VV1 = tensorV(frob(red(V)))
# 1. (B1)
ints = [("V", V), ("D2", weyl(2)), ("N2", dweyl(2)), ("D3", weyl(3)), ("PhiD1", Phi(weyl(1))), ("PhiN2", Phi(dweyl(2)))]
for a, M in ints:
    for b, N in ints:
        if len(M['wt']) * len(N['wt']) > 24: continue
        ok(same_mod2(red(tensor(M, N)), tensor(red(M), red(N))), f"B1 {a}⊗{b}")
# 2. (F1)
mods = [("V", red(V)), ("D2", red(weyl(2))), ("N3", red(dweyl(3))), ("V⊗D1", red(tensorV(weyl(1)))), ("frobV", frob(red(V)))]
for a, M in mods:
    for b, N in mods:
        ok(same_mod2(frob(tensor(M, N)), tensor(frob(M), frob(N)), rm=8), f"F1 {a},{b}")
# 3. (L4)
Xs = mods + [("triv", red(triv)), ("D0", red(weyl(0))), ("frobD2", frob(red(weyl(2)))), ("N1", red(dweyl(1)))]
for a, X in Xs:
    n = len(X['wt'])
    S = tensorV(tensorV(tensorV(X))); T = dsum(tensor(VV1, X), tensorV(X), tensorV(X))
    Mp = L4map(n)
    ok(is_hom(Mp, S, T) == 0, f"L4 hom X={a}"); ok(rank2(Mp, 8 * n) == 8 * n, f"L4 bijective X={a}")
# 4. (L5)
Ns = [("triv", triv), ("V", V)] + [(f"D{l}", weyl(l)) for l in range(4)] + [(f"N{l}", dweyl(l)) for l in range(1, 4)] \
   + [("V⊗D1", tensorV(weyl(1)))]
cache = {}
for a, N in Ns:
    n = len(N['wt'])
    S = red(tensorV(tensorV(Phi(N)))); T = red(dsum(Phi(N), Phi(N), Phi(tensorV(N))))
    cache[a] = (n, S, T, N)
    Mp = L5map(n)
    ok(is_hom(Mp, S, T) == 0, f"L5 hom N={a}"); ok(rank2(Mp, 8 * n) == 8 * n, f"L5 bijective N={a}")
print(f"chkC24: {checks} checks, {fails} failures")

# ---- controls ----
fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
n, S, T, N = cache["D2"]
Mg = L5map(n, hh=g)   # the table of g used where h belongs
control("g in place of h", is_hom(Mg, S, T) > 0 or rank2(Mg, 8 * n) < 8 * n)
Tbad = dsum(red(Phi(N)), red(Phi(N)), red(tensorV(tensorV(N))))   # no twist on the third summand
control("third summand without the twist", is_hom(L5map(n), S, Tbad) > 0)
uid = {r: {r: 1} for r in range(4)}   # u without the swap e1 <-> e2
X = red(weyl(2)); nX = len(X['wt'])
control("u without the swap", is_hom(L4map(nX, uu=uid), tensorV(tensorV(tensorV(X))), dsum(tensor(VV1, X), tensorV(X), tensorV(X))) > 0)
control("frob odd powers not killed", not same_mod2(frob(tensor(red(V), red(weyl(2))), 'odd'), tensor(frob(red(V)), frob(red(weyl(2)))), rm=8))
control("both V copies sent to the first", rank2(L4map(nX, second=4), 8 * nX) < 8 * nX)
print(f"controls: {fires}/{ctrl} fire")
