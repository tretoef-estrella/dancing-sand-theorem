#!/usr/bin/env python3
"""Brute force for piece C19 (Lemma 2.4: the Weyl filtrations of V⊗Δ(m) and V⊗∇(m)).
Grepy Escribano, 7 Oct 2026. Exact integers; reuses the lattice code of chkC18.
Checks: the four explicit maps commute with F^{(r)}, E^{(s)} (r, s <= m+3) and preserve weights;
g∘f = 0; exactness modulo p for p in {2,3,5,7,11,13} (rank counts); the explicit preimage formula
of the proof sketch; the case m = 0.  Controls must fail (reported as FIRES)."""
import importlib.util, sys, os, random
spec = importlib.util.spec_from_file_location("c18", os.path.join(os.path.dirname(__file__), "chkC18.py"))
# load only the definitions of chkC18 (its checks run too; that is harmless and fast)
_out = sys.stdout; sys.stdout = open(os.devnull, "w")
c18 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c18)
sys.stdout = _out
weyl, dweyl, tensorV, apply, addv, V = c18.weyl, c18.dweyl, c18.tensorV, c18.apply, c18.addv, c18.V

checks = 0; fails = 0
def ok(c, msg):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 20: print("FAIL", msg)

def mapv(f, vec):
    out = {}
    for i, x in vec.items(): out = addv(out, f(i), x)
    return out

def is_morphism(f, X, Y, RM):
    bad = 0
    for i in range(len(X['wt'])):
        for j in f(i): bad += Y['wt'][j] != X['wt'][i]
        for op in 'FE':
            for r in range(RM + 1):
                bad += mapv(f, X[op](r, i)) != apply(Y, op, r, f(i))
    return bad

def rank_mod(rows, p):
    rows = [[x % p for x in r] for r in rows]; rk = 0; ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((k for k in range(rk, len(rows)) if rows[k][c]), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], p - 2, p)
        rows[rk] = [x * inv % p for x in rows[rk]]
        for k in range(len(rows)):
            if k != rk and rows[k][c]:
                t = rows[k][c]; rows[k] = [(a - t * b) % p for a, b in zip(rows[k], rows[rk])]
        rk += 1
    return rk

def matrix(f, nsrc, ntgt):  # columns = images of basis vectors; returned as list of rows
    cols = [f(i) for i in range(nsrc)]
    return [[cols[i].get(j, 0) for i in range(nsrc)] for j in range(ntgt)]

def maps(m, wrong=None):
    ln = m + 1  # basis length of Δ(m), ∇(m); V⊗M index = e*ln + r
    def fD(R):
        out = {}
        if R <= m: out[R] = 1
        if R - 1 >= 0 and wrong != 'fD': out = addv(out, {ln + R - 1: 1})
        return out
    def gD(k):
        e, s = divmod(k, ln)
        if e == 1: return {s: 1} if s <= m - 1 else {}
        if s == 0: return {}
        return {s - 1: (1 if wrong == 'gD' else -1)}
    def fN(r):
        return addv({r + 1: 1}, {ln + r: (1 if wrong == 'fN' else -1)})
    def gN(k):
        e, r = divmod(k, ln)
        return {r: 1} if (e == 0 or wrong == 'gN') else {r + 1: 1}
    return fD, gD, fN, gN

primes = [2, 3, 5, 7, 11, 13]
for m in range(1, 9):
    X, Y, Z = weyl(m + 1), tensorV(weyl(m)), weyl(m - 1)
    Xn, Yn, Zn = dweyl(m - 1), tensorV(dweyl(m)), dweyl(m + 1)
    fD, gD, fN, gN = maps(m)
    RM = m + 3
    ok(is_morphism(fD, X, Y, RM) == 0, f"fD m={m}")
    ok(is_morphism(gD, Y, Z, RM) == 0, f"gD m={m}")
    ok(is_morphism(fN, Xn, Yn, RM) == 0, f"fN m={m}")
    ok(is_morphism(gN, Yn, Zn, RM) == 0, f"gN m={m}")
    nY = 2 * (m + 1)
    for (f, g, nx, nz) in [(fD, gD, m + 2, m), (fN, gN, m, m + 2)]:
        ok(all(mapv(g, f(i)) == {} for i in range(nx)), f"g∘f=0 m={m}")
        Mf, Mg = matrix(f, nx, nY), matrix(g, nY, nz)
        for p in primes:
            ok(rank_mod([r[:] for r in Mf], p) == nx, f"f injective mod {p} m={m}")
            ok(rank_mod([r[:] for r in Mg], p) == nz, f"g surjective mod {p} m={m}")
            ok(nx + nz == nY, f"ranks m={m}")
    # explicit preimage formula of the proof sketch (on random integer kernel vectors)
    ln = m + 1
    for _ in range(20):
        c = [random.randint(-9, 9) for _ in range(m + 1)]; dm = random.randint(-9, 9)
        y = {}
        for R in range(m + 1): y = addv(y, {R: c[R]})
        for s in range(m): y = addv(y, {ln + s: c[s + 1]})
        y = addv(y, {ln + m: dm})
        ok(mapv(gD, y) == {}, "kernel vector D")
        a = {R: c[R] for R in range(m + 1)}; a[m + 1] = dm
        ok(mapv(fD, {k: v for k, v in a.items() if v}) == y, f"preimage D m={m}")
        cc = [0] + [random.randint(-9, 9) for _ in range(m)]
        yN = {}
        for r in range(m + 1): yN = addv(yN, {r: cc[r]})
        for r in range(m): yN = addv(yN, {ln + r: -cc[r + 1]})
        ok(mapv(gN, yN) == {}, "kernel vector N")
        ok(mapv(fN, {r: cc[r + 1] for r in range(m) if cc[r + 1]}) == yN, f"preimage N m={m}")
    # (S3) range fD = span of F^{(R)}(b_0 e_0)
    for R in range(m + 2):
        ok(apply(Y, 'F', R, {0: 1}) == fD(R), f"S3 m={m} R={R}")

# (S4) m = 0: V⊗Δ(0) and V⊗∇(0) have the data of V under (e, 0) <-> e
for L in (tensorV(weyl(0)), tensorV(dweyl(0))):
    ok(L['wt'] == V['wt'] and all(L['F'](r, i) == V['F'](r, i) and L['E'](r, i) == V['E'](r, i)
       for r in range(5) for i in range(2)), "S4")

# ---- controls ----
fires = 0; ctrl = 0
def control(cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond)
m = 3
for w, (src, tgt, k) in [('fD', (weyl(4), tensorV(weyl(3)), 0)), ('gD', (tensorV(weyl(3)), weyl(2), 1)),
                         ('fN', (dweyl(2), tensorV(dweyl(3)), 2)), ('gN', (tensorV(dweyl(3)), dweyl(4), 3))]:
    control(is_morphism(maps(m, wrong=w)[k], src, tgt, 6) > 0)
# a map with the right formulas but onto the wrong lattice (fΔ into V⊗∇) fails
control(is_morphism(maps(3)[0], weyl(4), tensorV(dweyl(3)), 6) > 0)

print(f"checks {checks}, failures {fails}; controls {fires}/{ctrl} fire")
print("FIN-OK" if fails == 0 and fires == ctrl else "FIN-BAD")
