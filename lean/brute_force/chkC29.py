#!/usr/bin/env python3
"""Brute force for piece C29 (filtrations of V ⊗ −, Φ, ⊕ and of the dance lattices).
Grepy Escribano, 8 Oct 2026. Over Z localized at 2 (exact fractions, odd denominators) and F_2.
For X in {T(λ), λ ≤ 7; V^{⊗n}, n ≤ 4; V⊗V⊗Φ(T(l)) and Φ(T(l))^2 ⊕ Φ(V⊗T(l)), l ≤ 2}:
  - X is a DP-lattice with 2-integral operators; rank and character of T(λ) as in §3.3;
  - for every m ≤ maxwt+1: dim_Q Hom(X, ∇(m)) = dim_F2 Hom(X/2, ∇(m)/2) (weight-preserving),
    dim_Q Hom(Δ(m), X) = dim_F2 Hom(Δ(m)/2, X/2);
  - these dimensions equal the Δ- and ∇-multiplicities predicted by the rules
    V ⊗ Δ(l) ↝ Δ(l+1) + Δ(l−1) (Δ(1) for l = 0), Φ(Δ(l)) ↝ Δ(2l+1), ⊕ additive.
Controls: ∇(2) fails the Δ-test; Δ(2) fails the ∇-test; a wrong Φ fails."""
import os, sys
from fractions import Fraction as Fr
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "chkC28.py")).read()
_keep = sys.stdout; sys.stdout = open(os.devnull, "w")
exec(src[:src.index("Dlist = ")])
s20 = open(os.path.join(here, "chkC20.py")).read()
exec(s20[s20.index("def addv"):s20.index("def single_ops")])
sys.stdout = _keep
RM = 8
checks = 0; fails = 0
def ok(c, m):
    global checks, fails
    checks += 1
    if not c:
        fails += 1
        if fails < 25: print("FAIL", m)

def rank2(rows):
    M = [[mod2(x) for x in r] for r in rows]
    return rank(M, 2) if M else 0
def homdim(X, Y):
    unk = unknowns(X, Y)
    if not unk: return 0, 0
    rows = comm_rows(X, Y, unk)
    return len(unk) - rank(rows, 0), len(unk) - rank2(rows)
def integral(D):
    return all(Fr(a).denominator % 2 == 1 for op in 'FE' for m in D[op] for row in m for a in row)

def T(lam, wrong=None):
    if lam == 0: return c18.triv
    l = (lam - 1) // 2
    if lam % 2 == 1: return Phi(T(l, wrong), wrong)
    return c18.tensorV(Phi(T(l, wrong), wrong))
def tpow(n):
    X = c18.triv
    for _ in range(n): X = c18.tensorV(X)
    return X
# predicted Δ-multiplicities (the same rules give the ∇-multiplicities)
def mT(lam):
    if lam == 0: return {0: 1}
    l = (lam - 1) // 2
    m = mPhi(mT(l))
    return m if lam % 2 == 1 else mV(m)
def mPhi(m): return {2 * a + 1: c for a, c in m.items()}
def mV(m):
    out = {}
    for a, c in m.items():
        for b in ([1] if a == 0 else [a + 1, a - 1]): out[b] = out.get(b, 0) + c
    return out
def madd(*ms):
    out = {}
    for m in ms:
        for a, c in m.items(): out[a] = out.get(a, 0) + c
    return out
def binchar(lam):
    k = (lam + 1).bit_length() - 1; I = [t for t in range(k) if (lam + 1) >> t & 1]
    ws = [0]
    for t in list(range(k)) + I: ws = [w + s * 2 ** t for w in ws for s in (1, -1)]
    return sorted(ws)

def test(name, L, pred):
    D = dense(L, RM)
    ok(is_dp(D) == 0, f"{name} is DP"); ok(integral(D), f"{name} 2-integral")
    top = max(abs(w) for w in D['wt'])
    for m in range(0, top + 2):
        q, f = homdim(D, dweyl(m)); ok(q == f, f"{name} Δ-test m={m}: Q {q} F2 {f}")
        ok(q == pred.get(m, 0), f"{name} Δ-mult m={m}: {q} vs {pred.get(m, 0)}")
        q, f = homdim(weyl(m), D); ok(q == f, f"{name} ∇-test m={m}: Q {q} F2 {f}")
        ok(q == pred.get(m, 0), f"{name} ∇-mult m={m}: {q} vs {pred.get(m, 0)}")

for lam in range(0, 8):
    L = T(lam)
    ok(sorted(L['wt']) == binchar(lam), f"T({lam}) character")
    test(f"T({lam})", L, mT(lam))
for n in range(0, 5):
    m = {0: 1}
    for _ in range(n): m = mV(m)
    test(f"V^{n}", tpow(n), m)
for l in range(0, 3):
    PT = Phi(T(l))
    test(f"V⊗V⊗Φ(T({l}))", c18.tensorV(c18.tensorV(PT)), mV(mV(mPhi(mT(l)))))
    D1 = dense(PT, RM); D2 = dense(Phi(c18.tensorV(T(l))), RM)
    S = dsum(dsum(D1, D1), D2)
    # dsum works on dense lattices; test it through a dict wrapper
    Ls = {'wt': S['wt'], 'F': lambda r, i, S=S: {j: S['F'][r][j][i] for j in range(len(S['wt'])) if S['F'][r][j][i]} if r <= RM else {},
          'E': lambda r, i, S=S: {j: S['E'][r][j][i] for j in range(len(S['wt'])) if S['E'][r][j][i]} if r <= RM else {}}
    test(f"Φ(T({l}))^2⊕Φ(V⊗T({l}))", Ls, madd(mPhi(mT(l)), mPhi(mT(l)), mPhi(mV(mT(l)))))
print(f"chkC29: {checks} checks, {fails} failures")

fires = 0; ctrl = 0
def control(name, cond):
    global fires, ctrl
    ctrl += 1; fires += bool(cond); print(f"control {name}: {'FIRES' if cond else 'SILENT'}")
q, f = homdim(dweyl(2), dweyl(0)); control("∇(2) fails the Δ-test", q != f)
q, f = homdim(weyl(0), weyl(2)); control("Δ(2) fails the ∇-test", q != f)
Dw = dense(T(3, wrong='F'), RM); control("wrong Φ is not DP", is_dp(Dw) != 0)
print(f"controls: {fires}/{ctrl} fire")
