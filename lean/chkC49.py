# chkC49.py — brute force for Lean piece C49 (Corollary 10.17 for j >= 1, and l = 0 for every j).
# Grepy Escribano, 10 Oct 2026. Exact rationals; lattice model of T(l) from chk_lattice_lib.
import sys
from fractions import Fraction
from math import comb
import chk_lattice_lib as L
NF = [0]; NC = [0]
def ok(c, msg):
    NC[0] += 1
    if not c: NF[0] += 1; print("FAIL", msg)
def eye(n): return [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
def add(X, Y): return [[X[i][j] + Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def sub(X, Y): return [[X[i][j] - Y[i][j] for j in range(len(X[0]))] for i in range(len(X))]
def sc(c, X): return [[c * x for x in r] for r in X]
def mm(X, Y): return L.matmul(X, Y)
def diag(v): return [[Fraction(v[i]) if i == j else Fraction(0) for j in range(len(v))] for i in range(len(v))]
def dfact(k):
    p = 1
    while k > 1: p *= k; k -= 2
    return p
def smith(M):
    Mi = L.to_int(M); return None if Mi is None else L.smith2(Mi, len(M), len(M[0]))
def v2(q):
    q = Fraction(q)
    if q == 0: return 10**9
    a, b, v = q.numerator, q.denominator, 0
    while a % 2 == 0: a //= 2; v += 1
    while b % 2 == 0: b //= 2; v -= 1
    return v
MM = 14
dfi = lambda s: Fraction(1, dfact(2 * s - 1))
chF = [dfi(m) for m in range(MM)]            # Ch = sum dfi m F^(m)
shF = [dfi(m + 1) for m in range(MM)]        # Sh = sum dfi (m+1) F^(m)
def cmul(x, y): return [sum(comb(m, a) * x[a] * y[m - a] for a in range(m + 1)) for m in range(MM)]
shInv = [Fraction(1)]
for m in range(1, MM):                       # shInv m = - sum_{b<m} C(m,b) shF(m-b) shInv b
    shInv.append(-sum(comb(m, b) * shF[m - b] * shInv[b] for b in range(m)))
one = [Fraction(int(m == 0)) for m in range(MM)]
ok(cmul(shF, shInv) == one, "Sh * ShInv = 1"); ok(cmul(shInv, shF) == one, "ShInv * Sh = 1")
def K(j):                                    # (Ch - (-1)^j) * ShInv, a constant series
    eps = (-1) ** j
    return cmul([chF[m] - (eps if m == 0 else 0) for m in range(MM)], shInv)
def psiF(j):                                 # coef m f
    k = K(j); return lambda m, f: (4 * f + 2 * j + k[0]) if m == 0 else k[m]
def sigF(c): return lambda m, f: 4 * (f + c) if m == 0 else (1 if m == 1 else 0)
def xiZ(alpha, c, eta, z): return lambda m, f: 2 ** alpha * (f + c) if m == 0 else (eta if m == 1 else z(m))
# (P) Psi_j = XiOpZ 2 c eta z with c = (j+1)//2, eta unit, z m = K(j) m
for j in range(0, 12):
    k = K(j); c = (j + 1) // 2; P = psiF(j); X = xiZ(2, c, k[1], lambda m: k[m])
    ok(k[0] == 1 - (-1) ** j, f"K0 j={j}")
    ok(v2(k[1]) == 0, f"eta unit j={j}"); ok(k[1] == (1 if j % 2 == 0 else Fraction(1, 3)), f"eta value j={j}")
    ok(all(v2(k[m]) >= 0 for m in range(MM)), f"integral j={j}")
    ok(all(P(m, f) == X(m, f) for m in range(MM) for f in range(-6, 12)), f"Psi = XiOpZ j={j}")
for c in range(0, 8):
    S = sigF(c); X = xiZ(2, c, 1, lambda m: 0)
    ok(all(S(m, f) == X(m, f) for m in range(MM) for f in range(-6, 12)), f"Sig = XiOpZ c={c}")
# lattice side
def ops(l):
    _, W, Fm = L.lat(l); n = len(W)
    I = eye(n); P = I; pows = [I]; fact = 1
    for r in range(1, l + 3):
        P = mm(P, Fm); fact *= r; pows.append(sc(Fraction(1, fact), P))
    return W, Fm, pows, n
def act(l, x, B):                            # sum_{m<B} flD(coef m) * Fd m, floor (l - wt)/2 of the target
    W, Fm, pows, n = ops(l); R = [[Fraction(0)] * n for _ in range(n)]
    for m in range(min(B, len(pows))):
        D = diag([x(m, (l - w) // 2) for w in W]); R = add(R, mm(D, pows[m]))
    return R
def PsiC(l, d):                              # C39 Psi on T(l)
    W, Fm, pows, n = ops(l)
    Ch = eye(n); Sh = eye(n)
    for s in range(1, len(pows)):
        Ch = add(Ch, sc(dfi(s), pows[s])); Sh = add(Sh, sc(dfi(s + 1), pows[s]))
    Nil = sub(Sh, eye(n)); Shi = eye(n); T = eye(n)
    for _ in range(n + 1): T = sc(-1, mm(T, Nil)); Shi = add(Shi, T)
    S = diag([(-1) ** abs(d - w) for w in W])
    return add(sub(sc(2 * d, eye(n)), sc(2, diag(W))), mm(sub(Ch, S), Shi))
def SigC(l, e):                              # C39b SigmaOp
    W, Fm, pows, n = ops(l); return add(Fm, diag([2 * e - 2 * w for w in W]))
ctrl = {"psi_d+1": 0, "sig_c+1": 0, "eta2": 0, "wrong_shift": 0}
for l in range(0, 7):
    W, *_ = ops(l)
    ok(all((l - w) % 2 == 0 and -l <= w <= l for w in W), f"parity l={l}")
    for B in (l + 1, l + 3):
        for j in range(0, 6):
            c = (j + 1) // 2
            A1 = act(l, psiF(j), B); ok(A1 == PsiC(l, l + j), f"act Psi l={l} j={j} B={B}")
            if A1 != PsiC(l, l + j + 1): ctrl["psi_d+1"] += 1
            A2 = act(l, sigF(c), B); ok(A2 == SigC(l, l + 2 * c), f"act Sig l={l} c={c} B={B}")
    for j in range(0, 6):
        c = (j + 1) // 2
        s1, s2 = smith(PsiC(l, l + j)), smith(SigC(l, l + 2 * c))
        ok(s1 == s2, f"Corollary 10.17 Smith l={l} j={j} (c={c})")
        if s1 != smith(SigC(l, l + 2 * c + 2)): ctrl["sig_c+1"] += 1
        if smith(act(l, xiZ(2, c + 1, K(j)[1], lambda m: K(j)[m]), l + 1)) != s1: ctrl["wrong_shift"] += 1
ctrl["eta2"] = int(v2(Fraction(2)) != 0)
print("controls (each must be > 0):", ctrl)
ok(all(v > 0 for v in ctrl.values()), "controls fire")
print(f"checks {NC[0]}, failures {NF[0]}")
