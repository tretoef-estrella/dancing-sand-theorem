# chkC50f.py — brute force for Lean piece C50f (paper v8 §10.7: the glued system on T(l), the
# arms of an even family as operators, and Theorem 10.22 numerically). Grepy Escribano, 10 Oct 2026.
# Model and helpers copied from chkC49.py (exact rationals; lattice model of T(l) from chk_lattice_lib).
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

def ZFc(i):                                  # ZF i = -1 - (-1)^i ShInvF, a constant series
    e = (-1) ** i
    return lambda m, f: (-1 - e * shInv[0]) if m == 0 else -e * shInv[m]
def ZopC(l, d):                              # C39 Zop on T(l): -1 - parOp d * ShInv
    W, Fm, pows, n = ops(l)
    Sh = eye(n)
    for s in range(1, len(pows)): Sh = add(Sh, sc(dfi(s + 1), pows[s]))
    Nil = sub(Sh, eye(n)); Shi = eye(n); T = eye(n)
    for _ in range(n + 1): T = sc(-1, mm(T, Nil)); Shi = add(Shi, T)
    S = diag([(-1) ** abs(d - w) for w in W])
    return sub(sc(-1, eye(n)), mm(S, Shi))
def bmul(x, y):                              # product of two f-dependent series (coef m f)
    return lambda m, f: sum(comb(m, a) * x(a, f) * y(m - a, f - a) for a in range(m + 1))
def glue(X, Y, Z):
    n = len(X); M = [[Fraction(0)] * (2 * n) for _ in range(2 * n)]
    for a in range(n):
        for b in range(n):
            M[a][b] = X[a][b]; M[n + a][b] = Z[a][b]; M[n + a][n + b] = Y[a][b]
    return M
def isint(M): return all(v2(x) >= 0 for r in M for x in r)   # 2-adic integrality (odd denominators are units)
NWA = [0, 0]
ctrl = {"ZF_sign": 0, "Z_zero": 0, "U_wrong_arm": 0, "Zop_shift": 0}
smith_eq_i0 = 0; smith_tot_i0 = 0
for l in range(0, 7):
    W, Fm, pows, n = ops(l)
    for B in (l + 1, l + 3):
        for i in range(0, 7):
            # (O1) the lower-left arm
            ok(act(l, ZFc(i), B) == ZopC(l, l + i), f"act ZF = Zop l={l} i={i} B={B}")
            if act(l, lambda m, f, i=i: -ZFc(i)(m, f) - 2 * (m == 0), B) != ZopC(l, l + i): ctrl["ZF_sign"] += 1
            if ZopC(l, l + i) != ZopC(l, l + i + 1): ctrl["Zop_shift"] += 1
            P0, P1 = psiF(i), psiF(i + 1)
            ok(all(2 * ZFc(i)(m, f) == P0(m, f) - P1(m, f) for m in range(MM) for f in range(0, 12)),
               f"2 ZF = PsiF i - PsiF (i+1) i={i}")
            # (O2) the halves as operators on T(l)
            A0, A1 = act(l, P0, B), act(l, P1, B)
            U = sc(Fraction(1, 2), mm(sub(A1, sc(2, eye(n))), A1))
            Up = sc(Fraction(1, 2), mm(A0, add(A0, sc(2, eye(n)))))
            ok(isint(U) and isint(Up), f"halves integral l={l} i={i}")
            Uf = lambda m, f, P1=P1: Fraction(1, 2) * bmul(P1, lambda a, g: P1(a, g) - 2 * (a == 0))(m, f)
            Upf = lambda m, f, P0=P0: Fraction(1, 2) * bmul(P0, lambda a, g: P0(a, g) + 2 * (a == 0))(m, f)
            if B >= l + 1:
                ok(act(l, Uf, l + 3) == U and act(l, Upf, l + 3) == Up, f"act U = U-matrix l={l} i={i}")
            ok(mm(A1, sub(A1, sc(2, eye(n)))) == mm(sub(A1, sc(2, eye(n))), A1), f"commute l={l} i={i}")
            ZU = sc(Fraction(1, 2), sub(Up, U))
            ok(isint(ZU), f"(U' - U)/2 integral l={l} i={i}")
            if B != l + 1: continue
            # (T) Theorem 10.22, numerically: glue(Psi_{i+1}, Psi_i, Zop) ~ glue(U, U', (U'-U)/2)
            G1 = glue(A1, A0, ZopC(l, l + i)); G2 = glue(U, Up, ZU)
            s1, s2 = smith(G1), smith(G2)
            ok(s1 is not None and s2 is not None, f"Smith defined l={l} i={i}")
            if i >= 1: ok(s1 == s2, f"Thm 10.22 Smith l={l} i={i}")
            else:
                smith_tot_i0 += 1; smith_eq_i0 += int(s1 == s2)
            if smith(glue(A1, A0, [[Fraction(0)] * n for _ in range(n)])) != s1: ctrl["Z_zero"] += 1
            A2 = act(l, psiF(i + 2), B)                # the wrong arm: Psi_{i+2} in place of Psi_{i+1}
            Uw = sc(Fraction(1, 2), mm(sub(A2, sc(2, eye(n))), A2)); Zw = sc(Fraction(1, 2), sub(Up, Uw))
            if not (isint(Uw) and isint(Zw)): NWA[0] += 1; ctrl["U_wrong_arm"] += 1
            elif smith(glue(Uw, Up, Zw)) != s2: NWA[1] += 1; ctrl["U_wrong_arm"] += 1
print("i = 0 (not claimed here, C50h): Smith equal in", smith_eq_i0, "of", smith_tot_i0)
print("wrong arm: non-integral", NWA[0], "different Smith", NWA[1])
print("controls (each must be > 0):", ctrl)
ok(all(v > 0 for v in ctrl.values()), "controls fire")
print(f"checks {NC[0]}, failures {NF[0]}")
