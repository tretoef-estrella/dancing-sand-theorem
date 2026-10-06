# tilt_dp.py — «Grepy el volador 6», 4 Oct 2026. Explicit tilting lattices T(l) over Z_(2) with ALL divided powers F^(m)
# and the floor operator D, built by flight 2's two moves (A.1 «doblar» Phi, B.1 V (x) Phi):
#   Phi(N) = N[u]/(u^2 - 2F_N): F^(2s) = F_N^(s)/(2s-1)!! on both slots, F^(2s+1)(b0 n) = b1 F_N^(s) n/(2s+1)!!,
#            F^(2s+1)(b1 n) = (2s+2)/(2s+1)!! b0 F_N^(s+1) n ;  floor(b0 n) = 2 floor(n), floor(b1 n) = 2 floor(n) + 1.
#   V (x) M: F^(m) = 1 (x) F_M^(m) + F_V (x) F_M^(m-1);  floor adds.
#   T(0) = Z;  T(2l+1) = Phi(T(l));  T(2l+2) = V (x) Phi(T(l)).
# Matrices are dicts {(row, col): Fraction} (sparse), dimension 2^(k+|I|).
from fractions import Fraction
from functools import lru_cache

def dfact_odd(s):           # (2s-1)!! with (-1)!! = 1
    r = 1
    for t in range(1, 2 * s, 2): r *= t
    return r

class Lat:
    def __init__(self, dim, floor, Fdp):
        self.dim = dim; self.floor = floor; self.Fdp = Fdp   # Fdp[m] = sparse matrix of F^(m), m = 0..top
    def F(self, m):
        return self.Fdp[m] if m < len(self.Fdp) else {}

def Z():
    return Lat(1, [0], [{(0, 0): Fraction(1)}])

def phi(N):
    d = N.dim; dim = 2 * d
    floor = [2 * f for f in N.floor] + [2 * f + 1 for f in N.floor]   # b0 slot first, then b1 slot
    top = 2 * (len(N.Fdp) - 1) + 1
    Fdp = []
    for m in range(top + 1):
        M = {}
        if m % 2 == 0:
            s = m // 2; c = Fraction(1, dfact_odd(s))
            for (r, q), x in N.F(s).items():
                M[(r, q)] = M.get((r, q), 0) + c * x
                M[(d + r, d + q)] = M.get((d + r, d + q), 0) + c * x
        else:
            s = (m - 1) // 2
            c1 = Fraction(1, dfact_odd(s + 1))                 # (2s+1)!!
            for (r, q), x in N.F(s).items():                   # b0 n -> b1 F^(s) n / (2s+1)!!
                M[(d + r, q)] = M.get((d + r, q), 0) + c1 * x
            c2 = Fraction(2 * s + 2, dfact_odd(s + 1))
            for (r, q), x in N.F(s + 1).items():               # b1 n -> (2s+2)/(2s+1)!! b0 F^(s+1) n
                M[(r, d + q)] = M.get((r, d + q), 0) + c2 * x
        Fdp.append({k: v for k, v in M.items() if v})
    return Lat(dim, floor, Fdp)

def vtimes(Mo):
    d = Mo.dim; dim = 2 * d
    floor = list(Mo.floor) + [f + 1 for f in Mo.floor]   # b0 (x) M first, then b1 (x) M
    top = len(Mo.Fdp)
    Fdp = []
    for m in range(top + 1):
        M = {}
        for (r, q), x in Mo.F(m).items():
            M[(r, q)] = M.get((r, q), 0) + x; M[(d + r, d + q)] = M.get((d + r, d + q), 0) + x
        if m >= 1:
            for (r, q), x in Mo.F(m - 1).items():          # F_V (x) F^(m-1): b0 (x) n -> b1 (x) F^(m-1) n
                M[(d + r, q)] = M.get((d + r, q), 0) + x
        Fdp.append({k: v for k, v in M.items() if v})
    return Lat(dim, floor, Fdp)

@lru_cache(None)
def T(l):
    if l == 0: return Z()
    if l % 2 == 1: return phi(T((l - 1) // 2))
    return vtimes(phi(T((l - 2) // 2)))

def dense(M, dim):
    A = [[Fraction(0)] * dim for _ in range(dim)]
    for (r, q), x in M.items(): A[r][q] += x
    return A

def to_int(A):
    """scale a matrix of 2-adic integers (odd denominators) to an integer matrix with the same 2-adic Smith form."""
    from math import lcm
    L = 1
    for row in A:
        for x in row: L = lcm(L, Fraction(x).denominator)
    assert L % 2 == 1, 'non-integral entry'
    return [[int(Fraction(x) * L) for x in row] for row in A]
