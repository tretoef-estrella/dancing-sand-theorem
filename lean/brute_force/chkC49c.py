#!/usr/bin/env python3
"""Brute force for Lean piece C49c (paper v8 §10.6: Smith form and cokernel of Xi at c = 0).
Grepy Escribano, 10 Oct 2026. Reuses the engines of chkC15.py (dance of C13, slots, dancers, Smith
exponents, PAVA). Claims measured:
 (D) the integer final matrix M = finalMatrix Z ds alpha 0, in slot order, has the data Data0:
     off nested pairs 0; the row of the slot with Dset = {} is 0; on nested pairs with Dset s != {}
     the entry is nonzero with 2-adic valuation exactly alpha*2^k + cHatH(Dset s, Dset s')
     (cHatH = RH(a) - RH(b) + gamma(a minus b), RH = ruler with mu = 2^k - 1).
 (G) every integer matrix with Data0 has the Smith exponents of C15 Z3: alpha*2^k + yhatSharp, and one
     infinite exponent (tested on M with every entry multiplied by a random odd integer).
 (Z) the truncation lemma with a zero diagonal entry: Z = D + 2^N R, D = diag(u_j 2^E_j (j < n-1), 0),
     E_j < N, det Z = 0  =>  Smith exponents of Z are the E_j and one infinite exponent.
Controls (must fire): valuation +1; mu = 2^k instead of 2^k - 1; one nested entry doubled changes the Smith
form; (Z) with some E_j = N; (Z) with det Z != 0."""
import random
from fractions import Fraction as Fr
src = open('chkC15.py').read()
exec(src[:src.index('lists = [')])
import itertools
random.seed(4903)

def hI(I, k, u): return hfun(I, k, u)
def gamma(I, k, Dl):
    if not Dl: return 0
    mn = min(Dl)
    return sum(hI(I, k, u) for u in I if u not in Dl and u > mn)
def RH(I, k, al, mu, E): return ruler(I, k, al, mu, E)
def cHatH(I, k, al, mu, a, b): return RH(I, k, al, mu, a) - RH(I, k, al, mu, b) + gamma(I, k, a - b)

def final_matrix(ds, alpha, i):
    psig = lambda s, f, al=alpha, i=i: Fr(2) ** (al - 1) * (i + f)
    ksig = lambda u, s, f: Fr(0)
    R, pk, kk = dance(ds, psig, ksig)
    return [[2 * pk(s, 0) if s == s1 else (2 * kk(s, s1, 0) if s1 < s else 0) for s1 in range(R)] for s in range(R)]

def want_exps(ds, alpha):
    k = len(ds); I = Iof(ds); N = 2 ** len(I); K = 2 ** k
    xs = [ruler(I, k, alpha, K - 1, dancer(I, j + 1)) - ruler(I, k, alpha, K - 1, frozenset(I) - dancer(I, j + 1)) for j in range(N - 1)]
    ys = pava_ifit(xs)
    return sorted(alpha * K + ys[j] for j in range(N - 1))

def data0(ds, alpha, Mt, mu_shift=0, vshift=0):
    """True iff Mt satisfies Data0 (with an optional wrong mu or wrong valuation, for the controls)."""
    k = len(ds); I = Iof(ds); N = 2 ** len(I); K = 2 ** k
    for s in range(N):
        a = Dset(ds, s)
        for s1 in range(N):
            b = Dset(ds, s1)
            e = Mt[s][s1]
            if not b <= a:
                if e != 0: return False
            elif not a:
                if e != 0: return False
            else:
                if e == 0: return False
                if vq(Fr(e)) != alpha * K + cHatH(I, k, alpha, K - 1 + mu_shift, a, b) + vshift: return False
    return True

lists = [tuple(x) for n in range(1, 6) for x in itertools.product([False, True], repeat=n) if n + sum(x) <= 6]
for ds in lists:
    I = Iof(ds); m = len(I); N = 2 ** m
    for alpha in (1, 2, 3):
        M = final_matrix(ds, alpha, 0)
        ok("integer", all(Fr(e).denominator == 1 for r in M for e in r), (ds, alpha))
        # (D)
        ok("D-data0", data0(ds, alpha, M), (ds, alpha))
        if m >= 1:
            fire("ctl-valuation+1", not data0(ds, alpha, M, vshift=1))
            fire("ctl-mu=2^k", not data0(ds, alpha, M, mu_shift=1))
        ex = smith_exps(M)
        if m >= 1:
            fin = sorted(v for v in ex if v is not None)
            ok("D-smith=Z3", fin == want_exps(ds, alpha) and ex.count(None) == 1, (ds, alpha, ex))
        else:
            ok("D-I-empty-zero", all(e == 0 for r in M for e in r), (ds, alpha))
        # (G) random odd multiples keep Data0, and the Smith form
        for trial in range(3):
            Mp = [[e * random.choice([1, -1, 3, -3, 5, 7, -9, 11]) for e in r] for r in M]
            ok("G-data0-kept", data0(ds, alpha, Mp), (ds, alpha, trial))
            exp = smith_exps(Mp)
            if m >= 1:
                fin = sorted(v for v in exp if v is not None)
                ok("G-smith", fin == want_exps(ds, alpha) and exp.count(None) == 1, (ds, alpha, trial, exp))
            else:
                ok("G-zero", all(v is None for v in exp), (ds, alpha))
            if m >= 1:
                nested = [(s, s1) for s in range(N) for s1 in range(N) if M[s][s1] != 0]
                s, s1 = random.choice(nested)
                Mq = [r[:] for r in Mp]; Mq[s][s1] *= 2
                exq = smith_exps(Mq)
                fire("ctl-doubled-entry-changes-smith", sorted(v for v in exq if v is not None) != want_exps(ds, alpha) or exq.count(None) != 1)

# (Z) the truncation lemma with a zero diagonal entry
def zcase(n, N, Ebound, singular):
    E = [random.randint(0, Ebound) for _ in range(n - 1)]
    u = [random.choice([1, -1, 3, 5, -7]) for _ in range(n - 1)]
    D = [[Fr(0)] * n for _ in range(n)]
    for j in range(n - 1): D[j][j] = Fr(u[j] * 2 ** E[j])
    Z = [[D[a][b] + 2 ** N * random.randint(-3, 3) for b in range(n)] for a in range(n)]
    # set the corner so that det Z = 0: corner = C A^{-1} B (Schur), computed exactly
    A = [[Z[a][b] for b in range(n - 1)] for a in range(n - 1)]
    detA = det_frac(A)
    if detA == 0: return None
    Zc = [r[:] for r in Z]; Zc[n - 1][n - 1] = Fr(0)
    corner = -det_frac(Zc) / detA      # det Z is affine in the corner with slope det A
    Z[n - 1][n - 1] = corner if singular else corner + 2 ** N
    return E, Z
for n in (2, 3, 4, 5):
    for trial in range(200):
        N = random.randint(2, 6)
        r = zcase(n, N, N - 1, True)
        if r is None: continue
        E, Z = r
        ok("Z-corner-integral", vq(Z[n - 1][n - 1]) >= N if Z[n - 1][n - 1] != 0 else True, (n, N))
        ex = smith_exps(Z)
        ok("Z-smith", sorted(v for v in ex if v is not None) == sorted(E) and ex.count(None) == 1, (n, N, E, ex))
        r2 = zcase(n, N, N, True)
        if r2 is not None:
            E2, Z2 = r2
            ex2 = smith_exps(Z2)
            fire("ctl-Z-E=N", sorted(v for v in ex2 if v is not None) != sorted(E2) or ex2.count(None) != 1)
        r3 = zcase(n, N, N - 1, False)
        if r3 is not None:
            fire("ctl-Z-det-nonzero", smith_exps(r3[1]).count(None) != 1)

tot = sum(cnt.values())
print("COUNTS", cnt)
print("TOTAL", tot, "FAILURES", len(fails), fails[:10])
print("CONTROLS", ctrl, "ALL FIRE" if all(v > 0 for v in ctrl.values()) else "SOME SILENT")
