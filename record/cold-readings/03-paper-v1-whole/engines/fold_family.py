"""fold_family.py — family-level machine check of the fold law (cold reader, 2026-10-05).

For each family lambda and shift i, computes FROM THE DEFINITION
    Xbar(lambda, i) = T(lambda) / (tau_i T(lambda) + (a - 1) T(lambda)),   tau_i = F + 2(D + i),
    a = (-1)^{D+i} exp(F)  (Lemma 10.1; exp(F) = sum of divided powers),
with the divided powers of T(lambda) built from Prop. 3.1(b) (on Phi) and the coproduct (on V ⊗ M), all modulo
2^64 (odd denominators inverted), and compares with 2·X(lambda, i), X from the rule of §1.2 (engines/rule.py),
which my other gates show equals coker(tau_i on T(lambda)).
Self-checks: F^{(1)} equals the F of family_lattice.T; r!·F^{(r)} = F^r for r <= 6; a^2 = 1; a commutes with tau.
CONTROL: a -> -a (quotient by a + 1) must disagree somewhere.
Cells whose predicted largest exponent is >= 60 are skipped and counted.
Usage: python3 engines/fold_family.py LMAX IMAX
"""
import sys
import numpy as np
from collections import Counter
from math import factorial
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from smith2 import smith2, BIG
from lattices import T
import rule

LMAX, IMAX = int(sys.argv[1]), int(sys.argv[2])
U = np.uint64
MOD = 1 << 64


def inv(x):
    return pow(x % MOD, -1, MOD)


def dfact(n):  # (n)!! for odd n >= -1
    r = 1
    while n > 1:
        r *= n; n -= 2
    return r


def mulc(A, c):
    return (A * U(c % MOD))


_dp = {}


def divpowers(l):
    """list [F^(0), ..., F^(l)] on T(l), uint64 mod 2^64."""
    if l in _dp:
        return _dp[l]
    if l == 0:
        res = [np.ones((1, 1), dtype=U)]
    elif l % 2 == 1:
        res = phi_dp(divpowers((l - 1) // 2), l)
    else:
        res = v_dp(phi_dp(divpowers((l - 2) // 2), l - 1), l)
    _dp[l] = res
    return res


def phi_dp(dpN, top):
    n = dpN[0].shape[0]
    Z = np.zeros((n, n), dtype=U)
    def get(s):
        return dpN[s] if s < len(dpN) else Z
    out = []
    for r in range(top + 1):
        M = np.zeros((2 * n, 2 * n), dtype=U)
        if r % 2 == 0:
            s = r // 2
            c = inv(dfact(2 * s - 1))
            M[:n, :n] = mulc(get(s), c); M[n:, n:] = mulc(get(s), c)
        else:
            s = (r - 1) // 2
            M[n:, :n] = mulc(get(s), inv(dfact(2 * s + 1)))                 # b0 n -> b1 F^(s) n
            M[:n, n:] = mulc(get(s + 1), (2 * s + 2) * inv(dfact(2 * s + 1)))  # b1 n -> b0 F^(s+1) n
        out.append(M)
    return out


def v_dp(dpM, top):
    n = dpM[0].shape[0]
    Z = np.zeros((n, n), dtype=U)
    def get(s):
        return dpM[s] if 0 <= s < len(dpM) else Z
    out = []
    for r in range(top + 1):
        M = np.zeros((2 * n, 2 * n), dtype=U)
        M[:n, :n] = get(r); M[n:, n:] = get(r); M[n:, :n] = get(r - 1)
        out.append(M)
    return out


def expF(lam):
    """exp(F) on T(lam) without storing the divided powers of T(lam) itself when lam is large."""
    if lam <= 31:
        E = np.zeros_like(divpowers(lam)[0])
        for M in divpowers(lam):
            E += M
        return E
    if lam % 2 == 1:
        dps = phi_dp(divpowers((lam - 1) // 2), lam)
        E = np.zeros_like(dps[0])
        for M in dps:
            E += M
        return E
    dps = phi_dp(divpowers((lam - 2) // 2), lam - 1)
    Em = np.zeros_like(dps[0])
    for M in dps:
        Em += M
    n = Em.shape[0]
    E = np.zeros((2 * n, 2 * n), dtype=U)
    E[:n, :n] = Em; E[n:, n:] = Em; E[n:, :n] = Em   # exp(F_V) ⊗ exp(F_M), exp(F_V) = [[1,0],[1,1]]
    return E


stats = Counter()
for lam in range(1, LMAX + 1):
    Fm, w = T(lam)
    r = len(w)
    F64 = Fm.astype(np.int64).astype(U)
    if lam <= 31:
        dp = divpowers(lam)
        if not np.array_equal(dp[1], F64):
            stats["SELFCHECK FAIL F^(1)"] += 1
        P = np.eye(r, dtype=U)
        for q in range(1, min(6, lam) + 1):
            P = P @ F64
            if not np.array_equal(P, mulc(dp[q], factorial(q))):
                stats["SELFCHECK FAIL r!F^(r)=F^r"] += 1
    E = expF(lam)
    Dfl = np.array([(lam - x) // 2 for x in w], dtype=np.int64)
    for i in range(0, IMAX + 1):
        X = rule.X(lam, i)
        mx = max((e for e in X if e != rule.INF), default=0)
        if mx >= 60:
            stats["SKIPPED (exponent >= 60)"] += 1
            continue
        sign = np.where((Dfl + i) % 2 == 0, 1, MOD - 1).astype(U)
        A = sign[:, None] * E                       # a = (-1)^{D+i} exp(F)
        I = np.eye(r, dtype=U)
        tau = F64 + U(2) * np.diag((Dfl + i).astype(U))
        if not np.array_equal(A @ A, I):
            stats["SELFCHECK FAIL a^2 = 1"] += 1
        if not np.array_equal(A @ tau, tau @ A):
            stats["SELFCHECK FAIL a tau = tau a"] += 1
        pred = rule.fold(X)
        for name, Aop in (("a", A), ("CONTROL -a", (U(0) - A))):
            big = np.zeros((2 * r, 2 * r), dtype=U)
            big[:r, :r] = tau; big[:r, r:] = Aop - I
            res = smith2(big.astype(np.int64) if False else big.view(np.int64), 64)
            res[BIG] -= r
            got = Counter({e: c for e, c in res.items() if e != 0 and c > 0})
            if name == "a":
                stats["cells compared"] += 1
                if got != pred:
                    stats["FAIL Xbar != 2X"] += 1
                    if stats["FAIL Xbar != 2X"] <= 5:
                        print("MISMATCH", lam, i, rule.fmt(got), rule.fmt(pred))
            else:
                if got != pred:
                    stats["CONTROL -a detected"] += 1
                else:
                    stats["CONTROL -a NOT detected"] += 1
print(f"lambda <= {LMAX}, 0 <= i <= {IMAX}")
for k in sorted(stats):
    print(f"  {k}: {stats[k]}")
print("TOTAL FAIL COUNT:", sum(v for kk, v in stats.items() if "FAIL" in kk))
