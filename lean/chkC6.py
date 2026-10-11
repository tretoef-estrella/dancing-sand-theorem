#!/usr/bin/env python3
"""Brute force for Lean piece C6 (houses, windows, penalties: Lemmas 7.5-7.7), Grepy Escribano, 6 Oct 2026.
Exhaustive for k <= KMAX, every I subset of [0,k), every l < 2^k, alpha in {1,2}. Controls must fail somewhere."""
import itertools, sys

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6

def s2(x): return bin(x).count('1')
def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)
def oE(E): return sum(2**t for t in E)
def bit(x, u): return (x >> u) & 1
def r_(u, x): return v2((x >> u) + 1)

def nxt(k, I, t): return min([u for u in list(I) + [k] if u > t])
def hh(k, I, t): return nxt(k, I, t) - t
def gamma(k, I, D):
    if not D: return 0
    m = min(D)
    return sum(hh(k, I, u) for u in I if u not in D and u > m)
def ruler(k, I, a, mu, E): return sum(hh(k, I, t) - a * 2**t for t in E) - kappa(mu, oE(E))
def J(k, l, E): return 1 if l + oE(E) >= 2**k else 0
def xH(k, I, a, l, D):
    Dc = tuple(t for t in I if t not in D)
    return ruler(k, I, a, l, D) - ruler(k, I, a, l, Dc)
def subsets(I):
    for r in range(len(I) + 1):
        for c in itertools.combinations(I, r): yield c
def carry(l, E, u): return 1 if (l % 2**u) + (oE(E) % 2**u) >= 2**u else 0
def wdata(k, I, l, a, t, ctrl_noplus=False):
    h = hh(k, I, t); T = bit(l, t)
    if T == 1: kap = min(r_(t, l), h)
    else: kap = (0 if ctrl_noplus else 1) + min(r_(t + 1, l), h - 1)
    sat = 1 if kap == h else 0
    tau = h - a * 2**t - (kap if T == 1 else 0)
    return T, kap, sat, tau, h

fails = 0; cnt = {}; ctrl = {}
def check(c, m):
    global fails
    if not c:
        fails += 1
        if fails <= 20: print('FAIL', m)
def tick(n): cnt[n] = cnt.get(n, 0) + 1
def control(n, broke): ctrl[n] = ctrl.get(n, 0) + (1 if broke else 0)

for k in range(0, KMAX + 1):
    K = 2**k
    for I in subsets(tuple(range(k))):
        Isub = list(subsets(I))
        for a in (1, 2):
            # Lemma A and A' (range of mu / m)
            for mu in range(4 * K):
                l = mu % K; rk = r_(k, mu)
                for E in Isub:
                    check(ruler(k, I, a, mu, E) == ruler(k, I, a, l, E) - rk * J(k, l, E), f'A k={k} I={I} mu={mu} E={E}'); tick('A')
                    control('A with bit_k for r_k', ruler(k, I, a, mu, E) != ruler(k, I, a, l, E) - bit(mu, k) * J(k, l, E))
                m = mu; Pr, Pc = r_(k, m), r_(k, m + K)
                check((Pr == 0) != (Pc == 0), f'A one-zero k={k} m={m}'); tick('A-onezero')
                for A_ in Isub:
                    for B in Isub:
                        cH = ruler(k, I, a, l, A_) - ruler(k, I, a, l, B) + gamma(k, I, set(A_) - set(B))
                        chat = ruler(k, I, a, m, A_) - ruler(k, I, a, m + K, B) + gamma(k, I, set(A_) - set(B))
                        check(chat == cH - Pr * J(k, l, A_) + Pc * J(k, l, B), f"A' cost k={k} m={m}"); tick("A'-cost")
                    D = A_; Dc = tuple(t for t in I if t not in D)
                    clk = ruler(k, I, a, m, D) - ruler(k, I, a, m + K, Dc)
                    check(clk == xH(k, I, a, l, D) - Pr * J(k, l, D) + Pc * J(k, l, Dc), f"A' clock k={k} m={m}"); tick("A'-clock")
            for l in range(K):
                # A0
                for D in Isub:
                    Dc = tuple(t for t in I if t not in D)
                    check(xH(k, I, a, l, Dc) == -xH(k, I, a, l, D), 'A0 antisym'); tick('A0')
                for E in Isub:
                    for F in Isub:
                        if oE(E) <= oE(F): check(J(k, l, E) <= J(k, l, F), 'A0 upset'); tick('A0-up')
                # Lemma B
                for E in Isub:
                    if I: check(carry(l, E, min(I)) == 0, 'B1'); tick('B1')
                    tot = 0
                    for t in I:
                        T, kap, sat, tau, h = wdata(k, I, l, a, t)
                        d = 1 if t in E else 0; c = carry(l, E, t)
                        car = sum(carry(l, E, u + 1) for u in range(t, nxt(k, I, t)))
                        if T == 1: check(car == (kap if (d or c) else 0), f'B2 k={k} I={I} l={l} E={E} t={t}'); tick('B2')
                        else:
                            check(car == (kap if (d and c) else 0), f'B3 k={k} I={I} l={l} E={E} t={t}'); tick('B3')
                            _, kap0, _, _, _ = wdata(k, I, l, a, t, ctrl_noplus=True)
                            control('B3 without 1+', car != (kap0 if (d and c) else 0))
                        check((carry(l, E, nxt(k, I, t)) == 1) == (car > 0 and sat == 1), 'B4'); tick('B4')
                        cond = (T == 1 and t not in E) or (T == 0 and t in E)
                        tot += kap * c * (1 if cond else 0)
                    rhs = sum(wdata(k, I, l, a, t)[3] for t in E) - tot
                    check(ruler(k, I, a, l, E) == rhs, f'B5 k={k} I={I} l={l} E={E}'); tick('B5')
                    check(J(k, l, E) == carry(l, E, k), 'B6'); tick('B6')
                # Lemma C
                if I:
                    c_ = max(I); Ip = tuple(t for t in I if t != c_); lp = l % 2**c_
                    T, kap, sat, tau, h = wdata(k, I, l, a, c_)
                    assert h == k - c_
                    def Rp(E): return ruler(c_, Ip, a, lp, E)
                    def Jp(E): return J(c_, lp, E)
                    def xp(D): return xH(c_, Ip, a, lp, D)
                    def d1(D): return -tau - (kap if T == 1 else 0) * Jp(D) + (kap if T == 0 else 0) * Jp(tuple(t for t in Ip if t not in D))
                    for D0 in subsets(Ip):
                        D0c = D0 + (c_,)
                        check(ruler(k, I, a, l, D0) == Rp(D0) - (kap if T == 1 else 0) * Jp(D0), 'C1'); tick('C1')
                        check(ruler(k, I, a, l, D0c) == tau + Rp(D0) - (kap if T == 0 else 0) * Jp(D0), 'C2'); tick('C2')
                        check(J(k, l, D0) == (1 if T == 1 else 0) * sat * Jp(D0), 'C3'); tick('C3')
                        control('C3 without sat', J(k, l, D0) != (1 if T == 1 else 0) * Jp(D0))
                        check(J(k, l, D0c) == sat * ((1 if T == 1 else 0) + (1 if T == 0 else 0) * Jp(D0)), 'C4'); tick('C4')
                        check(gamma(k, I, set(D0c)) == gamma(c_, Ip, set(D0)), 'C5b'); tick('C5')
                        if D0:
                            check(gamma(k, I, set(D0)) == gamma(c_, Ip, set(D0)) + h, 'C5a'); tick('C5')
                            control('C5 without +h', gamma(k, I, set(D0)) != gamma(c_, Ip, set(D0)))
                        D0cp = tuple(t for t in Ip if t not in D0)
                        check(xH(k, I, a, l, D0) == xp(D0) + d1(D0), 'C6'); tick('C6')
                        check(xH(k, I, a, l, D0c) == -(xp(D0cp) + d1(D0cp)), 'C7'); tick('C7')

print('KMAX', KMAX)
print('COUNTS', cnt)
print('TOTAL FAILURES', fails)
print('CONTROLS', ctrl, 'ALL FIRE' if ctrl and all(v > 0 for v in ctrl.values()) else 'SOME CONTROL SILENT')
