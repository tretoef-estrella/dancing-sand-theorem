#!/usr/bin/env python3
"""Brute force for Lean piece C3 (paper v8 §5: rulers, gold, clocks; Lemma 5.1, Props 5.2-5.4), as
pure integer identities. Controls must fail somewhere. Grepy Escribano, 6 Oct 2026."""
import sys
from itertools import combinations
FAIL = 0; ctrl = {}; counts = {}
def check(c, m):
    global FAIL
    if not c:
        FAIL += 1
        if FAIL <= 10: print("FAIL", m)
def control(n, c): ctrl.setdefault(n, 0); ctrl[n] += (0 if c else 1)
def tick(n): counts[n] = counts.get(n, 0) + 1
def s2(x): return bin(x).count('1')
def v2(x):
    assert x > 0; k = 0
    while x % 2 == 0: x //= 2; k += 1
    return k
def kap(a, b): return s2(a) + s2(b) - s2(a + b)
def phi(x): return x + v2(x)
def subsets(S):
    S = sorted(S)
    for r in range(len(S) + 1):
        for c in combinations(S, r): yield frozenset(c)
for k in range(0, 7):
    K = 2 ** k
    for I in subsets(range(k)):
        nxt = {t: min([u for u in I if u > t] + [k]) for t in I}
        h = {t: nxt[t] - t for t in I}
        t1 = min(I) if I else k
        o = lambda E: sum(2 ** t for t in E)
        def delta(D): return 0 if not D else k - len(D) - min(D)
        def gamma(D): return 0 if not D else sum(h[u] for u in I - D if u > min(D))
        G = lambda E: sum(h[t] - 1 for t in E)
        def R(mu, E, al): return sum(h[t] - al * 2 ** t for t in E) - kap(mu, o(E))
        def Rs(E, al): return sum(h[t] - al * 2 ** t for t in E) - kap(K - 1, o(E))
        lam1 = K + o(I)
        for D in subsets(I):
            # Lemma 5.1
            check(delta(D) == G(D) + gamma(D), ("5.1a", k, I, D)); tick("5.1a")
            tail = (not D) or D == frozenset(u for u in I if u >= min(D))
            check((gamma(D) == 0) == tail, ("5.1b", k, I, D)); tick("5.1b")
            control("5.1a without gamma", delta(D) == G(D))
            # kappa(K-1, o_E) = k - min E
            check(kap(K - 1, o(D)) == (k - min(D) if D else 0), ("kap(K-1)", k, D)); tick("kap(K-1,oE)")
        for a in subsets(I):
            for b in subsets(a):
                Dl = a - b
                check(K - o(Dl) >= 1, ("window", k, I, a, b))
                for al in (1, 2, 3):
                    for i in range(1, 18):
                        m = i - 1
                        lhs = 1 - K + o(Dl) + delta(Dl) + sum(al + v2(i + d) for d in range(o(a), o(b) + K))
                        rhs = al * K + kap(m, K) + R(m, a, al) - R(m + K, b, al) + gamma(Dl)
                        check(lhs == rhs, ("5.2", k, I, a, b, al, i)); tick("5.2")
                        control("5.2 with R_m on both sides", lhs == al * K + kap(m, K) + R(m, a, al) - R(m, b, al) + gamma(Dl))
                    if a:
                        lhs0 = 1 - K + o(Dl) + delta(Dl) + sum(al + v2(d) for d in range(o(a), o(b) + K))
                        check(lhs0 == al * K + Rs(a, al) - Rs(b, al) + gamma(Dl), ("5.4 val", k, I, a, b, al)); tick("5.4 val")
        for D in subsets(I):
            E = I - D; xi = lam1 - 2 * o(D)
            check(xi >= 1, ("xi", k, I, D))
            for i in range(0, 18):
                if i == 0 and not D: continue
                u = phi(xi) + kap(i + o(D) - 1, xi) + sum(h[t] for t in D)
                if i >= 1:
                    m = i - 1
                    x = R(m, D, 1) - R(m + K, E, 1)
                    check(u == k + K + kap(m, K) + x, ("5.3", k, I, D, i)); tick("5.3")
                    control("5.3 without kappa(m,K)", u == k + K + x)
                else:
                    xs = Rs(D, 1) - Rs(E, 1)
                    check(u == k + K + xs, ("5.4 clock", k, I, D)); tick("5.4 clock")
for n, v in counts.items(): print(f"checked {n}: {v}")
print("controls (cases where the FALSE variant failed; must be > 0):")
ok = True
for n, v in ctrl.items(): print(f"  {n}: {v}"); ok = ok and v > 0
print("FAILURES:", FAIL); print("CONTROLS FIRE:", ok)
sys.exit(0 if FAIL == 0 and ok else 1)
