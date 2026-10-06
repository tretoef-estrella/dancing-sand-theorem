# gate_theoremO.py — Theorem 6.2 (Theorem O) of «The Dancing Sand Theorem» v2, by brute force.
# For I = {0, ..., s-1}, s <= SMAX (Theorem O depends only on s = |I|), and every 0 <= r <= N = 2^s, count the bijections
# L_r -> F_r (L_r = last r dancers, F_r = first r, o-order) all of whose arrows D -> E (E subset of D) are golden:
# D \ E empty or a tail I ∩ [t, k) of I.  Expected: exactly 1 in every case.
# The count stops at 2 (only «exactly one» is tested).
# Controls (must give a count != 1 somewhere): «golden» replaced by (c1) any subset, (c2) any run of consecutive digits of I.
import sys
SMAX = int(sys.argv[1])
def count(N, r, ok):
    rows = list(range(N - r, N)); cols = set(range(r))
    opts = [[e for e in range(r) if ok(p, e)] for p in rows]
    used = [False] * N
    def go(j):
        if j == r: return 1
        t = 0
        for e in opts[j]:
            if not used[e]:
                used[e] = True; t += go(j + 1); used[e] = False
                if t >= 2: return t   # only «exactly one» matters: stop at two
        return t
    return go(0)
def golden(s):
    def ok(p, e):
        if e & ~p: return False
        d = p ^ e
        if d == 0: return True
        lo = (d & -d).bit_length() - 1
        tail = ((1 << s) - 1) & ~((1 << lo) - 1)
        return d == tail
    return ok
def anysub(s): return lambda p, e: (e & ~p) == 0
def run(s):
    def ok(p, e):
        if e & ~p: return False
        d = p ^ e
        if d == 0: return True
        x = d >> ((d & -d).bit_length() - 1)
        return (x & (x + 1)) == 0
    return ok
tot = bad = c1 = c2 = 0
for s in range(SMAX + 1):
    N = 1 << s
    for r in range(N + 1):
        tot += 1
        if count(N, r, golden(s)) != 1: bad += 1
        if count(N, r, anysub(s)) != 1: c1 += 1
        if count(N, r, run(s)) != 1: c2 += 1
print("Theorem O, |I| <= %d: %d (s, r) cases, %d with a count != 1" % (SMAX, tot, bad))
print("control c1 (any subset): count != 1 in %d cases; control c2 (any run): count != 1 in %d cases" % (c1, c2))
print("VIGIA-INNER-DONE")
