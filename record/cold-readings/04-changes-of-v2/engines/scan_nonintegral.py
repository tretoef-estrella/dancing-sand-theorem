# scan_nonintegral.py — Grepy el lector frío del cubo 4, 2026-10-05.
# Over all houses H = (I, k, l, alpha), k <= KMAX, alpha <= AMAX: count level sets of fit(x_H)
# whose mean is not an integer; also after deleting the first dancer at l = 2^k - 1 (i = 0 cells).
import sys
from fitfast import blocks
KMAX = int(sys.argv[1]); AMAX = int(sys.argv[2])
def s2(a): return bin(a).count("1")
def kap(a, b): return s2(a) + s2(b) - s2(a + b)
def bits(m): return [t for t in range(m.bit_length()) if (m >> t) & 1]
def dancers(I):
    out = [0]
    for t in bits(I): out = out + [d | (1 << t) for d in out]
    return sorted(out)
tot = {}
first = {}
for k in range(1, KMAX + 1):
    for a in range(1, AMAX + 1):
        for I in range(1 << k):
            bs = bits(I) + [k]; h = {t: bs[j + 1] - t for j, t in enumerate(bs[:-1])}
            ds = dancers(I)
            for l in range(1 << k):
                R = {d: sum(h[t] - a * (1 << t) for t in bits(d)) - kap(l, d) for d in ds}
                x = [R[d] - R[I ^ d] for d in ds]
                bl = blocks(x)
                key = f"alpha{a}"
                tot[key + "_houses"] = tot.get(key + "_houses", 0) + 1
                if any(S % p for s, p, S in bl):
                    tot[key + "_houses_nonintegral"] = tot.get(key + "_houses_nonintegral", 0) + 1
                    if key not in first: first[key] = (I, k, l, a, x, [(p, S) for s, p, S in bl])
                if l == (1 << k) - 1 and I:
                    bl0 = blocks(x[1:])
                    if any(S % p for s, p, S in bl0):
                        tot[key + "_i0_nonintegral"] = tot.get(key + "_i0_nonintegral", 0) + 1
    print("k", k, "done", flush=True)
for kk in sorted(tot): print(" ", kk, "=", tot[kk])
for kk in sorted(first): print("  first", kk, first[kk])
