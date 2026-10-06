# gate_lemma72.py — Lemma 7.2(b) of «The Dancing Sand Theorem» v2, as restated, on random sequences.
# For random integer sequences x (length 2..LMAX, entries in [-6, 6]) and random non-increasing integer sequences delta:
#  (A) delta constant between consecutive cuts of x:  fit(x + delta) = fit(x) + delta  (the real part);
#  (B) delta jumping only at STRICT cuts:  the integer fit of x + delta is the integer fit of x plus delta.
# Control: delta jumping at a cut that is not strict must break (B) in some trial (cold reader 3's example (3,4,3,4)).
import sys, random
from fractions import Fraction as Fr
def fit(x):
    B = []
    for v in x:
        B.append([Fr(v), 1])
        while len(B) > 1 and B[-2][0] * B[-1][1] <= B[-1][0] * B[-2][1]:
            s, c = B.pop(); B[-1][0] += s; B[-1][1] += c
    z = []
    for s, c in B: z += [s / c] * c
    return z, B
def ifit(x):
    z, B = fit(x); out = []
    for s, c in B:
        S = int(s); r = S % c; out += [-(-S // c)] * r + [S // c] * (c - r)
    return out
def is_cut(x, b): return fit(x)[0] == fit(x[:b])[0] + fit(x[b:])[0]
LMAX, TRIALS = int(sys.argv[1]), int(sys.argv[2])
rnd = random.Random(2026)
a = bfail = afail = ctrl_tr = ctrl_fail = 0
for _ in range(TRIALS):
    n = rnd.randint(2, LMAX); x = [rnd.randint(-6, 6) for _ in range(n)]
    z = fit(x)[0]; y = ifit(x)
    cuts = [b for b in range(1, n) if is_cut(x, b)]
    strict = [b for b in cuts if z[b - 1] > z[b]]
    for pool, kind in ((cuts, 'A'), (strict, 'B'), ([b for b in cuts if b not in strict], 'C')):
        if not pool: continue
        jumps = [b for b in pool if rnd.random() < 0.6] or [rnd.choice(pool)]
        d = [0] * n; v = 0
        for j in range(n - 1, -1, -1):
            d[j] = v
            if j in jumps: v += rnd.randint(1, 3)
        xs = [x[j] + d[j] for j in range(n)]
        if kind == 'A':
            a += 1
            if fit(xs)[0] != [z[j] + d[j] for j in range(n)]: afail += 1
        elif kind == 'B':
            if ifit(xs) != [y[j] + d[j] for j in range(n)]: bfail += 1
        else:
            ctrl_tr += 1
            if ifit(xs) != [y[j] + d[j] for j in range(n)]: ctrl_fail += 1
x = [3, 4, 3, 4]; d = [1, 1, 0, 0]
ex = ifit([x[j] + d[j] for j in range(4)]) != [ifit(x)[j] + d[j] for j in range(4)]
print("(A) real part: %d trials, %d failures; (B) integer part, jumps at strict cuts only: %d failures" % (a, afail, bfail))
print("control: jumps at non-strict cuts, %d trials, integer part broken in %d; example (3,4,3,4)/(1,1,0,0) breaks it: %s" % (ctrl_tr, ctrl_fail, ex))
print("VIGIA-INNER-DONE")
