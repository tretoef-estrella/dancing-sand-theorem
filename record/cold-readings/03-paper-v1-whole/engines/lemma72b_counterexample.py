"""Counterexample to the INTEGER part of Lemma 7.2(b) as stated (cold reader, 2026-10-05).
x = (3,4,3,4) is cut at b = 2 (fit(x) = fit(x_<2) ++ fit(x_>=2) = (3.5,3.5,3.5,3.5)); delta = (1,1,0,0) is
non-increasing and constant between cuts. Claim of 7.2(b): intfit(x + delta) = intfit(x) + delta. Check it."""
import sys
from fractions import Fraction
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from rule import pava_blocks, integer_antitonic_fit

def realfit(x):
    out = []
    for S, p in pava_blocks(x):
        out += [Fraction(S, p)] * p
    return out

x = [3, 4, 3, 4]; b = 2; delta = [1, 1, 0, 0]
print("fit(x)          =", realfit(x))
print("fit(x<b)++fit(x>=b) =", realfit(x[:b]) + realfit(x[b:]), " -> cut at b:", realfit(x) == realfit(x[:b]) + realfit(x[b:]))
xd = [a + d for a, d in zip(x, delta)]
print("fit(x+delta)    =", realfit(xd), " fit(x)+delta =", [f + d for f, d in zip(realfit(x), delta)])
A = integer_antitonic_fit(xd); B = [a + d for a, d in zip(integer_antitonic_fit(x), delta)]
print("intfit(x+delta) =", A, " intfit(x)+delta =", B, " EQUAL" if A == B else " DIFFERENT (as multisets: %s)" % (sorted(A) != sorted(B)))
# control: a delta that is constant across the straddling level set must give equality
delta2 = [1, 1, 1, 1]
A2 = integer_antitonic_fit([a + d for a, d in zip(x, delta2)]); B2 = [a + d for a, d in zip(integer_antitonic_fit(x), delta2)]
print("control delta=(1,1,1,1):", A2, B2, "EQUAL" if A2 == B2 else "DIFFERENT")
