# gate_l72_mine.py — Grepy el lector frío del cubo 4, 2026-10-05. My own gate for Lemma 7.2(b) of v2.
# Part A: exhaustive search of the smallest counterexamples to the v1 integer claim
#         (delta non-increasing integer, changing only at a NON-strict cut).
# Part B: random sequences; the restated (b) (delta changes only at strict cuts) must never fail;
#         controls: (B1) a jump at a non-strict cut, (B2) a jump at a position that is not a cut.
import itertools
import random
import sys
from fitlib import fit_checked, int_fit, all_cuts, strict_cuts, level_sets, is_cut

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20261005
TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 50000


def delta_from_jumps(n, jumps, base=0):
    """delta_j = base + sum of the jumps g_p over jump positions p > j (non-increasing)."""
    return [base + sum(g for p, g in jumps.items() if p > j) for j in range(n)]


def add(a, b):
    return [u + v for u, v in zip(a, b)]


# ---------- Part A: exhaustive smallest counterexamples ----------
print("PART A: exhaustive search, entries in [0, R], delta = 0/1 step (and 0/2 step) at a non-strict cut")
found = {}
for n, R in ((2, 6), (3, 6), (4, 5), (5, 3)):
    cnt_ns = 0
    cnt_bad = 0
    first = None
    for x in itertools.product(range(R + 1), repeat=n):
        x = list(x)
        cuts = all_cuts(x)
        sc = set(strict_cuts(x))
        for b in cuts:
            if b in sc:
                continue
            cnt_ns += 1
            for g in (1, 2):
                d = delta_from_jumps(n, {b: g})
                lhs = int_fit(add(x, d))
                rhs = add(int_fit(x), d)
                # the real part must hold at every cut, strict or not
                assert fit_checked(add(x, d)) == add(fit_checked(x), d), ("real part fails", x, b)
                if lhs != rhs:
                    cnt_bad += 1
                    if first is None:
                        first = (x, b, g, d, lhs, rhs)
    print(f"  n={n} R={R}: non-strict cuts {cnt_ns}, counterexamples (with g=1,2) {cnt_bad}, first {first}")
    found[n] = first

# ---------- Part B: random sequences ----------
rng = random.Random(SEED)
stats = dict(trials=0, with_strict=0, tests=0, fail_real=0, fail_levels=0, fail_strict_kept=0,
             fail_int=0, fail_cuts_kept=0,
             c1_trials=0, c1_int_fail=0, c1_real_fail=0,
             c2_trials=0, c2_real_fail=0, c2_int_fail=0)
examples_c1 = []
for t in range(TRIALS):
    n = rng.randint(2, 10)
    R = rng.choice((2, 3, 4, 6, 9))
    x = [rng.randint(-R, R) for _ in range(n)]
    stats["trials"] += 1
    z = fit_checked(x)
    cuts = all_cuts(x)
    sc = strict_cuts(x)
    nsc = [b for b in cuts if b not in sc]
    noncut = [b for b in range(1, n) if b not in cuts]
    # --- the restated (b): jumps only at strict cuts
    if sc:
        stats["with_strict"] += 1
    js = {p: rng.randint(1, 3) for p in sc if rng.random() < 0.7}
    d = delta_from_jumps(n, js, base=rng.randint(-3, 3))
    xd = add(x, d)
    stats["tests"] += 1
    zd = fit_checked(xd)
    if zd != add(z, d):
        stats["fail_real"] += 1
    if level_sets(zd) != level_sets(z):
        stats["fail_levels"] += 1
    if not set(sc) <= set(strict_cuts(xd)):
        stats["fail_strict_kept"] += 1
    if not set(cuts) <= set(all_cuts(xd)):
        stats["fail_cuts_kept"] += 1
    if int_fit(xd) != add(int_fit(x), d):
        stats["fail_int"] += 1
    # --- control B1: one jump at a non-strict cut (it is still a cut: the real part must hold)
    if nsc:
        b = rng.choice(nsc)
        js1 = dict(js)
        js1[b] = rng.randint(1, 3)
        d1 = delta_from_jumps(n, js1)
        stats["c1_trials"] += 1
        if fit_checked(add(x, d1)) != add(z, d1):
            stats["c1_real_fail"] += 1
        if int_fit(add(x, d1)) != add(int_fit(x), d1):
            stats["c1_int_fail"] += 1
            if len(examples_c1) < 5:
                examples_c1.append((x, d1, int_fit(add(x, d1)), add(int_fit(x), d1)))
    # --- control B2: one jump at a position that is not a cut
    if noncut:
        b = rng.choice(noncut)
        d2 = delta_from_jumps(n, {b: rng.randint(1, 3)})
        stats["c2_trials"] += 1
        if fit_checked(add(x, d2)) != add(z, d2):
            stats["c2_real_fail"] += 1
        if int_fit(add(x, d2)) != add(int_fit(x), d2):
            stats["c2_int_fail"] += 1

print("PART B: seed", SEED)
for k, v in stats.items():
    print(f"  {k} = {v}")
print("  first control-B1 failures:")
for e in examples_c1:
    print("   ", e)
ok = all(stats[k] == 0 for k in ("fail_real", "fail_levels", "fail_strict_kept", "fail_int", "fail_cuts_kept"))
fired = stats["c1_int_fail"] > 0 and stats["c2_real_fail"] > 0
print("RESULT restated (b):", "0 failures" if ok else "FAILURES",
      "| controls fire:", fired)
