"""Print the intermediate values of the §1.2 example (n = 6) and the §1.3 example (n = 5), from engines/rule.py."""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import rule
for n in (5, 6, 7):
    print("n =", n, "multiplicities", dict(sorted(rule.multiplicities(n).items())))
    for lam, c in sorted(rule.multiplicities(n).items(), reverse=True):
        i = (n - lam) // 2
        k, I, h = rule.family(lam)
        print(f"  lam={lam} m={c} k={k} I={I} h={h} i={i} raw={rule.raw_clocks(lam, i)} pooled={rule.pooled_clocks(lam, i)} X={rule.fmt(rule.X(lam, i))}")
    print("  Syl2+Z2 =", rule.fmt(rule.syl2_plus_free(n)), " fold:", rule.fmt(rule.fold(rule.syl2_plus_free(n))))
