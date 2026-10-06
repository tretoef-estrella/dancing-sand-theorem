"""time the rule of §1.2 at n = 1024 (claim of §1.2: «n = 1024 takes seconds»), and print a digest."""
import sys, time, hashlib
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import rule
t0 = time.time()
for k in range(1, 1025):
    rule.multiplicities(k)   # warm the cache in order (my recursion is in n)
g = rule.syl2_plus_free(1024)
t1 = time.time()
tot = sum(c for e, c in g.items() if e != rule.INF)
print("n=1024: distinct exponents", len(g), "max finite exponent", max(e for e in g if e != rule.INF),
      "number of cyclic factors == 2^1023 - 1:", tot == 2**1023 - 1, f"time {t1-t0:.1f}s")
print("top of the podium:", sorted((e for e in g if e != rule.INF), reverse=True)[:5])
