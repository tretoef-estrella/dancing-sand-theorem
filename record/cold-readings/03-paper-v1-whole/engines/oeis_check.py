"""spanning trees of Q_n/<1> from the eigenvalues 2|J|, |J| even (n>=2), vs OEIS A193134 terms fetched 2026-10-05."""
from math import comb
oeis = {2: 1, 3: 16, 4: 4096, 5: 2147483648, 6: 14167099448608935641088,
        7: 99884502526333896315983085285953467624610139734016}
for n in range(2, 8):
    num = 1
    for j in range(2, n + 1, 2):
        num *= (2 * j) ** comb(n, j)
    tau = num // 2 ** (n - 1)
    assert num % 2 ** (n - 1) == 0
    print(n, tau, "OEIS", oeis[n], "EQUAL" if tau == oeis[n] else "DIFFERENT")
