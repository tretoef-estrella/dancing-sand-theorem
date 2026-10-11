# Python twin of run 2 (a): raw clocks from the paper, same layout as the Lean #eval.
import sys; sys.path.insert(0, 'checks')
import m2_rule as R
out = []
for lam in range(1, 64):
    k, I = R.family(lam); Ds = R.dancers_in_o_order(I)
    out.append([[R.raw_clock(lam, i, D, I, k) for j, D in enumerate(Ds) if not (i == 0 and j == 0)] for i in range(6)])
open('checks/m2_clocks_py.txt', 'w').write(repr(out)); print('written', len(out), 'families')
