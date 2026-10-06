# check1.py — check 1: Syl_2 K(Q_n) (+) Z directly from the Laplacian (my engine) vs the rule as printed.
# Controls: (a) no pooling; (b) column ruler read at m instead of m + K (mission form, i >= 1 cells).
import sys, os, subprocess, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from myrule import *

HERE = os.path.dirname(os.path.abspath(__file__))
n0, n1 = int(sys.argv[1]), int(sys.argv[2])


def direct(n):
    out = subprocess.run([os.path.join(HERE, 'mysmith'), 'lap', str(n)], capture_output=True, text=True).stdout
    lines = out.strip().split('\n')
    G = {}
    for tok in lines[0].split()[1:]:
        e, c = tok.split(':')
        if int(e) > 0:
            G[int(e)] = int(c)
    z = int(lines[1].split()[1])
    if z:
        G['Z'] = z
    return G


allok = True
for n in range(n0, n1 + 1):
    t0 = time.time()
    D = direct(n)
    t1 = time.time()
    RB = group_rule(n, form='B')
    RX = group_rule(n, form='X')
    C_np = group_rule(n, form='B', pool=False)
    C_m = group_rule(n, form='X', ctrl='m_only')
    nf = sum(c for e, c in D.items() if e != 'Z')
    print(f'n={n} direct {fmt(D)}  [{t1 - t0:.1f} s]')
    print(f'   rule(B)={fmt(RB)}')
    print(f'   rule = direct: {RB == D}; mission form = direct: {RX == D}; #factors = 2^(n-1)-1: {nf == 2 ** (n - 1) - 1}; one Z: {D.get("Z") == 1}')
    print(f'   control no-pooling differs: {C_np != D}; control carries-at-m differs: {C_m != D}')
    if C_np != D:
        print(f'      no-pooling: {fmt(C_np)}')
    if C_m != D:
        print(f'      carries-at-m: {fmt(C_m)}')
    allok &= (RB == D and RX == D)
    sys.stdout.flush()
print('RESULT', 'PASS' if allok else 'FAIL')
