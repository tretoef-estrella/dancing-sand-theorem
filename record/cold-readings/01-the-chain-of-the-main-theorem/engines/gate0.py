# gate0.py — C-G0: my Z/2^64 Smith engine against PARI/GP matsnf (an independent implementation).
# Random integer matrices with mixed 2-adic valuations (some singular), and Laplacians of Q_n, n = 1..7.
import random, subprocess, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SCR = os.path.join(ROOT, 'scratch')
os.makedirs(SCR, exist_ok=True)


def v2(x):
    return (x & -x).bit_length() - 1


def mine_file(M):
    N = len(M)
    p = os.path.join(SCR, 'g0_mat.txt')
    with open(p, 'w') as f:
        f.write(f'{N}\n')
        for r in M:
            f.write(' '.join(map(str, r)) + '\n')
    out = subprocess.run([os.path.join(HERE, 'mysmith'), 'file', p], capture_output=True, text=True).stdout
    return parse(out)


def parse(out):
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


def pari(M):
    N = len(M)
    s = 'M=[' + ';'.join(','.join(map(str, r)) for r in M) + '];print(matsnf(M))'
    out = subprocess.run(['gp', '-q', '-f', '--default', 'parisizemax=200000000'], input=s, capture_output=True, text=True).stdout.strip()
    vals = [int(t) for t in out.strip('[]').replace(' ', '').split(',') if t != '']
    G = {}
    for d in vals:
        if d == 0:
            G['Z'] = G.get('Z', 0) + 1
        else:
            e = v2(abs(d))
            if e > 0:
                G[e] = G.get(e, 0) + 1
    # matsnf may return fewer entries than N? it returns N entries for square matrices
    assert len(vals) == N, (len(vals), N)
    return G


def lap(n):
    N = 1 << n
    return [[(n if x == y else (-1 if bin(x ^ y).count('1') == 1 else 0)) for y in range(N)] for x in range(N)]


random.seed(20261004)
ok = bad = 0
for trial in range(60):
    N = random.randint(4, 40)
    M = [[(random.randint(-9, 9) * (1 << random.choice([0, 0, 1, 2, 3, 5]))) for _ in range(N)] for _ in range(N)]
    if trial % 4 == 0:  # make it singular: last row = sum of two others
        M[-1] = [M[0][j] + 2 * M[1][j] for j in range(N)]
    if trial % 4 == 1:  # all entries even: shifts every exponent
        M = [[2 * x for x in r] for r in M]
    a, b = mine_file(M), pari(M)
    if a == b:
        ok += 1
    else:
        bad += 1
        print('MISMATCH random', trial, N, a, b)
print(f'C-G0a random matrices: {ok}/{ok + bad} agree')
ok2 = 0
for n in range(1, 8):
    out = subprocess.run([os.path.join(HERE, 'mysmith'), 'lap', str(n)], capture_output=True, text=True).stdout
    a = parse(out)
    b = pari(lap(n))
    print('n', n, 'mine', a, 'pari', b, 'AGREE' if a == b else 'MISMATCH')
    ok2 += (a == b)
print(f'C-G0b Laplacians n=1..7: {ok2}/7 agree')
# control: a deliberately wrong engine reading (drop one exponent) must be caught by the comparison
a = parse(subprocess.run([os.path.join(HERE, 'mysmith'), 'lap', '5'], capture_output=True, text=True).stdout)
b = pari(lap(5))
k0 = min(e for e in a if e != 'Z'); a[k0] -= 1
print('control (one factor removed) detected:', a != b)
print('RESULT', 'PASS' if bad == 0 and ok2 == 7 else 'FAIL')
