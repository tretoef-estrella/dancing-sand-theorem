"""check_rule_internal.py — checks on the rule of §1.2 itself (no Smith form), and the §1.4 corollaries from it.

S6: equivalent form (Prop. 5.3 as printed in §1.2): u_i(D) == k + K + kappa(m,K) + x_D, lambda <= LMAX, 1 <= i <= IMAX
S7: Lemma 7.9 claim: integer antitonic fit is non-increasing, all (lambda, i) with lambda + 2i <= NMAX
TIE: does the «strictly decreasing» clause ever matter (PAVA merging equal means vs not)?
S8: all big clocks >= 1 (no hidden trivial factor), lambda + 2i <= NMAX
Cor 1.5, 1.6 (and the «in particular» forms), 1.7 for n <= NMAX, from the rule.
CONTROL: a deliberately wrong variant of each corollary formula must fail somewhere.
Usage: python3 engines/check_rule_internal.py LMAX IMAX NMAX
"""
import sys
from collections import Counter
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import rule
from rule import INF, phi, v2, kappa, family, dancers, raw_clocks, pooled_clocks, integer_antitonic_fit

LMAX, IMAX, NMAX = (int(a) for a in sys.argv[1:4])

# S6
bad6 = 0; tot6 = 0
for lam in range(1, LMAX + 1):
    k, I, h = family(lam)
    for i in range(1, IMAX + 1):
        u = raw_clocks(lam, i)
        for D, uD in zip(dancers(I), u):
            tot6 += 1
            if rule.equivalent_form_clock(lam, i, D) != uD:
                bad6 += 1
                if bad6 <= 5:
                    print("S6 MISMATCH", lam, i, D, uD, rule.equivalent_form_clock(lam, i, D))
print(f"S6 equivalent form: {tot6} (lambda,i,D) checked, {bad6} mismatches")


def fit_nonstrict(x):  # PAVA merging only on strict violation (ties NOT merged)
    st = []
    for v in x:
        st.append([v, 1])
        while len(st) >= 2 and st[-2][0] * st[-1][1] < st[-1][0] * st[-2][1]:
            s, c = st.pop(); st[-1][0] += s; st[-1][1] += c
    out = []
    for S, p in st:
        q, r = divmod(S, p); out += [q + 1] * r + [q] * (p - r)
    return out


bad7 = 0; tot7 = 0; ties = 0; bad8 = 0; pooled_cases = 0
for lam in range(1, NMAX + 1):
    for i in range(0, (NMAX - lam) // 2 + 1):
        y = pooled_clocks(lam, i)
        u = raw_clocks(lam, i)
        tot7 += 1
        if any(y[j] < y[j + 1] for j in range(len(y) - 1)):
            bad7 += 1
            if bad7 <= 5:
                print("S7 NOT NON-INCREASING", lam, i, u, y)
        body = u[1:] if i == 0 else u
        if integer_antitonic_fit(body) != fit_nonstrict(body):
            ties += 1
            if ties <= 5:
                print("TIE matters:", lam, i, body, integer_antitonic_fit(body), fit_nonstrict(body))
        if integer_antitonic_fit(body) != body:
            pooled_cases += 1
        if any(e < 1 for e in y):
            bad8 += 1
            if bad8 <= 5:
                print("S8 trivial clock", lam, i, y)
print(f"S7 monotone fit: {tot7} (lambda,i) with lambda+2i<={NMAX}, {bad7} violations; pooling acts in {pooled_cases}")
print(f"TIE clause matters in {ties} cases")
print(f"S8 big clocks >= 1: {bad8} violations")


def g(N):
    return max(phi(x) for x in range(1, N))


def top(gr, cnt):
    out = []
    for e in sorted((e for e in gr if e != INF), reverse=True):
        out += [e] * min(gr[e], cnt - len(out))
        if len(out) >= cnt:
            break
    return out[:cnt]


bad15 = bad16 = bad16p = bad17 = 0
ctrl15 = ctrl16 = 0
groups = {}
for n in range(1, NMAX + 1):
    gr = rule.syl2_plus_free(n)
    groups[n] = gr
    assert gr[INF] == 1
    if n >= 2:
        nf = sum(c for e, c in gr.items() if e != INF)
        an = 2 ** (n - 2) - 2 ** ((n - 2) // 2)
        if nf != 2 ** (n - 1) - 1 or gr[1] != an:
            bad15 += 1; print("Cor1.5 FAIL", n, nf, gr[1], an)
        if gr[1] != 2 ** (n - 2) - 2 ** ((n - 1) // 2):  # control: wrong floor
            ctrl15 += 1
    if n >= 4:
        c = top(gr, n + 1)
        G = g(n - 1)
        if n % 2 == 0:
            pred = [max(G, phi(n) - 1)] + [G] * n
        elif phi(n - 1) <= G:
            pred = [G] * (n + 1)
        else:
            pred = [phi(n - 1)] * (n - 1) + [max(G, phi(n - 1) - 2), G]
        if c != pred:
            bad16 += 1; print("Cor1.6 FAIL", n, c, pred)
        # control: c_n with phi(n-1)-1 instead of -2
        if n % 2 == 1 and phi(n - 1) > G:
            predw = [phi(n - 1)] * (n - 1) + [max(G, phi(n - 1) - 1), G]
            if c != predw:
                ctrl16 += 1
    if n >= 3:
        c = top(gr, n + 1 if n >= 4 else n)
        ok = (c[0] == max(g(n), v2(n) + n - 1) and all(x == g(n) for x in c[1:n - 1])
              and c[n - 1] == max(g(n - 1), v2(n - 1) + n - 3))
        if n >= 4:
            ok = ok and c[n] == g(n - 1)
        if not ok:
            bad16p += 1; print("Cor1.6 'in particular' FAIL", n, c)
e = 1
while 2 ** e <= NMAX:
    a, b = groups[2 ** e], groups[2 ** e - 1]
    pred = Counter({x: 2 * y for x, y in b.items() if x != INF})
    pred[2 ** e + e - 1] += 1
    pred[INF] = 1
    if a != pred:
        bad17 += 1; print("Cor1.7 FAIL e =", e)
    e += 1
print(f"Cor 1.5 (n=2..{NMAX}): {bad15} failures; control (wrong floor) failed at {ctrl15} n's")
print(f"Cor 1.6 (n=4..{NMAX}): {bad16} failures; control (c_n with -1) failed at {ctrl16} n's")
print(f"Cor 1.6 'in particular' (n=3..{NMAX}): {bad16p} failures")
print(f"Cor 1.7 (2^e <= {NMAX}): {bad17} failures")
