"""theoremF_check.py — machine check of §7 (Theorem F and its uses), written from the text of §5–§7.

Cold reader «Grepy el lector frío del cubo 3», 2026-10-05. Integers only (fits as exact (sum, count) pairs).

For every house H = (I, k, l, alpha), k <= KMAX, I ⊆ [0,k), 0 <= l < 2^k, alpha in ALPHAS:
  * builds R_H, J_H, x_H, c_H (§7.3), the real and integer antitonic fits;
  * runs the construction of V in the proof of Theorem 7.8 LITERALLY (steps 1-8), recursively on |I|,
    and checks (E) against the TRUE integer fit of x_H, (M), (G) for every arrow b ⊊ a;
  * checks (Cut), (Λ), Lemma 7.9 (integer separation), the step-1 formula ŷ_H = [max(X1,0), min(X2,0)],
    the step-1 claim intfit(x_{H'} + d_1) = ŷ' + d_1, the Theorem 7.10 claim intfit(x_H + δ) = ŷ_H + δ for the
    penalty shifts δ = -P J_H(D) and δ = +P J_H(I∖D) (P = 1..PMAX), and the i = 0 deletion (l = 2^k - 1);
  * STRADDLE detector: at every jump position of d_1 / δ, and at the cut b, is there a level set of the fit with
    equal values on both sides, and is its value an integer?  (This is the hidden hypothesis of Lemma 7.2(b).)
CONTROLS (must fail somewhere): V with c_F moved one below the interval; V := v' even when a central flat exists.
Usage: python3 engines/theoremF_check.py KMAX PMAX
"""
import sys
from collections import Counter

KMAX = int(sys.argv[1]); PMAX = int(sys.argv[2]); ALPHAS = (1, 2)


def s2(x): return bin(x).count("1")
def kappa(a, b): return s2(a) + s2(b) - s2(a + b)


def run_ones(x, u):
    r = 0
    while (x >> (u + r)) & 1:
        r += 1
    return r


def pava(x):
    st = []
    for v in x:
        st.append([v, 1])
        while len(st) >= 2 and st[-2][0] * st[-1][1] <= st[-1][0] * st[-2][1]:
            s, c = st.pop(); st[-1][0] += s; st[-1][1] += c
    return st


def realfit(x):
    """list of (S, p) per position (value S/p)."""
    out = []
    for S, p in pava(x):
        out += [(S, p)] * p
    return out


def intfit(x):
    out = []
    for S, p in pava(x):
        q, r = divmod(S, p)
        out += [q + 1] * r + [q] * (p - r)
    return out


def eqv(a, b): return a[0] * b[1] == b[0] * a[1]
def isint(a): return a[0] % a[1] == 0


def floor_(a): return a[0] // a[1]
def ceil_(a): return -((-a[0]) // a[1])


def int_separation(x):
    blocks = pava(x)
    for (S1, p1), (S2, p2) in zip(blocks, blocks[1:]):
        if not (S1 // p1 >= -((-S2) // p2)):
            return False
    return True


def straddles(fit, positions):
    """for each cut position b (0<b<len), is fit[b-1] == fit[b]?  returns (n_straddle, n_straddle_nonint)."""
    ns = nn = 0
    for b in positions:
        if 0 < b < len(fit) and eqv(fit[b - 1], fit[b]):
            ns += 1
            if not isint(fit[b]):
                nn += 1
    return ns, nn


def jumps(d):
    return [p for p in range(1, len(d)) if d[p] != d[p - 1]]


def house(I, k, l, alpha):
    s = len(I); N = 1 << s
    h = {}
    for j, t in enumerate(I):
        h[t] = (I[j + 1] if j + 1 < s else k) - t
    oD = [sum(1 << I[j] for j in range(s) if (p >> j) & 1) for p in range(N)]
    R = [sum(h[I[j]] - alpha * (1 << I[j]) for j in range(s) if (p >> j) & 1) - kappa(l, oD[p]) for p in range(N)]
    J = [1 if l + oD[p] >= (1 << k) else 0 for p in range(N)]
    x = [R[p] - R[N - 1 - p] for p in range(N)]

    def gamma(q):
        if q == 0:
            return 0
        jmin = (q & -q).bit_length() - 1
        mn = I[jmin]
        return sum(h[I[j]] for j in range(s) if not (q >> j) & 1 and I[j] > mn)

    def chat(a, b):
        return R[a] - R[b] + gamma(a & ~b)
    return dict(I=I, k=k, l=l, alpha=alpha, s=s, N=N, h=h, R=R, J=J, x=x, chat=chat, gamma=gamma)


stats = Counter()
memo = {}


def build(I, k, l, alpha):
    key = (I, k, l, alpha)
    if key in memo:
        return memo[key]
    H = house(I, k, l, alpha)
    N = H["N"]; x = H["x"]
    yt = intfit(x)  # TRUE integer fit
    H["yhat"] = yt
    if len(I) == 0:
        H["V"] = [0]; H["Vbad"] = [0]; H["Vbad2"] = [0]
        memo[key] = H
        return H
    c = I[-1]; Ip = I[:-1]; hh = k - c
    Hp = build(Ip, c, l % (1 << c), alpha)
    Np = Hp["N"]; Jp = Hp["J"]; Vp = Hp["V"]; yp = Hp["yhat"]
    T = (l >> c) & 1
    kap = min(run_ones(l, c), hh) if T == 1 else 1 + min(run_ones(l, c + 1), hh - 1)
    tau = hh - alpha * (1 << c) - (kap if T == 1 else 0)
    # Lemma 7.7 consistency: first half of x_H equals x_{H'} + d_1
    d1 = [-tau - (kap * Jp[p] if T == 1 else 0) + (kap * Jp[Np - 1 - p] if T == 0 else 0) for p in range(Np)]
    if [x[p] for p in range(Np)] != [Hp["x"][p] + d1[p] for p in range(Np)]:
        stats["FAIL Lemma 7.7 (first half of x_H != x_H' + d1)"] += 1
    X1 = [yp[p] + d1[p] for p in range(Np)]
    X2 = [-X1[Np - 1 - p] for p in range(Np)]
    # step-1 claim (integer part of Lemma 7.2(b))
    if intfit([Hp["x"][p] + d1[p] for p in range(Np)]) != X1:
        stats["FAIL step-1 claim intfit(x_H'+d1) == y'+d1"] += 1
    fp = realfit(Hp["x"])
    ns, nn = straddles(fp, jumps(d1))
    stats["step1 jumps examined"] += len(jumps(d1))
    stats["step1 straddles (any value)"] += ns
    stats["step1 straddles NON-INTEGER"] += nn
    # step-1 formula
    if yt != [max(v, 0) for v in X1] + [min(v, 0) for v in X2]:
        stats["FAIL step-1 formula yhat_H = [max(X1,0),min(X2,0)]"] += 1
    # inherited potential
    vp = [Vp[p] - (kap * Jp[p] if T == 1 else 0) for p in range(Np)] + \
         [tau + Vp[p] - (kap * Jp[p] if T == 0 else 0) for p in range(Np)]
    Vbad = None
    if X1[Np - 1] > 0:
        V = vp[:]
        Vbad = vp[:]  # control 1 not applicable: no flat
        Vbad2 = vp[:]
        stats["no central flat"] += 1
    else:
        stats["central flat"] += 1
        F1 = [p for p in range(Np) if X1[p] <= 0]
        f = F1[0]
        if F1 != list(range(f, Np)):
            stats["FAIL F1 not a final segment"] += 1
        c3 = vp[f]; c4 = vp[N - 1 - f]
        lo = c3; hi = c4
        if f > 0:
            pprev = f - 1; pstar = N - 1 - pprev
            lo = max(lo, vp[pstar]); hi = min(hi, vp[pprev])
        if lo > hi:
            stats["FAIL empty interval for c_F"] += 1
        cF = lo
        V = [cF if f <= p <= N - 1 - f else vp[p] for p in range(N)]
        Vbad = [cF - 1 if f <= p <= N - 1 - f else vp[p] for p in range(N)]   # control: below the interval
        Vbad2 = vp[:]                                                         # control: ignore the flat
    H["V"] = V
    for name, W in (("V", V), ("CONTROL c_F-1", Vbad), ("CONTROL v' (no flat fix)", Vbad2)):
        okE = all(W[p] - W[N - 1 - p] == yt[p] for p in range(N))
        okM = all(W[p] >= W[p + 1] for p in range(N - 1))
        okG = True
        chat = H["chat"]
        for a in range(N):
            b = a
            while True:
                b = (b - 1) & a
                if b == a:
                    break
                if W[a] - W[b] > chat(a, b):
                    okG = False
                    break
                if b == 0:
                    break
            if not okG:
                break
        if name == "V":
            if not okE: stats["FAIL (E)"] += 1
            if not okM: stats["FAIL (M)"] += 1
            if not okG: stats["FAIL (G)"] += 1
        else:
            if not (okE and okM and okG):
                stats["control detected (" + name + ")"] += 1
            elif W != V:
                stats["control NOT detected though V changed (" + name + ")"] += 1
    memo[key] = H
    return H


houses = 0
for k in range(0, KMAX + 1):
    for mask in range(1 << k):
        I = tuple(t for t in range(k) if (mask >> t) & 1)
        for l in range(1 << k):
            for alpha in ALPHAS:
                H = build(I, k, l, alpha)
                houses += 1
                N = H["N"]; x = H["x"]; yt = H["yhat"]; J = H["J"]
                fit = realfit(x)
                # (Cut)
                bs = [p for p in range(N) if J[p] == 1]
                if bs:
                    b = bs[0]
                    if b > 0 and realfit(x[:b]) + realfit(x[b:]) != fit:
                        # compare as values
                        if not all(eqv(u, v) for u, v in zip(realfit(x[:b]) + realfit(x[b:]), fit)):
                            stats["FAIL (Cut)"] += 1
                    ns, nn = straddles(fit, [b, N - b])
                    stats["cut-b straddles (any value)"] += ns
                    stats["cut-b straddles NON-INTEGER"] += nn
                # (Λ)
                if max(abs(v) for v in yt) > alpha * ((1 << k) - 1):
                    stats["FAIL (Lambda)"] += 1
                # Lemma 7.9 in the house
                if not int_separation(x):
                    stats["FAIL Lemma 7.9 house"] += 1
                if any(yt[p] < yt[p + 1] for p in range(N - 1)):
                    stats["FAIL integer fit not non-increasing (house)"] += 1
                # penalty cells (Theorem 7.10 (U2))
                for P in range(1, PMAX + 1):
                    for kind in ("row", "col"):
                        d = [-P * J[p] for p in range(N)] if kind == "row" else [P * J[N - 1 - p] for p in range(N)]
                        xd = [x[p] + d[p] for p in range(N)]
                        if intfit(xd) != [yt[p] + d[p] for p in range(N)]:
                            stats["FAIL Thm7.10 (U2) intfit(x+delta)==yhat+delta"] += 1
                        if not int_separation(xd):
                            stats["FAIL Lemma 7.9 cell"] += 1
                        ns, nn = straddles(fit, jumps(d))
                        stats["cell straddles NON-INTEGER"] += nn
                # i = 0 deletion
                if l == (1 << k) - 1 and N >= 2:
                    if intfit(x[1:]) != yt[1:]:
                        stats["FAIL i=0 deletion intfit(x[1:]) == yhat[1:]"] += 1
                    if not int_separation(x[1:]):
                        stats["FAIL Lemma 7.9 deletion"] += 1
                    ns, nn = straddles(fit, [1])
                    stats["deletion straddles NON-INTEGER"] += nn
print(f"houses checked: {houses} (k <= {KMAX}, alpha in {ALPHAS}), penalties P = 1..{PMAX}")
for key in sorted(stats):
    print(f"  {key}: {stats[key]}")
fails = sum(v for kk, v in stats.items() if kk.startswith("FAIL"))
print("TOTAL FAIL COUNT:", fails)
