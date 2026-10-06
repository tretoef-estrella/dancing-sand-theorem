# gate_cold5.py — cold reader 5 (Grepy Muchas Pilas), 5 October 2026.
# Written from the text of version 3 alone (§1.2, §5, §7.1, §7.3), before opening material/read_after/.
# Exact integer arithmetic only. Checks the sealed predictions S1–S14 of checks/SEALED.md.
import sys, random
from itertools import product

def s2(x): return bin(x).count('1')
def v2(x): return (x & -x).bit_length() - 1
def kap(a, b): return s2(a) + s2(b) - s2(a + b)
def phi(x): return x + v2(x)
def is_pow2(x): return x > 0 and (x & (x - 1)) == 0

# ---------- antitonic fit by pool-adjacent-violators, exact ----------
def pav(x):
    """non-increasing least-squares fit; returns list of blocks [sum, count]
    (adjacent blocks with equal means merged, so blocks = level sets)."""
    st = []
    for v in x:
        st.append([v, 1])
        while len(st) >= 2 and st[-2][0] * st[-1][1] <= st[-1][0] * st[-2][1]:
            s, c = st.pop()
            st[-1][0] += s; st[-1][1] += c
    return st

def per_pos(blocks):
    out = []
    for s, c in blocks:
        out.extend([(s, c)] * c)
    return out

def eq(a, b): return a[0] * b[1] == b[0] * a[1]
def gt(a, b): return a[0] * b[1] > b[0] * a[1]

def integral(blocks): return all(s % c == 0 for s, c in blocks)

def is_cut(x, b):
    full = per_pos(pav(x))
    cat = per_pos(pav(x[:b])) + per_pos(pav(x[b:]))
    return all(eq(p, q) for p, q in zip(full, cat))

def strict_at(x, b):
    f = per_pos(pav(x))
    return gt(f[b - 1], f[b])

# ---------- families and houses ----------
def family(lam):
    L = lam + 1
    k = L.bit_length() - 1
    I = [t for t in range(k) if (L >> t) & 1]
    return k, I

def hgaps(I, k):
    nxt = I[1:] + [k]
    return {t: nxt[j] - t for j, t in enumerate(I)}

def dancers(I):
    """o_D for D in o-order, indexed by p in [0, 2^s): bit j of p <-> t_j in D."""
    s = len(I)
    return [sum(1 << I[j] for j in range(s) if (p >> j) & 1) for p in range(1 << s)]

def hD_list(I, k):
    h = hgaps(I, k); s = len(I)
    return [sum(h[I[j]] for j in range(s) if (p >> j) & 1) for p in range(1 << s)]

def house(I, k, ell, alpha):
    o = dancers(I); hd = hD_list(I, k); N = len(o)
    R = [hd[p] - alpha * o[p] - kap(ell, o[p]) for p in range(N)]
    x = [R[p] - R[N - 1 - p] for p in range(N)]
    J = [1 if ell + o[p] >= (1 << k) else 0 for p in range(N)]
    return x, J

def boundary(J):
    for p, j in enumerate(J):
        if j: return p
    return None

# ---------- controls on the tools themselves ----------
def tool_controls():
    x = [3, 4, 3, 4]
    assert is_cut(x, 2) and not strict_at(x, 2), "tool control: (3,4,3,4) must be cut at 2, not strictly"
    assert not integral(pav(x)), "tool control: fit of (3,4,3,4) is 7/2"
    assert integral(pav([5, 1, 3])), "tool control: fit of (5,1,3) is (5,2,2)"
    # a strict cut that is a cut
    y = [5, 5, 0, -5]
    assert is_cut(y, 2) and strict_at(y, 2)
    print("TOOL-CONTROLS ok")

def main():
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    KPEN = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    LAMMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 255
    IMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 40
    tool_controls()
    # ===== houses =====
    nh = 0; bad_int = 0; nbound = 0; bad_cut = 0; bad_strict = 0
    npen = 0; bad_pen = 0; bad_pen_shift = 0
    ndel = 0; bad_del = 0
    c1_fire = 0; c1_tot = 0
    c3_fire = 0; c3_tot = 0
    zero_fit_I = []        # S11 witnesses (alpha=1, I nonempty, fit identically 0)
    s12_wit = None
    for k in range(1, KMAX + 1):
        for Imask in range(1 << k):
            I = [t for t in range(k) if (Imask >> t) & 1]
            for ell in range(1 << k):
                for alpha in (1, 2, 3):
                    nh += 1
                    x, J = house(I, k, ell, alpha)
                    N = len(x)
                    bl = pav(x)
                    if not integral(bl): bad_int += 1
                    if alpha == 1 and I:
                        if len(bl) == 1 and bl[0][0] == 0:
                            zero_fit_I.append((tuple(I), k, ell))
                        if k >= 3 and max(c for s, c in bl) >= (1 << (k - 1)) and s12_wit is None:
                            s12_wit = (tuple(I), k, ell, max(c for s, c in bl))
                    b = boundary(J)
                    if b is not None:
                        nbound += 1
                        for pos in sorted({b, N - b}):
                            if not is_cut(x, pos): bad_cut += 1
                            elif not strict_at(x, pos): bad_strict += 1
                        # C3: strictness one dancer after the boundary
                        if b + 1 < N:
                            c3_tot += 1
                            if not strict_at(x, b + 1): c3_fire += 1
                    # S2 penalties
                    if k <= KPEN and b is not None:
                        base = per_pos(bl)
                        for Pr, Pc in product(range(5), range(5)):
                            if Pr == 0 and Pc == 0: continue
                            npen += 1
                            sh = [-Pr * J[p] + Pc * J[N - 1 - p] for p in range(N)]
                            y = [x[p] + sh[p] for p in range(N)]
                            yb = pav(y)
                            if not integral(yb): bad_pen += 1
                            # Lemma 7.2(b): fit(x + shift) = fit(x) + shift
                            fy = per_pos(yb)
                            if not all(eq(fy[p], (base[p][0] + sh[p] * base[p][1], base[p][1])) for p in range(N)):
                                bad_pen_shift += 1
                    # deletion
                    if ell == (1 << k) - 1 and I:
                        ndel += 1
                        d = pav(x[1:])
                        fd = per_pos(d); fx = per_pos(bl)
                        if not integral(d) or not all(eq(fd[p], fx[p + 1]) for p in range(N - 1)):
                            bad_del += 1
                    # C1
                    if k <= KPEN:
                        c1_tot += 1
                        z = x[:]; z[0] += 1
                        if not integral(pav(z)): c1_fire += 1
    print(f"HOUSES k<={KMAX}: {nh} houses; non-integral fits: {bad_int}")
    print(f"BOUNDARIES: {nbound} houses with a boundary; cuts missing: {bad_cut}; cuts not strict: {bad_strict}")
    print(f"PENALTIES k<={KPEN}, (P_r,P_c) in [0,4]^2 minus (0,0): {npen} cells; non-integral: {bad_pen}; fit != fit(x_H)+shift: {bad_pen_shift}")
    print(f"DELETIONS: {ndel}; bad: {bad_del}")
    print(f"C1 (x_H + 1 at first dancer, k<={KPEN}): non-integral in {c1_fire} of {c1_tot}")
    print(f"C3 (strictness one dancer after the boundary): fails in {c3_fire} of {c3_tot}")
    print(f"S11 witnesses (alpha=1, I nonempty, fit = 0): {len(zero_fit_I)}; first: {zero_fit_I[:3]}")
    print(f"S12 witness: {s12_wit}")
    # ===== C2: random antisymmetric sequences =====
    rnd = random.Random(20261005)
    c2 = 0
    for _ in range(10000):
        half = [rnd.randint(-6, 6) for _ in range(4)]
        seq = half + [-v for v in reversed(half)]
        if not integral(pav(seq)): c2 += 1
    print(f"C2 (random antisymmetric length 8): non-integral fit in {c2} of 10000")
    # ===== real families, raw clocks of §1.2 =====
    ncell = 0; s4_bad = 0; s5_bad = 0; s5_bad_pen = 0; s6_bad = 0; s6_n = 0
    s10_hit = 0; s14_hit = 0; s13_hit = 0; s13_n = 0; nb_cells = 0
    c5_fire = 0; c5_tot = 0
    for lam in range(1, LAMMAX + 1):
        k, I = family(lam); K = 1 << k
        o = dancers(I); hd = hD_list(I, k); N = len(o)
        for i in range(0, IMAX + 1):
            ncell += 1
            u = []
            for p in range(N):
                if i == 0 and p == 0: continue
                xi = lam + 1 - 2 * o[p]
                assert xi > 0
                u.append(phi(xi) + kap(i + o[p] - 1, xi) + hd[p])
            ub = pav(u)
            if not integral(ub): s4_bad += 1
            # C5 control: perturb the first raw clock
            if i >= 1 and N >= 2:
                c5_tot += 1
                z = u[:]; z[0] += 1
                if not integral(pav(z)): c5_fire += 1
            if i >= 1:
                m = i - 1
                # §5 rulers directly
                def Rmu(mu, p): return hd[p] - o[p] - kap(mu, o[p])
                xd = [Rmu(m, p) - Rmu(m + K, N - 1 - p) for p in range(N)]
                cst = k + K + kap(m, K)
                if any(u[p] != cst + xd[p] for p in range(N)): s5_bad += 1
                # Lemma 7.5: penalty cell of the house (I, k, m mod K, 1)
                ell = m % K
                xH, J = house(I, k, ell, 1)
                def rk(mu): return v2((mu >> k) + 1)
                Pr, Pc = rk(m), rk(m + K)
                xp = [xH[p] - Pr * J[p] + Pc * J[N - 1 - p] for p in range(N)]
                if xp != xd: s5_bad_pen += 1
                # S6 head dyadic
                s6_n += 1
                head = ub[0][1]
                if not is_pow2(head): s6_bad += 1
                b = boundary(J)
                if b is not None:
                    nb_cells += 1
                    if head == b and not is_pow2(b): s10_hit += 1
                    if not is_pow2(b): s14_hit += 1
                    # S13 counterfactual: the jump one dancer late
                    if (Pr > 0 or Pc > 0) and b + 1 < N:
                        s13_n += 1
                        shl = [-Pr * (1 if p >= b + 1 else 0) + Pc * (1 if p < N - b + 1 else 0) for p in range(N)]
                        y = [xH[p] + shl[p] for p in range(N)]
                        if not is_pow2(pav(y)[0][1]): s13_hit += 1
            else:
                # i = 0: u_0(D) = k + K + x_{H#}(D), D != empty
                xH, J = house(I, k, K - 1, 1)
                if I and any(u[p - 1] != k + K + xH[p] for p in range(1, N)): s5_bad += 1
    print(f"REAL CELLS lam<={LAMMAX}, i<={IMAX}: {ncell} cells")
    print(f"S4 raw clocks of §1.2 with a non-integral level set: {s4_bad}")
    print(f"C5 (raw clocks + 1 at first dancer, i>=1): non-integral in {c5_fire} of {c5_tot}")
    print(f"S5 u != k+K+kappa(m,K)+x_D (§5 rulers), or u_0 != k+K+x_H#: {s5_bad}; §5 clocks != penalty cell of Lemma 7.5: {s5_bad_pen}")
    print(f"S6 non-dyadic heads: {s6_bad} of {s6_n}")
    print(f"cells with a boundary: {nb_cells}; S10 hits (head == pos(b), not a power of 2): {s10_hit}; S14 hits (pos(b) not a power of 2): {s14_hit}")
    print(f"S13 counterfactual (jump one dancer late) non-dyadic heads: {s13_hit} of {s13_n}")
    print("FIN-OK")

if __name__ == '__main__':
    main()
