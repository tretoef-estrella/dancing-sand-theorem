# gate_houses_mine.py — Grepy el lector frío del cubo 4, 2026-10-05.
# My own check of Theorem 7.8 (Theorem F) of v2 with STRICT (Cut), of Lemma 7.9, and of the
# integer shifts used in Theorem 7.10 / Proposition 9.6, on every house H = (I, k, l, alpha)
# with 1 <= k <= KMAX, alpha <= AMAX. Written from the definitions of §5 and §7.3 only.
#
# Usage: python3 gate_houses_mine.py KMAX AMAX
import sys
from fractions import Fraction
from functools import lru_cache
from fitlib import fit_checked, int_fit, level_sets, is_cut, separation_ok
import fitfast as ff

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
AMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3
KMIN = int(sys.argv[3]) if len(sys.argv) > 3 else 1   # houses with KMIN <= k <= KMAX are checked
AMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 1
PMAX = 4


def s2(a):
    return bin(a).count("1")


def kap(a, b):
    return s2(a) + s2(b) - s2(a + b)


def bits(m):
    return [t for t in range(m.bit_length()) if (m >> t) & 1]


def dancers(I):
    """subsets of I as masks, in o-order (o_D = mask)."""
    out = [0]
    for t in bits(I):
        out = out + [d | (1 << t) for d in out]
    return sorted(out)


def hvals(I, k):
    bs = bits(I) + [k]
    return {t: bs[j + 1] - t for j, t in enumerate(bs[:-1])}


def R(I, k, l, a, E, h):
    return sum(h[t] - a * (1 << t) for t in bits(E)) - kap(l, E)


def J(I, k, l, E):
    return 1 if l + E >= (1 << k) else 0


def gold(I, h, Dl):
    if Dl == 0:
        return 0
    mn = bits(Dl)[0]
    return sum(h[u] for u in bits(I) if not (Dl >> u) & 1 and u > mn)


def run_ones(l, u):
    r = 0
    while (l >> (u + r)) & 1:
        r += 1
    return r


def _house(I, k, l, a):
    """Data of a house from the definitions: dancers, x_H, yhat_H, J_H."""
    ds = dancers(I)
    h = hvals(I, k)
    Rv = {d: R(I, k, l, a, d, h) for d in ds}
    x = [Rv[d] - Rv[I ^ d] for d in ds]
    Jv = {d: J(I, k, l, d) for d in ds}
    return ds, h, Rv, x, tuple(int_fit(x)), Jv


_house_cached = lru_cache(maxsize=None)(_house)


def house(I, k, l, a):
    return _house(I, k, l, a) if k == KMAX else _house_cached(I, k, l, a)


STATS = {}


def bump(key, n=1):
    STATS[key] = STATS.get(key, 0) + n


def _build_V(I, k, l, a, mode):
    """The function V of the proof of Theorem 7.8 (steps 1-8), recursively.
    mode: 'lo' / 'hi' = admissible ends of the interval of step 7;
          controls: 'hi+1', 'lo-1', 'vI' (c_F := v'(I'))."""
    ds, h, Rv, x, yh, Jv = house(I, k, l, a)
    if I == 0:
        return ((0, 0),)
    c = I.bit_length() - 1
    Ip = I ^ (1 << c)
    kp, lp = c, l % (1 << c)
    dsp, hp, Rvp, xp, yhp, Jp = house(Ip, kp, lp, a)
    Vp = dict(build_V(Ip, kp, lp, a, mode))
    T = (l >> c) & 1
    hh = k - c
    if T:
        kp_ = min(run_ones(l, c), hh)
    else:
        kp_ = 1 + min(run_ones(l, c + 1), hh - 1)
    sat = 1 if kp_ == hh else 0
    tau = hh - a * (1 << c) - (kp_ if T else 0)
    # step 1 objects
    d1 = {D: -tau - (kp_ * Jp[D] if T else 0) + (0 if T else kp_ * Jp[Ip ^ D]) for D in dsp}
    pos = {D: j for j, D in enumerate(dsp)}
    X1 = {D: yhp[pos[D]] + d1[D] for D in dsp}
    vq = {}
    for D in dsp:
        vq[D] = Vp[D] - (kp_ * Jp[D] if T else 0)
        vq[D | (1 << c)] = tau + Vp[D] - (0 if T else kp_ * Jp[D])
    V = dict(vq)
    if X1[Ip] <= 0:
        F1 = [D for D in dsp if X1[D] <= 0]
        # claims of step 7: F1 is a final segment of the first half containing I'
        idx = [pos[D] for D in F1]
        if not (idx == list(range(idx[0], len(dsp))) and Ip in F1):
            bump("FAIL_F1_not_final_segment")
        f = F1[0]
        c3, c4 = vq[f], vq[I ^ f]
        if c3 != max(vq[D] for D in F1):
            bump("FAIL_c3_not_max")
        if c4 != min(vq[I ^ D] for D in F1):
            bump("FAIL_c4_not_min")
        if pos[f] > 0:
            p = dsp[pos[f] - 1]
            ps = I ^ p
            if not vq[ps] < vq[p]:
                bump("FAIL_vps_lt_vp")
            lo, hi = max(c3, vq[ps]), min(c4, vq[p])
        else:
            lo, hi = c3, c4
        if lo > hi:
            bump("FAIL_interval_empty")
        cF = {"lo": lo, "hi": hi, "hi+1": hi + 1, "lo-1": lo - 1, "vI": vq[Ip]}[mode]
        for D in F1:
            V[D] = cF
            V[I ^ D] = cF
    return tuple(sorted(V.items()))


build_V = lru_cache(maxsize=None)(_build_V)   # cached for the children; the top level is not


def check_house(I, k, l, a, mode):
    """Checks (E), (M), (G), (Lambda) for V built with `mode`. Returns list of failed claims."""
    ds, h, Rv, x, yh, Jv = house(I, k, l, a)
    V = dict(_build_V(I, k, l, a, mode) if k == KMAX else build_V(I, k, l, a, mode))
    bad = []
    N = len(ds)
    # (E)
    for j, D in enumerate(ds):
        if V[D] - V[I ^ D] != yh[j]:
            bad.append("E")
            break
    # (M)
    for j in range(N - 1):
        if V[ds[j]] < V[ds[j + 1]]:
            bad.append("M")
            break
    # (G)
    gfail = False
    for A in ds:
        sub = (A - 1) & A
        while True:
            B = sub
            if B != A:
                cost = Rv[A] - Rv[B] + gold(I, h, A ^ B)
                if V[A] - V[B] > cost:
                    gfail = True
                    break
            if sub == 0:
                break
            sub = (sub - 1) & A
        if gfail:
            break
    if gfail:
        bad.append("G")
    # (Lambda)
    if max(abs(v) for v in yh) > a * ((1 << k) - 1):
        bad.append("Lambda")
    return bad


def fast_cuts(x):
    """All cuts of x by my criterion (b inside a level set L of value c is a cut iff the sum of
    x - c over L before b is exactly 0). Cross-validated against the definition below."""
    z = fit_checked(x)
    cuts, nonstrict = [], []
    for s, p in level_sets(z):
        acc = Fraction(0)
        for j in range(s, s + p):
            if j > s and acc == 0:
                cuts.append(j)
                nonstrict.append(j)
            acc += Fraction(x[j]) - z[j]
        if s + p < len(x):
            cuts.append(s + p)
    return sorted(cuts), nonstrict


def main():
    nh = 0
    crossval = 0
    for k in range(KMIN, KMAX + 1):
        for a in range(AMIN, AMAX + 1):
            for I in range(1 << k):
                for l in range(1 << k):
                    nh += 1
                    ds, h, Rv, x, yh, Jv = house(I, k, l, a)
                    N = len(ds)
                    z = fit_checked(x)
                    blx = ff.blocks(x)
                    if ff.levels(blx) != level_sets(z) or ff.int_fit_bl(blx) != list(yh) \
                            or ff.separation_bl(blx) != separation_ok(x):
                        bump("FAIL_fitfast_vs_fitlib")
                    bump("fitfast_crossvalidated")
                    # ---- Theorem 7.8 with admissible prices
                    for mode in ("lo", "hi"):
                        for f in check_house(I, k, l, a, mode):
                            bump(f"FAIL_{f}_{mode}")
                    # ---- controls: wrong prices
                    for mode in ("hi+1", "lo-1", "vI"):
                        if check_house(I, k, l, a, mode):
                            bump(f"control_price_{mode}_fires")
                    # ---- step 1 / Lemma 7.7 / Lemma 7.3 (for I != 0)
                    if I:
                        c = I.bit_length() - 1
                        Ip = I ^ (1 << c)
                        dsp, hp, Rvp, xp, yhp, Jp = house(Ip, c, l % (1 << c), a)
                        first = x[:N // 2]
                        dd = [first[j] - xp[j] for j in range(N // 2)]
                        # Lemma 7.7: the formula of d1 from the window data of W_c
                        T = (l >> c) & 1
                        hh = k - c
                        kk = min(run_ones(l, c), hh) if T else 1 + min(run_ones(l, c + 1), hh - 1)
                        tau = hh - a * (1 << c) - (kk if T else 0)
                        d1f = [-tau - (kk * Jp[D] if T else 0) + (0 if T else kk * Jp[Ip ^ D]) for D in dsp]
                        if dd != d1f:
                            bump("FAIL_lemma77_d1")
                        second = x[N // 2:]
                        if second != [-first[N // 2 - 1 - j] for j in range(N // 2)]:
                            bump("FAIL_antisymmetry")
                        sat = 1 if kk == hh else 0
                        case = ("a" if any(Jp.values()) else "b") if (T and sat) else ("c" if (sat and any(Jp.values())) else "d")
                        bump("case_" + case)
                        zp = fit_checked(xp)
                        if fit_checked(first) != [zp[j] + dd[j] for j in range(N // 2)]:
                            bump("FAIL_step1_real")
                        if level_sets(fit_checked(first)) != level_sets(zp):
                            bump("FAIL_step1_levels")
                        X1 = int_fit(first)
                        if X1 != [yhp[j] + dd[j] for j in range(N // 2)]:
                            bump("FAIL_step1_int")
                        X2 = [-X1[N // 2 - 1 - j] for j in range(N // 2)]
                        glued = [max(v, 0) for v in X1] + [min(v, 0) for v in X2]
                        if list(yh) != glued:
                            bump("FAIL_lemma73_int")
                        # d1 non-increasing, integer
                        if any(dd[j] < dd[j + 1] for j in range(len(dd) - 1)):
                            bump("FAIL_d1_not_nonincreasing")
                    # ---- (Cut), strict, by the definition
                    cuts, nonstrict = fast_cuts(x)
                    if crossval < 3000:
                        crossval += 1
                        direct = [b for b in range(1, N) if is_cut(x, b)]
                        if direct != cuts:
                            bump("FAIL_fastcuts_crossval")
                        bump("crossval_done")
                    bump("nonstrict_cuts_all_positions", len(nonstrict))
                    if nonstrict:
                        bump("houses_with_a_nonstrict_cut")
                    Js = [Jv[D] for D in ds]
                    if any(Js):
                        bump("boundaries")
                        pb = Js.index(1)
                        if pb == 0:
                            bump("FAIL_b_is_empty")
                        for q in sorted({pb, N - pb}):
                            if not is_cut(x, q):
                                bump("FAIL_cut")
                            if not z[q - 1] > z[q]:
                                bump("FAIL_strict")
                        # control: the same claim one position later
                        q = pb + 1
                        if q < N and not (is_cut(x, q) and z[q - 1] > z[q]):
                            bump("control_cut_strict_at_b+1_fires")
                        if q < N:
                            bump("control_cut_strict_at_b+1_tried")
                        # ---- penalty shifts (Theorem 7.10, Lemma 7.9, Prop 9.6)
                        jr = Js
                        jc = [Jv[I ^ D] for D in ds]
                        for Pr in range(PMAX + 1):
                            for Pc in range(PMAX + 1):
                                if Pr == Pc == 0:
                                    continue
                                d = [-Pr * jr[j] + Pc * jc[j] for j in range(N)]
                                xs = [x[j] + d[j] for j in range(N)]
                                bump("shifts")
                                bls = ff.blocks(xs)
                                yi = ff.int_fit_bl(bls)
                                if yi != [yh[j] + d[j] for j in range(N)]:
                                    bump("FAIL_shift_int")
                                if ff.levels(bls) != ff.levels(blx):
                                    bump("FAIL_shift_levels")
                                if not ff.separation_bl(bls):
                                    bump("FAIL_shift_separation")
                                if any(yi[j] < yi[j + 1] for j in range(N - 1)):
                                    bump("FAIL_shift_intfit_not_nonincreasing")
                                if (Pr, Pc) in ((1, 0), (0, 1), (4, 4)):
                                    # a sample cross-validated with the Fraction engine
                                    if int_fit(xs) != yi:
                                        bump("FAIL_fitfast_vs_fitlib_shift")
                                # control: same shift moved one position later
                                if pb + 1 < N:
                                    jr2 = [1 if j >= pb + 1 else 0 for j in range(N)]
                                    jc2 = [jr2[N - 1 - j] for j in range(N)]
                                    d2 = [-Pr * jr2[j] + Pc * jc2[j] for j in range(N)]
                                    xs2 = [x[j] + d2[j] for j in range(N)]
                                    bump("control_shift_tried")
                                    if ff.int_fit_bl(ff.blocks(xs2)) != [yh[j] + d2[j] for j in range(N)]:
                                        bump("control_shift_fires")
                    else:
                        bump("houses_J_zero")
                    # ---- Lemma 7.9 on the house itself
                    if not separation_ok(x):
                        bump("FAIL_separation_house")
                    # ---- deletion at l = 2^k - 1
                    if l == (1 << k) - 1 and I:
                        bump("deletions")
                        if not z[0] > z[1]:
                            bump("FAIL_empty_not_alone")
                        xr = x[1:]
                        if fit_checked(xr) != z[1:]:
                            bump("FAIL_deletion_real")
                        if int_fit(xr) != list(yh[1:]):
                            bump("FAIL_deletion_int")
                        if not separation_ok(xr):
                            bump("FAIL_deletion_separation")
        print(f"k <= {k} done, houses so far {nh}", flush=True)
    print("houses", nh)
    fails = {k_: v for k_, v in STATS.items() if k_.startswith("FAIL")}
    for k_ in sorted(STATS):
        print(f"  {k_} = {STATS[k_]}")
    print("RESULT:", "0 failures" if not fails else f"FAILURES {fails}")


main()
