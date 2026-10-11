# Integrality (Lemma 7.9) and the floor of every cell (Theorem 7.10, house form) (§7.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §7.5: Lemma 7.9 and the inequality part of Theorem 7.10 («`T(r) ≥ Y(r)` for every `r`»), stated for houses and penalty cells. The matrices `M^{(α)}(λ, i)` themselves, and the identification of their Smith exponents, come with Theorem D in a later piece; nothing here mentions a matrix.

This file reuses, without changing them:
- piece C1 (`RequestProject/AntitonicFit/`): `fit`, `ifit`, `toR`, `IsStrictCut`, Lemma 7.2 (in the forms `lemma_7_2_b3_b2`, `lemma_7_2_b2`), Lemma 7.3, consequence (L), and the other lemmas there;
- piece C2 (`RequestProject/SmithBounds/`): `NonIncrOn`, `tailSum`, `IsRMatching`, `theorem_U` (Theorem 7.4);
- piece C6 (`RequestProject/Houses/`): `Houses.JH`, `Houses.xH`, `Houses.cHatH`, `Houses.d1`, Lemmas A0, C;
- piece C7 (`RequestProject/TheoremF/`): `dancer`, `xHseq`, `JHseq`, `dWalk`, Lemma 0, Lemma 0f, Theorems F0, F1;
- piece C8 (`RequestProject/Potential/`): `yhat`, `cHat`, `IsArrow`, `IsPotential`, `theorem_F`.

## Setting

A **house** is `H = (I, k, ℓ, α)` with `I ⊆ {0, …, k − 1}`, `ℓ < 2^k`, `α ∈ ℤ`, `α ≥ 1`; `N := 2^{|I|}`; positions `p < N` index the dancers `dancer_I(p)`. Write `x_H`, `J_H`, `ŷ_H = ifit_N(x_H)` as in C7–C8.

For integers `P_r, P_c ≥ 0` (natural numbers) the **penalty cell** `Cell(H; P_r, P_c)` has, for positions `p, q < N`,
- the **cell clocks** `z(p) := x_H(p) − P_r J_H(p) + P_c J_H(N − 1 − p)`;
- the **cell costs** `cost(p, q) := ĉ_H(p, q) − P_r J_H(p) + P_c J_H(q)`.
The **cell arrows** are the pairs `p, q < N` with `dancer_I(q) ⊆ dancer_I(p)` (loops `q = p` included).

## Part A — Lemma 7.9 (integrality)

**Lemma 7.9.** For every house `H`:
- (I1) for every `p < N`, `fit_N(x_H)(p) = ŷ_H(p)` (as reals); in particular the real fit of `x_H` takes integer values, and `ŷ_H` is non-increasing on `[0, N)`;
- (I2) for all `P_r, P_c ∈ ℕ`, with `z` the cell clocks: for every `p < N`, `ifit_N(z)(p) = ŷ_H(p) − P_r J_H(p) + P_c J_H(N − 1 − p)` and `fit_N(z)(p) = ifit_N(z)(p)` (as reals); so `ifit_N(z)` is non-increasing on `[0, N)`;
- (I3) if `ℓ = 2^k − 1` and `I ≠ ∅`: `J_H(p) = [p ≠ 0]` for `p < N`; `x_H` has a strict cut at `1`; and the sequence `x^♯(j) := x_H(j + 1)` of length `N − 1` has `fit_{N−1}(x^♯)(j) = fit_N(x_H)(j + 1)` and `ifit_{N−1}(x^♯)(j) = ŷ_H(j + 1)` for `j < N − 1` (deleting the first dancer restricts the fit), and these are integers.

*Proof (from the paper).* (I1) by induction on `|I|`. For `I = ∅` the sequence is `(0)`. Let `I ≠ ∅`, with `H'`, `d = dWalk` as in C7. By C7 (W2), the real fit of the first half `x' + d` is `fit(x') + d`, integral by induction (and equal to `ifit(x') + d`); by Lemma 7.3 (C7, (W3)) `fit_N(x_H) = [max(Z_1, 0), min(mirror(Z_1), 0)]` with `Z_1 = fit(x') + d`, integral, and equal to the integer fit by (W3) for `ifit`. On a level set of integral value `v` with `P` positions and sum `S`, `S = P v` (consequence (L)), so `S mod P = 0` and `ifit = v` there. Monotonicity: the fit is non-increasing. (I2): the shift `δ(p) := −P_r J_H(p) + P_c J_H(N − 1 − p)` is integer and non-increasing (`J_H` is non-decreasing, C7), and it changes only at the first position `b` with `J_H(b) = 1` and at `N − b` (Lemma 0f: `J_H(0) = 0`); these are strict cuts of `x_H` (Theorem F1 of C7). So Lemma 7.2(b) (C1, `lemma_7_2_b3_b2`) gives `ifit(x_H + δ) = ifit(x_H) + δ` and the level sets of `fit(x_H + δ)` are those of `fit(x_H)`; then `fit(x_H + δ) = fit(x_H) + δ` is integral and equals the integer fit as in (I1). (I3): `ℓ + o_D ≥ 2^k` iff `o_D ≥ 1` iff `D ≠ ∅`, i.e. `p ≠ 0` (Lemma 0b–0c). So `b = 1` and the cut at `1` is strict (Theorem F1); a cut at `1` means `fit(x_H) = [fit(x_H(0)), fit(x^♯)]`, i.e. `fit_{N−1}(x^♯)(j) = fit_N(x_H)(j + 1)`, and the level sets of `x^♯` are those of `x_H` shifted, so the integer fits agree too. ∎

## Part B — the floor of a cell (Theorem 7.10, case `i ≥ 1`, house form)

**Theorem B.** Let `H` be a house, `P_r, P_c ∈ ℕ`, and `V` a potential for `H` (C8; one exists by `Potential.theorem_F`). Put `v(p) := V(p) − P_r J_H(p)` and `w(p) := V(p) − P_c J_H(p)`. Then:
- (U1) `v` and `w` are non-increasing on `[0, N)`;
- (U2) for every `p < N`: `v(p) − w(N − 1 − p) = ifit_N(z)(p)` (the integer fit of the cell clocks);
- (U3) for every cell arrow `p, q < N`, `dancer_I(q) ⊆ dancer_I(p)`: `v(p) − w(q) ≤ cost(p, q)`, with equality when `q = p`.
Consequently (Theorem 7.4, `SmithBounds.theorem_U`, with everything cast to `ℝ`): for every `r` and every `r`-matching `(Rows, β)` of the cell arrows on `[0, N)`, `tailSum N r (ifit_N(z)) ≤ Σ_{a ∈ Rows} cost(a, β(a))`; that is, `T(r) ≥ Y(r)`.

*Proof (from the paper).* (U1): `V` is non-increasing (M) and `J_H` non-decreasing. (U2): `v(p) − w(N − 1 − p) = V(p) − V(N − 1 − p) − P_r J_H(p) + P_c J_H(N − 1 − p) = ŷ_H(p) + δ(p)` by (E), which is `ifit_N(z)(p)` by (I2). (U3): `v(p) − w(q) − cost(p, q) = V(p) − V(q) − ĉ_H(p, q)`, which is `≤ 0` by (G) when `dancer_I(q) ⊊ dancer_I(p)`, and `0` on loops (`ĉ_H(p, p) = 0`: `R_H(a) − R_H(a) + γ(∅)` and `γ(∅) = 0`). ∎

## Part C — the shift `0` (Theorem 7.10, case `i = 0`, house form)

**Theorem C.** Let `H = (I, k, 2^k − 1, α)` be a house with `I ≠ ∅` and `V` a potential for `H`. Index the dancers `D ≠ ∅` by `j ↦ dancer_I(j + 1)` (rows) and the dancers `D ≠ I` by `j ↦ dancer_I(j)` (columns), `j < N − 1`, and put `ŷ^♯(j) := ifit_{N−1}(x^♯)(j)`, `cost^♯(a, b) := ĉ_H(a + 1, b)` for `a, b < N − 1`, with arrows `dancer_I(b) ⊆ dancer_I(a + 1)`. Then `v(j) := V(j + 1)` and `w(j) := V(j)` satisfy:
- (U1) `v`, `w` non-increasing on `[0, N − 1)`;
- (U2) `v(j) − w(N − 2 − j) = ŷ^♯(j)` for `j < N − 1`;
- (U3) `v(a) − w(b) ≤ cost^♯(a, b)` for every arrow, `a, b < N − 1`.
Consequently, by `SmithBounds.theorem_U`, every `r`-matching of these arrows on `[0, N − 1)` costs at least `tailSum (N − 1) r ŷ^♯`.

*Proof (from the paper).* (U1) from (M). (U2): `V(j + 1) − V(N − 2 − j) = V(j + 1) − V(N − 1 − (j + 1)) = ŷ_H(j + 1) = ŷ^♯(j)` by (E) and (I3). (U3): if `dancer_I(b) ⊊ dancer_I(a + 1)`, by (G); if they are equal, `b = a + 1` and both sides are `0`. ∎

## Checks before formalization

`lean/chkC9.py` (logs `logs/chkC9.log`, `logs/chkC9_k6.log`): exhaustive for every `k ≤ 5`, every `I ⊆ {0, …, k − 1}`, every `ℓ < 2^k`, `α ∈ {1, 2, 3}`, `P_r, P_c ≤ 4` (and `k ≤ 6` with `P_r, P_c ≤ 2`), with `V` built by C8's construction; exact rational arithmetic for the fits. It checks (I1)–(I3), (U1)–(U3) of Theorems B and C, and, for `N ≤ 4`, `P_r, P_c ≤ 1`, the conclusion `min cost ≥ Y(r)` by enumerating every `r`-matching. Controls, each of which must fail somewhere: (I1) for `x_H` with `1` added at its first dancer (not a house); (I2) with the shift moved one dancer late; (U3) with `w := V` (no column penalty); (I3) with `ℓ = 2^k − 2`.
