# The unique golden matching (Theorem O) and the natural minor (Corollary 6.3)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §6.2: Theorem 6.2 (Theorem O) and Corollary 6.3. Corollary 6.3 is stated here under an explicit hypothesis (H) on the valuations of the entries; in the paper (H) is Proposition 5.2 combined with Theorem D, which is a later piece. This file is self-contained, except that it reuses definitions of the previous pieces already formalized in this project: `Rulers.oE`, `Rulers.kappa`, `Rulers.h`, `Rulers.gamma`, `Rulers.ruler` (piece C3, `RequestProject/Rulers/`), and `SmithBounds.corollary_B'` may be used in the proof (piece C2, `RequestProject/SmithBounds/`).

## Part A — Theorem O in binary form

Fix `s ≥ 0` and put `N := 2^s`. For `p, g ∈ {0, …, N − 1}`, `g` is a **golden image** of `p` if `g = p`, or if there is `j < s` such that the bits `j, j+1, …, s − 1` of `p` are all equal to `1` (that is, `⌊p / 2^j⌋ = 2^{s−j} − 1`) and `g = p mod 2^j` (the block of top bits is cleared).

**Theorem A (Theorem O, binary form).** For every `s ≥ 0` and every `0 ≤ r ≤ N`, there is exactly one bijection `β : {N − r, …, N − 1} → {0, …, r − 1}` such that `β(p)` is a golden image of `p` for every `p`.

*Proof (from the paper).* Induction on `s`; `s = 0` is trivial (`N = 1`, `r ∈ {0, 1}`; for `r = 1` the only map sends `0 ↦ 0`, a loop). Let `s ≥ 1`, `N = 2^s`.
- `r ≤ N/2`: every row `p ≥ N − r ≥ N/2` has top bit `1`, every column `< r ≤ N/2` has top bit `0`. A golden image with top bit `0` of a `p` with top bit `1` is obtained by clearing a block that contains the top bit; write `p = N/2 + p'`. Then `g` is a golden image of `p` with `g < N/2` if and only if either `g = p'` (the block is exactly the top bit), or `g` is a golden image of `p'` in `{0, …, N/2 − 1}` with `g ≠ p'` (the block is longer, so the bits of `p'` cleared are all `1`). In other words, if and only if `g` is a golden image of `p'` at size `s − 1`. So the bijections for `(s, r)` are those for `(s − 1, r)` composed with `p ↦ p − N/2`, and there is exactly one.
- `r = N/2 + q` with `0 < q ≤ N/2`: the columns `N/2, …, N/2 + q − 1` have top bit `1`; a golden image of `p` with top bit `1` is `p` itself (clearing a block always clears the top bit). So these columns are reached only by loops; they are rows (they lie in `{N − r, …}` since `N − r = N/2 − q`), so they are matched with themselves. The rows `N/2 − q, …, N/2 − 1` have top bit `0`, so their only golden image is themselves; they are columns (they are `< r`), so they are matched with themselves. The remaining rows `N/2 + q, …, N − 1` must go to the remaining columns `0, …, N/2 − q − 1`, which is the problem `(s, N/2 − q)` of the first case, with exactly one solution. ∎

## Part B — Theorem O for dancers

**Setting.** Fix `k ≥ 0` and a finite set `I ⊆ {0, …, k − 1}`. The **dancers** are the subsets `D ⊆ I`; there are `N := 2^{|I|}` of them. Order them by `o_D := Σ_{t∈D} 2^t` (`Rulers.oE`); this map is injective on the subsets of `I`. The **rank** of `D` is `rank(D) := #{D' ⊆ I : o_{D'} < o_D}`, so the ranks are `0, …, N − 1`. For `0 ≤ r ≤ N` put
- `L_r := {D ⊆ I : rank(D) ≥ N − r}` (the last `r` dancers),
- `F_r := {D ⊆ I : rank(D) < r}` (the first `r` dancers).

An arrow `a → b` between dancers is **golden** if `b ⊆ a` and `γ(a ∖ b) = 0`, where `γ` is the gold of piece C3 (`Rulers.gamma k I`). (By Lemma 5.1(b) of C3 this means `b = a` or `b = a ∖ T` for a tail `T = {t ∈ I : t ≥ t₀}` of `I` contained in `a`.)

**Theorem B (Theorem O).** For every `k`, every `I ⊆ {0, …, k−1}` and every `0 ≤ r ≤ N`, there is exactly one bijection `β : L_r → F_r` all of whose arrows `D → β(D)` are golden.

*Proof (from the paper).* Let `t_1 < ⋯ < t_s` be the elements of `I` and identify a dancer `D` with `p(D) := Σ_j [t_j ∈ D] 2^{j−1} ∈ {0, …, 2^s − 1}`; `p` is a bijection from the dancers onto `{0, …, N − 1}`, and `o_D < o_{D'}` if and only if `p(D) < p(D')`, so `p(D) = rank(D)`. A tail of `I` contained in `D` corresponds to a block of top bits of `p(D)` that are all equal to `1`, and removing it clears that block. So the golden arrows `D → D'` are exactly the pairs with `p(D')` a golden image of `p(D)` in the sense of Part A, and Theorem B is Theorem A transported by `p`. ∎

## Part C — the complement and the cost of a bijection

Keep the setting of Part B.

**Lemma C1 (the complement reverses the order).** For dancers `D, D'`: `o_{I∖D} = o_I − o_D`; hence `o_D < o_{D'}` if and only if `o_{I∖D'} < o_{I∖D}`, `rank(I ∖ D) = N − 1 − rank(D)`, and `D ↦ I ∖ D` is a bijection from `L_r` onto `F_r`.

**Lemma C2 (cost of a bijection).** Fix an integer `α`, `μ ≥ 0` and `K := 2^k`. For dancers `a, b` put the **normalized cost**
  `ĉ(a, b) := R_μ(a) − R_{μ+K}(b) + γ(a ∖ b)`
(with `R_μ := Rulers.ruler k I α μ`), and for a dancer `D` put `x_D := R_μ(D) − R_{μ+K}(I ∖ D)`. Then for every bijection `β : L_r → F_r` (no support condition),
  `Σ_{D∈L_r} ĉ(D, β(D)) = Σ_{D∈L_r} x_D + Σ_{D∈L_r} γ(D ∖ β(D))`.

*Proof.* `Σ_D R_{μ+K}(β(D)) = Σ_{E∈F_r} R_{μ+K}(E) = Σ_{D∈L_r} R_{μ+K}(I ∖ D)`, by Lemma C1. ∎

## Part D — Corollary 6.3 (the natural minor), under the valuation hypothesis

Keep the setting of Parts B and C, with `α`, `μ`, `K`, `ĉ` and `x_D` as in Lemma C2, and fix an integer `C`. Let `M` be an integer matrix indexed by the dancers (a function from pairs of subsets of `I` to `ℤ`) such that

- (S) `M(a, b) = 0` unless `b ⊆ a`;
- (H) for every pair `b ⊆ a ⊆ I` there is `n ∈ ℕ` with `n = C + ĉ(a, b)`, `2^n ∣ M(a, b)` and `2^{n+1} ∤ M(a, b)` (in particular `C + ĉ(a, b) ≥ 0`).

For `0 ≤ r ≤ N`, let `M[L_r, F_r]` be the `r × r` submatrix with rows `L_r` and columns `F_r`, listed in any fixed orders `e : Fin r ≃ L_r`, `f : Fin r ≃ F_r`, and put `U(r) := Σ_{D∈L_r} x_D`.

**Corollary D (Corollary 6.3).** There is `n ∈ ℕ` with `n = r·C + U(r)`, `2^n ∣ det M[L_r, F_r]` and `2^{n+1} ∤ det M[L_r, F_r]`. In particular `det M[L_r, F_r] ≠ 0`.

*Proof (from the paper).* The determinant is a signed sum over the bijections `β : L_r → F_r` of `Π_D M(D, β(D))`. A term with an arrow outside the support is `0` by (S). For `β` inside the support, by (H) the product has exact valuation `Σ_D (C + ĉ(D, β(D))) = r·C + U(r) + Σ_D γ(D ∖ β(D))` (Lemma C2; exact valuations add because `2` is prime). The gold is a non-negative integer, zero for all arrows exactly for the golden bijection `β_r` of Theorem B, which lies inside the support. So exactly one term has valuation `r·C + U(r)` and every other non-zero term has valuation at least `r·C + U(r) + 1` (Lemma B of piece C2). ∎

## Checks before formalization

`lean/chkC4.py` (log `logs/chkC4.log`, 481 s while a Lean build shared the machine): Theorem A for every `s ≤ 6` and every `r` (134 cases); Theorem B for every `k ≤ 6`, every `I`, every `r` (1 220 cases); Lemma C1 and Lemma C2 for every `k ≤ 5`, `α ∈ {1, 2}`, `μ ∈ {0, 1, 5}`, random bijections (7 686 identities); Corollary D on random integer matrices satisfying (S) and (H), every `k ≤ 4`, every `I`, every `r ≥ 1`, exact determinants (960 minors). **0 failures.** Controls, each of which must fail somewhere: golden images without «all equal to `1`» (uniqueness fails in 99 cases); golden arrows allowing gold `≤ 1` (525); Lemma C2 with columns `L_r` instead of `F_r` (5 355); Corollary D with one entry `1` outside the support (720).
