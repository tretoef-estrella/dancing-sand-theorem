# The deficit law (Lemma 4.5) and the closed form of the final matrix (§4.4–§4.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §4.4–§4.5: the polynomials `q_t` of Theorem 4.4, Lemma 4.5 (the deficit law) and its subadditivity remark, the rescaling `c^{(h)} = −2^{1−2^h} q_h` used at the end of the proof of Theorem 4.4, and the valuation of the closed-form entries `M_{DD'}` stated in Theorem D. The payment systems and the moves (Propositions 4.1–4.3), and the identification of `M` with the matrix of the dance (Theorem 4.4 itself), come in a later piece; here the closed form is a **definition**, and only its arithmetic is proved.

This file reuses, without changing them:
- piece C3 (`RequestProject/Rulers/`): `oE` (`o_E = Σ_{t∈E} 2^t`), `minOr`, `delta` (`δ(Δ) = k − |Δ| − min Δ`, `δ(∅) = 0`), `v2`, and Lemma 5.0 (`lemma_5_0_sdiff`).

## Setting

All coefficient functions are functions `Finset ℕ → ℤ` (or `→ ℚ`), indexed by finite sets `Δ` of natural numbers (the monomial `y^Δ = ∏_{t∈Δ} y_t` of the algebra `ℤ[y_t]/(y_t^2)`). The product of that algebra on coefficient functions is
  `(f ⋆ g)(Δ) := Σ_{Δ₁ ⊆ Δ} f(Δ₁) · g(Δ ∖ Δ₁)`
(ordered decompositions `Δ = Δ₁ ⊔ Δ₂`), and multiplication by `y_t` is `(y_t f)(Δ) := [t ∈ Δ] · f(Δ ∖ {t})`.

Fix `I : Finset ℕ`.

**The polynomials `q_t`.** `a_t(Δ)` is the coefficient of `y^Δ` in `q_t`, defined by recursion on `t`:
- `a_0(Δ) := −[Δ = ∅]` (that is, `q_0 = −1`);
- `a_{t+1}(Δ) := (a_t ⋆ a_t)(Δ) − [t ∈ I] · [t ∈ Δ] · a_t(Δ ∖ {t})` (that is, `q_{t+1} = q_t^2 − [t ∈ I] y_t q_t`).

**The rescaled coefficients.** `c_h(Δ) ∈ ℚ`, by recursion on `h`:
- `c_0(Δ) := [Δ = ∅]`;
- `c_{h+1}(Δ) := −½ (c_h ⋆ c_h)(Δ) − [h ∈ I] · [h ∈ Δ] · c_h(Δ ∖ {h})`.

**The closed-form entries.** For `k ∈ ℕ`, `K := 2^k`, `α ∈ ℤ`, `i ∈ ℕ` and finite sets `D' ⊆ D`, put `π_0(d) := 2^α (i + d)` (in `ℚ`; `α ≥ 1` below) and
  `Mc(D, D') := −2^{1 − K + o(D ∖ D')} · a_k(D ∖ D') · ∏_{d = o_D}^{o_{D'} + K − 1} π_0(d)`  (in `ℚ`),
the product running over the natural numbers `d` with `o_D ≤ d < o_{D'} + K`.

## Part A — the polynomials

**(A1) Support.** For every `t` and `Δ`: if `Δ ⊄ {u ∈ I : u < t}` then `a_t(Δ) = 0`.

**(A2) Constant term.** For every `t ≥ 1`, `a_t(∅) = 1`.

**(A3) The deficit, general form.** For every `t` and every non-empty `Δ ⊆ I` with `max Δ < t`: `a_t(Δ) ≠ 0` and
  `v_2(a_t(Δ)) = t − |Δ| − min Δ`
(an identity of natural numbers; the right side is `≥ 0`, because `Δ ⊆ [min Δ, t)`).

**Lemma 4.5 (the deficit law).** Let `k ≥ 1` and `I ⊆ {0, …, k − 1}`. For every `Δ ⊆ I`: `a_k(Δ) ≠ 0` and `v_2(a_k(Δ)) = δ(Δ)` (as integers, with `δ = Rulers.delta k`); in particular `a_k(∅) = 1` and `v_2(a_k(Δ)) = k − |Δ| − min Δ` for `Δ ≠ ∅`. So `v_2(a_k(Δ))` depends only on `k` and `Δ`, not on the other elements of `I`.

**(A4) Strict subadditivity.** For non-empty disjoint `Δ₁, Δ₂ ⊆ {0, …, k − 1}`:
  `δ(Δ₁) + δ(Δ₂) − δ(Δ₁ ∪ Δ₂) = k − max(min Δ₁, min Δ₂) ≥ 1`.

**(A5) Example `λ = 6`.** For `I = {0, 1}`: `a_1(∅) = 1`, `a_1({0}) = 1` (`q_1 = 1 + y_0`); and `a_2(∅) = 1`, `a_2({0}) = 2`, `a_2({1}) = −1`, `a_2({0, 1}) = −1` (`q_2 = 1 + 2y_0 − y_1 − y_0 y_1`).

*Proof of (A3) (from the paper).* Induction on `|Δ|`, then on `t`. Let `m := max Δ ∈ I`, `μ := min Δ`. By (A1) `q_m` does not involve `y_m`, so the coefficient of `y^Δ` in `a_m ⋆ a_m` is `0` (every ordered decomposition puts `m` into a part `Δ_j` with `a_m(Δ_j) = 0`), and `a_{m+1}(Δ) = −a_m(Δ ∖ {m})`. If `Δ = {m}` this is `−a_m(∅) = ±1` (valuation `0 = (m + 1) − 1 − m`; `a_0(∅) = −1`, `a_m(∅) = 1` for `m ≥ 1`); otherwise `Δ ∖ {m}` is non-empty with maximum `< m`, minimum `μ`, and by induction its valuation is `m − (|Δ| − 1) − μ`. For `t ≥ m + 1`, `t ∉ Δ`, so the term `[t ∈ Δ]` vanishes and
  `a_{t+1}(Δ) = 2 a_t(∅) a_t(Δ) + Σ_{∅ ≠ Δ₁ ⊊ Δ} a_t(Δ₁) a_t(Δ ∖ Δ₁) = 2 a_t(Δ) + 2 Σ a_t(Δ₁) a_t(Δ₂)`
over the unordered decompositions into non-empty parts. One of `min Δ₁, min Δ₂` is `μ` and the other is `≤ m`, so by induction each cross term has valuation `≥ 1 + 2t − |Δ| − μ − m`, which exceeds `v_2(2 a_t(Δ)) = 1 + t − |Δ| − μ` by `t − m ≥ 1`; so `v_2(a_{t+1}(Δ)) = 1 + t − |Δ| − μ`. ∎

Lemma 4.5 follows from (A2), (A3) and `max Δ ≤ k − 1`. (A4): `δ(Δ₁) + δ(Δ₂) − δ(Δ₁ ∪ Δ₂) = k − min Δ₁ − min Δ₂ + min(Δ₁ ∪ Δ₂)`, and `min(Δ₁ ∪ Δ₂) = min(min Δ₁, min Δ₂)`; the result is `k − max(min Δ₁, min Δ₂) ≥ 1` because both minima are `≤ k − 1`.

## Part B — the rescaling (end of the proof of Theorem 4.4)

**(B1)** For every `h` and every `Δ`:
  `c_h(Δ) = −2^{1 − 2^h} · 2^{o(Δ)} · a_h(Δ)`  (in `ℚ`).

*Proof.* Put `y_t := 2^{2^t} x_t`; the coefficient of `x^Δ` in `q_h` is `2^{o(Δ)} a_h(Δ)`. Then `c^{(h)} = −2^{1 − 2^h} q_h` satisfies `c^{(0)} = 1` and
  `c^{(h+1)} = −2^{1 − 2^{h+1}} q_h^2 + [h ∈ I] 2^{1 − 2^h} 2^{−2^h} y_h q_h = −2^{1 − 2^{h+1}} (q_h^2 − [h ∈ I] y_h q_h)`.
On coefficients: by induction on `h`, using `2^{o(Δ₁)} 2^{o(Δ ∖ Δ₁)} = 2^{o(Δ)}` for `Δ₁ ⊆ Δ`, and `2^{o(Δ ∖ {h})} · 2^{2^h} = 2^{o(Δ)}` for `h ∈ Δ`. ∎

## Part C — the closed form (Theorem D, the valuations)

**(C1) Window.** For `D' ⊆ D ⊆ I ⊆ {0, …, k − 1}`: `o_{D'} + K − o_D = K − o(D ∖ D') ≥ 1` (so the window `[o_D, o_{D'} + K − 1]` is non-empty).

**(C2) Integrality and valuation.** Let `k ≥ 1`, `I ⊆ {0, …, k − 1}`, `α ≥ 1`, `i ∈ ℕ`, and `D' ⊆ D ⊆ I` with `0 < i + o_D` (that is, `i ≥ 1` or `D ≠ ∅`). Then `Mc(D, D')` is a non-zero integer (there is `z ∈ ℤ`, `z ≠ 0`, with `Mc(D, D') = z`), and
  `v_2(Mc(D, D')) = 1 − K + o(D ∖ D') + δ(D ∖ D') + Σ_{d = o_D}^{o_{D'} + K − 1} (α + v_2(i + d))`
(an identity of integers; `v_2` of the non-zero rational, e.g. `padicValRat 2`).

*Proof.* Every `d` in the window has `i + d ≥ i + o_D ≥ 1`, so `π_0(d) ≠ 0` and `v_2(π_0(d)) = α + v_2(i + d)`; `a_k(D ∖ D') ≠ 0` with valuation `δ(D ∖ D')` by Lemma 4.5; `v_2` is additive. Integrality: the valuation is `≥ 1 − K + o(Δ) + α(K − o(Δ)) ≥ 1` (by (C1) and `α ≥ 1`), and the odd part is an integer (`a_k` and the `i + d` are integers). ∎

## Checks before formalization

`lean/chkC10.py` (logs `logs/chkC10.log`, `logs/chkC10_k6.log`): exhaustive for every `k ≤ 6`, every `I ⊆ {0, …, k − 1}`, all `t ≤ k`, all `Δ`; for Part C, `α ∈ {1, 2}`, `i ≤ 3`, all `D' ⊆ D ⊆ I`. Exact rational arithmetic. Checked: (A1)–(A5), Lemma 4.5, (B1), (C1), (C2). 0 failures. Controls, each of which must fail somewhere, and does: the square over **unordered** decompositions (no cross doubling); the term `[t + 1 ∈ I]` instead of `[t ∈ I]`; the deficit with `|Δ| − 1`; the rescaling with `2^{1 − 2^{h+1}}`; the valuation of (C2) without `δ`.
