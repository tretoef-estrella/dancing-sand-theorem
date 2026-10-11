module

public import RequestProject.Deficit.Basic
public import RequestProject.Deficit.Polynomials
public import RequestProject.Deficit.DeficitLaw
public import RequestProject.Deficit.Rescaling
public import RequestProject.Deficit.ClosedForm

/-!
# The deficit law (Lemma 4.5) and the closed form of the final matrix (`C10_deficit_law.md`)

Index of the formalization (namespace `Deficit`).

## Encodings

* Coefficient functions are functions `Finset ℕ → ℤ` (for `a_t`) and `Finset ℕ → ℚ` (for
  `c_h`); the value at `Δ` is the coefficient of `y^Δ = ∏_{t∈Δ} y_t`.
* The product `(f ⋆ g)(Δ) = Σ_{Δ₁ ⊆ Δ} f(Δ₁) g(Δ ∖ Δ₁)` is `starMul f g Δ`, a sum over
  `Δ.powerset` (ordered decompositions).  Indicators `[P]` are `if P then 1 else 0`.
* `a I t Δ` (`a_t(Δ)`) and `c I h Δ` (`c_h(Δ)`) are defined by structural recursion on `t`, `h`,
  with exactly the recursions of the Setting (`Δ ∖ {t}` is `Δ \ {t}`).
* `pi0 α i d = 2^α (i + d)` in `ℚ` (`α : ℤ`, integer power), and
  `Mc I k α i D D' = −2^{1 − 2^k + o(D ∖ D')} · a_k(D ∖ D') · ∏_{d ∈ Finset.Ico o_D (o_{D'} + 2^k)} π_0(d)`
  in `ℚ` (the power of `2` is an integer power).
* Reused from C3: `Rulers.oE` (`o_E`), `Rulers.minOr` (`min`, with `min ∅ = k`),
  `Rulers.delta` (`δ`), `Rulers.v2` (`v_2` on `ℕ`) and Lemma 5.0 (`Rulers.lemma_5_0_sdiff`).
  Valuations: `padicValInt 2` on integers, `padicValRat 2` on rationals.
* `I ⊆ {0, …, k − 1}` is `hI : ∀ t ∈ I, t < k`; "non-empty" is `Finset.Nonempty`;
  `min Δ`, `max Δ` of a non-empty `Δ` are `Δ.min' h`, `Δ.max' h` (in (A4), `min` is
  `Rulers.minOr k`, which agrees with `min'` on non-empty sets).

## Files

* `Basic.lean` — the Setting: `starMul`, `a`, `c`, `pi0`, `Mc`.
* `Polynomials.lean` — **(A1)** `A1_support`, **(A2)** `A2_const`, **(A3)** `A3_deficit`
  (with the odd-part form `A3_odd`).
* `DeficitLaw.lean` — **Lemma 4.5** `lemma_4_5` (with `lemma_4_5_empty`,
  `lemma_4_5_nonempty`, `lemma_4_5_indep` for the "in particular" and "depends only on `k` and
  `Δ`" sentences), **(A4)** `A4_subadditivity`, **(A5)** `A5_q1`, `A5_q2`.
* `Rescaling.lean` — **(B1)** `B1_rescaling`.
* `ClosedForm.lean` — **(C1)** `C1_window`, **(C2)** `C2_integrality_valuation`.

## Remarks on hypotheses

* (A1), (A2), (B1) hold for every `I` (no hypothesis); (A3) needs only `Δ ⊆ I` (no bound on `I`).
* `lemma_4_5_empty` (`a_k(∅) = 1`) does not need `I ⊆ {0, …, k − 1}`.
* (A3) is stated as an identity of natural numbers, together with `|Δ| + min Δ ≤ t` (so the
  natural subtraction does not truncate).
* All hypotheses of (C1), (C2), Lemma 4.5 and (A4) are used.
-/
