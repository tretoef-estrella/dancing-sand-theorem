module

public import RequestProject.PathSum.Aux

/-!
# `C43_path_sum.md`: (P0), (P1), (P2)

* (P0) `P0`: uniqueness of the right inverse (stated over any field `K`, more general than
  `ℚ_[2]`).
* (P1) `P1`: the inverse of `Σ` is `sL`; from (P0) and the operator `sLOp` with coefficients
  `sL`, which is a right inverse of `Σ` by the recursion `sL_succ`.
* (P2) `P2`: Lemma 10.10, by strong induction on `L` (`P2_gen`, which needs only `α ≥ 1`).
-/

@[expose] public section

noncomputable section

namespace PathSum

open FormalOps FormalDance Doubling Finset

/-- **(P0)** of `C43_path_sum.md` (uniqueness of the right inverse): if `x.coef 0 f ≠ 0` for
every `f ≥ 0` and `Agree (x * Y₁) 1`, `Agree (x * Y₂) 1`, then `Agree Y₁ Y₂`. Stated over any
field `K` (the file has `K = ℚ_[2]`), which is more general. -/
theorem P0 {K : Type*} [Field K] (x Y₁ Y₂ : Bf K) (hx : ∀ f : ℤ, 0 ≤ f → x.coef 0 f ≠ 0)
    (h₁ : Agree (x * Y₁) 1) (h₂ : Agree (x * Y₂) 1) : Agree Y₁ Y₂ := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro f hf
    have e1 := h₁ L f hf
    have e2 := h₂ L f hf
    rw [coef_mul_split] at e1 e2
    have hs : ∑ a ∈ range L, (L.choose (a + 1) : K) * x.coef (a + 1) f *
        Y₁.coef (L - (a + 1)) (f - ((a + 1 : ℕ) : ℤ)) =
        ∑ a ∈ range L, (L.choose (a + 1) : K) * x.coef (a + 1) f *
        Y₂.coef (L - (a + 1)) (f - ((a + 1 : ℕ) : ℤ)) := by
      refine sum_congr rfl fun a ha => ?_
      have := mem_range.mp ha
      rw [ih (L - (a + 1)) (by omega) _ (by push_cast; omega)]
    rw [hs] at e1
    exact mul_left_cancel₀ (hx f (by omega)) (add_right_cancel (e1.trans e2.symm))

/-- Proof of (P1) of `C43_path_sum.md` (auxiliary): the operator with coefficients
`coef L f = sL α c η L f`. -/
def sLOp (α c : ℕ) (η : ℚ_[2]) : Bf ℚ_[2] := ⟨fun L f => sL α c η L f⟩

/-- Proof of (P1) of `C43_path_sum.md` (auxiliary): `sLOp` is a right inverse of `Σ` at the
floors `f ≥ m`, by the recursion `sL_succ`. -/
lemma agree_SigOp_sLOp {α c : ℕ} (hc : 1 ≤ c) (η : ℚ_[2]) :
    Agree (SigOp α c η * sLOp α c η) 1 := by
  intro m f hf
  have h0 : piF α c f ≠ 0 := piF_ne_zero hc (by omega)
  rcases m with _ | L
  · simp [SigOp, sLOp, sL_zero, h0]
  · rw [coef_mul_split, sum_range_succ', Bf.coef_one, if_neg (by omega)]
    have hz : ∀ a ∈ range L, ((L + 1).choose (a + 1 + 1) : ℚ_[2]) *
        (SigOp α c η).coef (a + 1 + 1) f *
        (sLOp α c η).coef (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ)) = 0 := by
      intro a _
      rw [SigOp, XiOp_coef_ge_two _ _ _ _ (by omega)]
      ring
    rw [sum_eq_zero hz]
    simp only [SigOp, XiOp_coef_zero, XiOp_coef_one, sLOp, sL_succ, zero_add,
      Nat.choose_one_right, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

/-- **(P1)** of `C43_path_sum.md` (the inverse of `Σ`): for `c ≥ 1` and `Y` with
`Agree (SigOp α c η * Y) 1`, `Y.coef L f = sL α c η L f` for all `L` and `f ≥ L` (`η`
arbitrary). -/
theorem P1 {α c : ℕ} (hc : 1 ≤ c) (η : ℚ_[2]) (Y : Bf ℚ_[2])
    (hY : Agree (SigOp α c η * Y) 1) :
    ∀ L : ℕ, ∀ f : ℤ, (L : ℤ) ≤ f → Y.coef L f = sL α c η L f :=
  P0 (SigOp α c η) Y (sLOp α c η) (fun _ hf => piF_ne_zero hc hf) hY (agree_SigOp_sLOp hc η)

/-- **(P2)** of `C43_path_sum.md` (Lemma 10.10), the strong induction on `L`, in the more general
form with `α ≥ 1` instead of `α ≥ 2` and the bound written `(1/2)^(α − 1)`. -/
theorem P2_gen {α c : ℕ} (hα : 1 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (Y : Bf ℚ_[2])
    (hY : Agree (XiOp α c η ζ * Y) 1) :
    ∀ L : ℕ, ∀ f : ℤ, (L : ℤ) ≤ f →
      ∃ e : ℚ_[2], Y.coef L f = sL α c η L f * (1 + e) ∧ ‖e‖ ≤ (1 / 2 : ℝ) ^ (α - 1) := by
  have hη0 : η ≠ 0 := by rintro rfl; simp at hη
  have hC : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (α - 1) := by positivity
  have hC1 : (1 / 2 : ℝ) ^ (α - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro f hf
  have h0 : piF α c f ≠ 0 := piF_ne_zero hc (by omega)
  have h := hY L f hf
  rcases L with _ | L
  · refine ⟨0, ?_, by simp⟩
    simp only [Bf.coef_mul, zero_add, range_one, sum_singleton, Nat.choose_self, Nat.cast_one,
      one_mul, XiOp_coef_zero, Nat.sub_self, Nat.cast_zero, sub_zero, Bf.coef_one,
      if_true] at h
    rw [sL_zero, add_zero, mul_one, eq_div_iff h0, mul_comm, h]
  · rw [coef_mul_split, sum_range_succ', Bf.coef_one, if_neg (by omega)] at h
    obtain ⟨e1, he1, hn1⟩ := ih L (by omega) (f - 1) (by push_cast at hf; omega)
    have hIH : ∀ a : ℕ, a < L → ∃ e : ℚ_[2],
        Y.coef (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ)) =
          sL α c η (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ)) * (1 + e) ∧
          ‖e‖ ≤ (1 / 2 : ℝ) ^ (α - 1) := fun a ha =>
      ih _ (by omega) _ (by push_cast at hf ⊢; omega)
    choose! E hE hEn using hIH
    set s := sL α c η (L + 1) f with hs
    have hs0 : s ≠ 0 := sL_ne_zero hc hη0 hf
    let t : ℕ → ℚ_[2] := fun a => -(((L + 1).choose (a + 1 + 1) : ℚ_[2]) *
      (ζ (a + 1 + 1) f * (1 + E a)) *
      sL α c η (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ)) / (piF α c f * s))
    have ht : ∀ a ∈ range L, ‖t a‖ ≤ (1 / 2 : ℝ) ^ (α - 1) := by
      intro a ha
      have ha' := mem_range.mp ha
      simp only [t, norm_neg]
      rw [hs, term_identity hc hη0 (by omega) (by omega) hf]
      refine term_norm_le hα hη (by omega) f ?_
      rw [norm_mul]
      exact mul_le_one₀ (hζ _ (by omega) f) (norm_nonneg _)
        (norm_one_add_le ((hEn a ha').trans hC1))
    refine ⟨e1 + ∑ a ∈ range L, t a, ?_, ?_⟩
    · have hsum : ∑ a ∈ range L, ((L + 1).choose (a + 1 + 1) : ℚ_[2]) *
            (XiOp α c η ζ).coef (a + 1 + 1) f *
            Y.coef (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ)) =
          ∑ a ∈ range L, ((L + 1).choose (a + 1 + 1) : ℚ_[2]) *
            (ζ (a + 1 + 1) f * (1 + E a)) *
            sL α c η (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ)) := by
        refine sum_congr rfl fun a ha => ?_
        rw [XiOp_coef_ge_two _ _ _ _ (by omega), hE a (mem_range.mp ha)]
        ring
      rw [hsum] at h
      simp only [XiOp_coef_zero, zero_add, XiOp_coef_one, Nat.add_sub_cancel, Nat.cast_one,
        Nat.choose_one_right] at h
      rw [he1, show (((L + 1 : ℕ) : ℚ_[2])) = (L : ℚ_[2]) + 1 by push_cast; ring] at h
      have hst : ∑ a ∈ range L, t a = -(∑ a ∈ range L, ((L + 1).choose (a + 1 + 1) : ℚ_[2]) *
            (ζ (a + 1 + 1) f * (1 + E a)) *
            sL α c η (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ))) / (piF α c f * s) := by
        rw [neg_div, sum_div, ← sum_neg_distrib]
      rw [hst]
      have hs' : s * piF α c f = -(((L : ℚ_[2]) + 1) * η * sL α c η L (f - 1)) := by
        rw [hs, sL_succ, div_mul_cancel₀ _ h0]
      generalize (∑ a ∈ range L, ((L + 1).choose (a + 1 + 1) : ℚ_[2]) *
            (ζ (a + 1 + 1) f * (1 + E a)) *
            sL α c η (L + 1 - (a + 1 + 1)) (f - ((a + 1 + 1 : ℕ) : ℤ))) = S at h ⊢
      field_simp
      linear_combination h - (1 + e1) * hs'
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hn1
        (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC ht))

/-- `C43_path_sum.md` (auxiliary): `2 ^ (−(α − 1 : ℤ)) = (1/2)^(α − 1)` for `α ≥ 1`. -/
lemma two_zpow_eq {α : ℕ} (hα : 1 ≤ α) :
    (2 : ℝ) ^ (-(α - 1 : ℤ)) = (1 / 2 : ℝ) ^ (α - 1) := by
  rw [show (α - 1 : ℤ) = ((α - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, one_div, inv_pow]

/-- **(P2)** of `C43_path_sum.md` (Lemma 10.10, the path sum), as in the file: for `α ≥ 2`,
`c ≥ 1`, `‖η‖ = 1`, `‖ζ m f‖ ≤ 1` for all `m ≥ 2` and `f`, and `Y` with
`Agree (XiOp α c η ζ * Y) 1`: for all `L` and `f ≥ L`, `sL α c η L f ≠ 0` and there is `e` with
`Y.coef L f = sL α c η L f * (1 + e)` and `‖e‖ ≤ 2 ^ (−(α − 1 : ℤ))`. (Only `α ≥ 1` is used from
`α ≥ 2`, see `P2_gen`.) -/
theorem P2 {α c : ℕ} (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (Y : Bf ℚ_[2])
    (hY : Agree (XiOp α c η ζ * Y) 1) :
    ∀ L : ℕ, ∀ f : ℤ, (L : ℤ) ≤ f →
      sL α c η L f ≠ 0 ∧
        ∃ e : ℚ_[2], Y.coef L f = sL α c η L f * (1 + e) ∧
          ‖e‖ ≤ (2 : ℝ) ^ (-(α - 1 : ℤ)) := by
  intro L f hf
  have hη0 : η ≠ 0 := by rintro rfl; simp at hη
  refine ⟨sL_ne_zero hc hη0 hf, ?_⟩
  rw [two_zpow_eq (by omega)]
  exact P2_gen (by omega) hc hη hζ Y hY L f hf

end PathSum
