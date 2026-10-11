module

public import RequestProject.Conjugation.PartC1
public import RequestProject.PathSum.Defs

/-!
# `C45_conjugation_and_general_eta.md`: Part X — the operators

* (X1) `X1_xi`, `X1_sig` (collected in `X1`);
* (X2) `X2`.
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset

/-- (X1) of `C45_conjugation_and_general_eta.md`: for `η ≠ 0`,
`PathSum.XiOp α c η ζ = cj η (PathSum.XiOp α c 1 (fun j f => η⁻¹ ^ j * ζ j f))`. -/
theorem X1_xi (α c : ℕ) {η : ℚ_[2]} (hη : η ≠ 0) (ζ : ℕ → ℤ → ℚ_[2]) :
    PathSum.XiOp α c η ζ = cj η (PathSum.XiOp α c 1 (fun j f => η⁻¹ ^ j * ζ j f)) := by
  ext m f
  rcases m with _ | _ | m
  · simp
  · simp
  · rw [coef_cj, PathSum.XiOp_coef_ge_two _ _ _ _ (by omega),
      PathSum.XiOp_coef_ge_two _ _ _ _ (by omega), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hη,
      one_pow, one_mul]

/-- (X1) of `C45_conjugation_and_general_eta.md`: `PathSum.SigOp α c η = cj η (PathSum.SigOp α c 1)`
(this half holds for every `η`, also `η = 0`). -/
theorem X1_sig (α c : ℕ) (η : ℚ_[2]) : PathSum.SigOp α c η = cj η (PathSum.SigOp α c 1) := by
  ext m f
  rcases m with _ | _ | m
  · simp [PathSum.SigOp]
  · simp [PathSum.SigOp]
  · simp only [PathSum.SigOp, coef_cj]
    rw [PathSum.XiOp_coef_ge_two _ _ _ _ (by omega), PathSum.XiOp_coef_ge_two _ _ _ _ (by omega),
      mul_zero]

/-- **(X1)** of `C45_conjugation_and_general_eta.md`, collected: for `η : ℚ_[2]`, `η ≠ 0`, and
`ζ`: `XiOp α c η ζ = cj η (XiOp α c 1 (fun j f => η⁻¹ ^ j * ζ j f))` and
`SigOp α c η = cj η (SigOp α c 1)`. -/
theorem X1 (α c : ℕ) {η : ℚ_[2]} (hη : η ≠ 0) (ζ : ℕ → ℤ → ℚ_[2]) :
    PathSum.XiOp α c η ζ = cj η (PathSum.XiOp α c 1 (fun j f => η⁻¹ ^ j * ζ j f)) ∧
    PathSum.SigOp α c η = cj η (PathSum.SigOp α c 1) :=
  ⟨X1_xi α c hη ζ, X1_sig α c η⟩

/-- **(X2)** of `C45_conjugation_and_general_eta.md`: if `‖η‖ = 1` and `‖ζ j f‖ ≤ 1` for
`j ≥ 2`, then `‖η⁻¹ ^ j * ζ j f‖ ≤ 1` for `j ≥ 2`. -/
theorem X2 {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1) :
    ∀ j, 2 ≤ j → ∀ f, ‖η⁻¹ ^ j * ζ j f‖ ≤ 1 := by
  intro j hj f
  rw [norm_mul, norm_pow, norm_inv, hη, inv_one, one_pow, one_mul]
  exact hζ j hj f

end Conjugation
