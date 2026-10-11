module

public import Mathlib

/-!
# `C50g_theorem_10_22_for_i_positive.md`: (A) — associates

Folder `RequestProject/EvenFold/`, namespace `EvenFold`. (A) is stated over any commutative ring.
-/

@[expose] public section

noncomputable section

namespace EvenFold

/-- **(A)** of `C50g_theorem_10_22_for_i_positive.md` (associates): for a commutative ring `R`, a
`Fintype n` with `DecidableEq`, `M P : Matrix n n R` with `IsUnit P.det`, and `c : R`:
`(n → R) ⧸ range (c • mulVecLin (P * M)) ≃ₗ[R] (n → R) ⧸ range (c • mulVecLin M)`. -/
theorem A {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M P : Matrix n n R) (hP : IsUnit P.det) (c : R) :
    Nonempty (((n → R) ⧸ LinearMap.range (c • Matrix.mulVecLin (P * M))) ≃ₗ[R]
      ((n → R) ⧸ LinearMap.range (c • Matrix.mulVecLin M))) := by
  letI := P.invertibleOfIsUnitDet hP
  let e : (n → R) ≃ₗ[R] (n → R) := Matrix.toLinearEquiv' P this
  have he : (LinearMap.range (c • Matrix.mulVecLin M)).map (e : (n → R) →ₗ[R] (n → R)) =
      LinearMap.range (c • Matrix.mulVecLin (P * M)) := by
    rw [Matrix.mulVecLin_mul, ← LinearMap.comp_smul, LinearMap.range_comp]
    rfl
  exact ⟨(Submodule.Quotient.equiv _ _ e he).symm⟩

end EvenFold
