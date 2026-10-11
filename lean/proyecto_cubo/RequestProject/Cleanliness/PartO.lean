module

public import RequestProject.Cleanliness.Defs

/-!
# `C48_cleanliness_one_move.md`: Part O — the operators at level 0

Namespace `Cleanliness`. (O1) and (O2) of the file. The equality of (O2) is an equality in
`Bf ℤ_[2]`, not only agreement.
-/

@[expose] public section

noncomputable section

namespace Cleanliness

open RingK FormalOps Finset

/-- **(O1)** of `C48_cleanliness_one_move.md`: if `2 ≤ α` and `IsUnit η`, then
`Good (G0 α η z)` for every `z`. -/
theorem O1 (α : ℕ) (η : ℤ_[2]) (hα : 2 ≤ α) (hη : IsUnit η) (z : ℕ → ℤ_[2]) :
    Good (G0 α η z) := by
  refine ⟨fun Δ m => ?_, fun y => ?_, fun y => ?_⟩
  · by_cases hΔ : Δ = ∅
    · by_cases h0 : m = 0
      · have : G0 α η z Δ m = fun y => 2 ^ α * y := by funext y; simp [G0, hΔ, h0]
        rw [this]; exact K3_pow_mul α hα
      · have : G0 α η z Δ m = fun _ => if m = 1 then η else z m := by
          funext y; simp [G0, hΔ, h0]
        rw [this]; exact K3_const _
    · have : G0 α η z Δ m = fun _ => 0 := by funext y; simp [G0, hΔ]
      rw [this]; exact K3_const _
  · obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
    exact ⟨2 ^ k * y, by simp [G0]; ring⟩
  · simpa [G0] using hη

/-- **(O2)** of `C48_cleanliness_one_move.md`: for `α c : ℕ`, `η`, `z`,
`covSys ∅ 0 (c : ℤ_[2]) (G0 α η z) ⟨∅, _⟩ ⟨∅, _⟩ = XiOpZ α c η (fun m _ => z m)` (an equality
in `Bf ℤ_[2]`). -/
theorem O2 (α c : ℕ) (η : ℤ_[2]) (z : ℕ → ℤ_[2]) :
    covSys ∅ 0 (c : ℤ_[2]) (G0 α η z) ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ =
      Smith2.XiOpZ α c η (fun m _ => z m) := by
  ext m f
  simp [covSys_coef, G0, Smith2.XiOpZ, oS]

end Cleanliness
