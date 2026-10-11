module

public import RequestProject.ArmsEven.Defs

/-!
# `C50c_the_arms_of_the_even_families.md`: Part A — the first arms

(A1) the arms `GPsi (eI i) (i + 1)` and `GPsi 0 i` are congruent modulo `2`.
-/

@[expose] public section

noncomputable section

namespace ArmsEven

open RingK Cleanliness FoldOdd FormalOps Finset

/-- Helper for (A1) of `C50c_the_arms_of_the_even_families.md`:
`KF (i + 1) - KF i = (2 * (-1) ^ i) • ShInvF`. -/
lemma KF_succ_sub (i : ℕ) :
    KF (i + 1) - KF i = ((2 : ℤ_[2]) * (-1) ^ i) • (ShInvF : Bf ℤ_[2]) := by
  rw [KF, KF, ← sub_mul, sub_sub_sub_cancel_left, ← sub_smul, smul_mul_assoc, one_mul]
  congr 1
  ring

/-- Helper for (A1) of `C50c_the_arms_of_the_even_families.md`:
`kJ (i + 1) m - kJ i m = 2 * ((-1) ^ i * shInvC m)`. -/
lemma kJ_succ_sub (i m : ℕ) : kJ (i + 1) m - kJ i m = 2 * ((-1) ^ i * shInvC m) := by
  have h := congrArg (fun x : Bf ℤ_[2] => x.coef m 0) (KF_succ_sub i)
  simp only [Bf.coef_sub, Bf.coef_smul] at h
  rw [kJ, kJ, h, ShInvF, coef_cst]
  ring

/-- **(A1)** of `C50c_the_arms_of_the_even_families.md`: for every `i`,
`Cong2 (GPsi (eI i) (i + 1)) (GPsi 0 i)`. -/
theorem A1 (i : ℕ) : DanceMod2.Cong2 (GPsi (eI i) (i + 1)) (GPsi 0 i) := by
  intro Δ m y
  by_cases hΔ : Δ = ∅
  · by_cases h0 : m = 0
    · exact ⟨2 * (eI i : ℤ_[2]), by simp [GPsi, hΔ, h0]; ring⟩
    · refine ⟨(-1) ^ i * shInvC m, ?_⟩
      simp only [GPsi, hΔ, h0, if_true, if_false]
      exact kJ_succ_sub i m
  · exact ⟨0, by simp [GPsi, hΔ]⟩

end ArmsEven
