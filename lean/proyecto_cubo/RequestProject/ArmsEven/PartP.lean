module

public import RequestProject.ArmsEven.Defs

/-!
# `C50c_the_arms_of_the_even_families.md`: Part P — the positions

(P1) the covariant system of `GPsi e j` at `c` is `XiOpZ 2 (c + e) (kJ j 1) (kJ j ·)`; (P2) the
arms `Ψ_i`, `Ψ_{i+1}` are covariant systems at the same position `c = (i + 1) / 2`; (P3) every
`GPsi e j` is good.
-/

@[expose] public section

noncomputable section

namespace ArmsEven

open RingK Cleanliness FoldOdd FormalOps Finset

/-- **(P1)** of `C50c_the_arms_of_the_even_families.md`: for every `c e j : ℕ`,
`covSys ∅ 0 c (GPsi e j) e∅ e∅ = XiOpZ 2 (c + e) (kJ j 1) (fun m _ => kJ j m)`. -/
theorem P1 (c e j : ℕ) :
    covSys ∅ 0 (c : ℤ_[2]) (GPsi e j) ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ =
      Smith2.XiOpZ 2 (c + e) (kJ j 1) (fun m _ => kJ j m) := by
  ext m f
  rcases m with _ | _ | m
  · simp [covSys_coef, GPsi, Smith2.XiOpZ, oS]; ring
  · simp [covSys_coef, GPsi, Smith2.XiOpZ]
  · simp [covSys_coef, GPsi, Smith2.XiOpZ]

/-- Helper for (P2) of `C50c_the_arms_of_the_even_families.md`:
`(i + 1) / 2 + eI i = (i + 2) / 2`. -/
lemma add_eI (i : ℕ) : (i + 1) / 2 + eI i = (i + 1 + 1) / 2 := by
  unfold eI; omega

/-- **(P2)** of `C50c_the_arms_of_the_even_families.md`: for every `i`, with `c = (i + 1) / 2`,
`covSys ∅ 0 c (GPsi 0 i) e∅ e∅ = PsiF i` and
`covSys ∅ 0 c (GPsi (eI i) (i + 1)) e∅ e∅ = PsiF (i + 1)`. -/
theorem P2 (i : ℕ) :
    covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) (GPsi 0 i) ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ = PsiF i ∧
      covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) (GPsi (eI i) (i + 1)) ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ = PsiF (i + 1) := by
  refine ⟨?_, ?_⟩
  · rw [P1, (F5 i 0).1.1, Nat.add_zero]
  · rw [P1, (F5 (i + 1) 0).1.1, add_eI]

/-- **(P3)** of `C50c_the_arms_of_the_even_families.md`: for every `e j : ℕ`, `Good (GPsi e j)`. -/
theorem P3 (e j : ℕ) : Good (GPsi e j) := by
  refine ⟨fun Δ m => ?_, fun y => ⟨y + (e : ℤ_[2]), by simp [GPsi]⟩, fun y => ?_⟩
  · by_cases hΔ : Δ = ∅
    · by_cases h0 : m = 0
      · have : GPsi e j Δ m = (fun y => 2 ^ 2 * y) + fun _ => 4 * (e : ℤ_[2]) := by
          funext y; simp [GPsi, hΔ, h0]; ring
        rw [this]; exact K3_add (K3_pow_mul 2 le_rfl) (K3_const _)
      · have : GPsi e j Δ m = fun _ => kJ j m := by funext y; simp [GPsi, hΔ, h0]
        rw [this]; exact K3_const _
    · have : GPsi e j Δ m = fun _ => 0 := by funext y; simp [GPsi, hΔ]
      rw [this]; exact K3_const _
  · simpa [GPsi] using (F5 j 0).1.2.1

end ArmsEven
