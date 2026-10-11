module

public import RequestProject.ArmsEven.PartP
public import RequestProject.ArmsEven.PartA
public import RequestProject.ArmsEven.PartC

/-!
# `C50c_the_arms_of_the_even_families.md`: Part E — the arms of an even family

(E1) the halves `U`, `U'` of `Ψ_{i+1}(Ψ_{i+1} − 2)` and `Ψ_i(Ψ_i + 2)` exist as good systems,
congruent modulo `2`, with the arms `GPsi (eI i) (i + 1)`, `GPsi 0 i` congruent modulo `2`;
(E2) both pairs of arms dance congruently modulo `2` (`GlueDance.PairRel`).

In both statements `c := (i + 1) / 2`, `Γ₁ := GPsi (eI i) (i + 1)` and `Γ₀ := GPsi 0 i` are
written out in full, and `e∅` is `⟨∅, Finset.empty_subset _⟩`.
-/

@[expose] public section

noncomputable section

namespace ArmsEven

open RingK Cleanliness DanceMod2 FoldOdd FormalOps Finset

/-- Helper for (E1) of `C50c_the_arms_of_the_even_families.md`: the `e∅ e∅` entry of
`M * (M + a • 1)` for matrices on `Dn ∅` (which has the single index `e∅`). -/
lemma entry_mul_add_smul_one (M : Matrix (Dn ∅) (Dn ∅) (Bf ℤ_[2])) (a : ℤ_[2]) :
    (M * (M + a • (1 : Matrix (Dn ∅) (Dn ∅) (Bf ℤ_[2])))) ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ =
      M ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ *
        (M ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ + a • (1 : Bf ℤ_[2])) := by
  haveI : Subsingleton (Dn ∅) := DanceXi.finOneDnEmpty.symm.subsingleton
  rw [Matrix.mul_apply, Fintype.sum_subsingleton _ ⟨∅, Finset.empty_subset _⟩, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply_eq]

/-- **(E1)** of `C50c_the_arms_of_the_even_families.md`: for every `i`, with `c = (i + 1) / 2`,
`Γ₁ = GPsi (eI i) (i + 1)` and `Γ₀ = GPsi 0 i`, there are good systems `U`, `U'` with
`Cong2 Γ₁ Γ₀`, `Cong2 U U'`, `2 U = Γ₁ (Γ₁ − 2)`, `2 U' = Γ₀ (Γ₀ + 2)` (as `prodFun 0`), and
`2 • covSys ∅ 0 c U e∅ e∅ = PsiF (i + 1) * (PsiF (i + 1) - 2 • 1)`,
`2 • covSys ∅ 0 c U' e∅ e∅ = PsiF i * (PsiF i + 2 • 1)`. -/
theorem E1 (i : ℕ) :
    ∃ U U' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good U ∧ Good U' ∧
      Cong2 (GPsi (eI i) (i + 1)) (GPsi 0 i) ∧ Cong2 U U' ∧
      (∀ Δ m y, 2 * U Δ m y = prodFun 0 (GPsi (eI i) (i + 1))
        (GPsi (eI i) (i + 1) + (-2 : ℤ_[2]) • uSys) Δ m y) ∧
      (∀ Δ m y, 2 * U' Δ m y = prodFun 0 (GPsi 0 i) (GPsi 0 i + (2 : ℤ_[2]) • uSys) Δ m y) ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF (i + 1) * (PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U' ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF i * (PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) := by
  obtain ⟨U, hUg, hU⟩ := H1 (GPsi (eI i) (i + 1)) (P3 _ _) 0 (-1) (Or.inr rfl)
  obtain ⟨U', hU'g, hU'⟩ := H1 (GPsi 0 i) (P3 _ _) 0 1 (Or.inl rfl)
  have e1 : (2 : ℤ_[2]) * -1 = -2 := by norm_num
  have hU2 : ∀ Δ m y, 2 * U Δ m y = prodFun 0 (GPsi (eI i) (i + 1))
      (GPsi (eI i) (i + 1) + (-2 : ℤ_[2]) • uSys) Δ m y := by
    rw [← e1]; exact hU
  have hU'2 : ∀ Δ m y, 2 * U' Δ m y =
      prodFun 0 (GPsi 0 i) (GPsi 0 i + (2 : ℤ_[2]) • uSys) Δ m y := by
    simpa only [mul_one] using hU'
  refine ⟨U, U', hUg, hU'g, A1 i, C1 _ _ (P3 _ _).1 (P3 _ _).1 (A1 i) 0 U U' hU2 hU'2, hU2, hU'2,
    ?_, ?_⟩
  · have hM := congrFun (congrFun (H2 _ (P3 _ _) 0 (-1) (Or.inr rfl) U hU ∅
      (((i + 1) / 2 : ℕ) : ℤ_[2])) ⟨∅, Finset.empty_subset _⟩) ⟨∅, Finset.empty_subset _⟩
    rw [entry_mul_add_smul_one, (P2 i).2, Matrix.smul_apply] at hM
    rw [hM, e1, neg_smul, ← sub_eq_add_neg]
  · have hM := congrFun (congrFun (H2 _ (P3 _ _) 0 1 (Or.inl rfl) U' hU' ∅
      (((i + 1) / 2 : ℕ) : ℤ_[2])) ⟨∅, Finset.empty_subset _⟩) ⟨∅, Finset.empty_subset _⟩
    rw [entry_mul_add_smul_one, (P2 i).1, Matrix.smul_apply] at hM
    rw [hM, mul_one]

/-- **(E2)** of `C50c_the_arms_of_the_even_families.md`: for every `i` and every `ds`, with `c`,
`Γ₁`, `Γ₀` as in (E1), there are good systems `U`, `U'` with `Cong2 U U'`,
`2 • covSys ∅ 0 c U e∅ e∅ = PsiF (i + 1) * (PsiF (i + 1) - 2 • 1)`,
`2 • covSys ∅ 0 c U' e∅ e∅ = PsiF i * (PsiF i + 2 • 1)`, and both pairs of arms
(`PsiF (i + 1)`, `PsiF i`) and (`covSys ∅ 0 c U e∅ e∅`, `covSys ∅ 0 c U' e∅ e∅`), as `1 × 1`
matrices, dance congruently modulo `2` (`GlueDance.PairRel ds 1`). -/
theorem E2 (i : ℕ) (ds : List Bool) :
    ∃ U U' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good U ∧ Good U' ∧ Cong2 U U' ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF (i + 1) * (PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U' ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF i * (PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (∃ Xk Yk, GlueDance.PairRel ds 1 (fun _ _ => PsiF (i + 1)) (fun _ _ => PsiF i) Xk Yk) ∧
      ∃ Uk U'k, GlueDance.PairRel ds 1
        (fun _ _ => covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩)
        (fun _ _ => covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U' ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩) Uk U'k := by
  obtain ⟨U, U', hUg, hU'g, hA, hC, -, -, hE, hE'⟩ := E1 i
  have hP : ∀ t ∈ (∅ : Finset ℕ), t < 0 := by simp
  refine ⟨U, U', hUg, hU'g, hC, hE, hE', ?_, ?_⟩
  · exact D1 ds 1 0 ∅ hP (((i + 1) / 2 : ℕ) : ℤ_[2]) _ _ (P3 _ _) (P3 _ _) hA
      DanceXi.finOneDnEmpty _ _ (funext fun _ => funext fun _ => (P2 i).2.symm)
      (funext fun _ => funext fun _ => (P2 i).1.symm)
  · exact D1 ds 1 0 ∅ hP (((i + 1) / 2 : ℕ) : ℤ_[2]) U U' hUg hU'g hC
      DanceXi.finOneDnEmpty _ _ rfl rfl

end ArmsEven
