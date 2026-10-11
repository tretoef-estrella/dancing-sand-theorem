module

public import RequestProject.EvenZero.PartM

/-!
# `C50h_theorem_10_22_at_zero.md`: Part K — the approximation

(K1) `PsiC (2 ^ n) ≡ PsiC 0` modulo `2 ^ (n + 2)` (C49b `C1`); (K2) the halves are congruent modulo
`2 ^ (n + 1)`; (K3) the approximants exist (C50c `P1`, `P3`, `H1`, `H2`, and C48b `DanceXi.T2`).
-/

@[expose] public section

noncomputable section

namespace EvenZero

open FormalOps FormalDance RingK

/-- **(K1)** of `C50h_theorem_10_22_at_zero.md`: for every `n`,
`ContZero.MCong (n + 2) (fun _ _ : Fin 1 => PsiC (2 ^ n)) (fun _ _ : Fin 1 => PsiC 0)`. -/
theorem K1 (n : ℕ) :
    ContZero.MCong (n + 2) (fun _ _ : Fin 1 => PsiC (2 ^ n)) (fun _ _ : Fin 1 => PsiC 0) :=
  ContZero.mcong_iff.2 fun _ _ => by
    have := ContZero.C1 2 (2 ^ n) 0 n ⟨-1, by push_cast; ring⟩ (FoldOdd.kJ 0 1)
      (fun m _ => FoldOdd.kJ 0 m)
    rw [add_comm] at this
    exact this

/-- Proof of (K2) of `C50h_theorem_10_22_at_zero.md`: halving a congruence (`ℤ_[2]` has no
`2`-torsion). -/
lemma cong_half {M : ℕ} {x y : Bf ℤ_[2]}
    (h : ContZero.Cong (M + 1) ((2 : ℤ_[2]) • x) ((2 : ℤ_[2]) • y)) : ContZero.Cong M x y := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z, fun m f hf => ?_⟩
  have := hz m f hf
  simp only [Bf.coef_sub, Bf.coef_smul] at this ⊢
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) ?_
  rw [pow_succ] at this
  linear_combination this

/-- **(K2)** of `C50h_theorem_10_22_at_zero.md`: for every `n` and `V V₀ : Bf ℤ_[2]` with
`(2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • 1)` and
`(2 : ℤ_[2]) • V₀ = PsiC 0 * (PsiC 0 + (2 : ℤ_[2]) • 1)`:
`ContZero.MCong (n + 1) (fun _ _ : Fin 1 => V) (fun _ _ : Fin 1 => V₀)`. -/
theorem K2 (n : ℕ) (V V₀ : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hV₀ : (2 : ℤ_[2]) • V₀ = PsiC 0 * (PsiC 0 + (2 : ℤ_[2]) • (1 : Bf ℤ_[2]))) :
    ContZero.MCong (n + 1) (fun _ _ : Fin 1 => V) (fun _ _ : Fin 1 => V₀) :=
  ContZero.mcong_iff.2 fun s s' => by
    have h1 := ContZero.mcong_iff.1 (K1 n) s s'
    refine cong_half ?_
    rw [hV, hV₀]
    exact h1.mul (h1.add (ContZero.Cong.refl _ _))

/-- **(K3)** of `C50h_theorem_10_22_at_zero.md` (the approximants exist): for every `l n`, there
are `V : Bf ℤ_[2]` and matrices `Xk Vk` with
`(2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • 1)`,
`DanceRel (Families.ds l) 1 (fun _ _ => PsiC (2 ^ n)) Xk` and
`DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`. -/
theorem K3 (l n : ℕ) :
    ∃ (V : Bf ℤ_[2]) (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) (Bf ℤ_[2])),
      (2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      DanceRel (Families.ds l) 1 (fun _ _ => PsiC (2 ^ n)) Xk ∧
      DanceRel (Families.ds l) 1 (fun _ _ => V) Vk := by
  have hΓ := ArmsEven.P3 0 0
  obtain ⟨Γ', hΓ'g, hΓ'⟩ := ArmsEven.H1 (ArmsEven.GPsi 0 0) hΓ 0 1 (Or.inl rfl)
  have hP1 : covSys ∅ 0 ((2 ^ n : ℕ) : ℤ_[2]) (ArmsEven.GPsi 0 0) ⟨∅, Finset.empty_subset _⟩
      ⟨∅, Finset.empty_subset _⟩ = PsiC (2 ^ n) := by
    rw [ArmsEven.P1, Nat.add_zero]; rfl
  have hM := congrFun (congrFun (ArmsEven.H2 _ hΓ 0 1 (Or.inl rfl) Γ' hΓ' ∅
    ((2 ^ n : ℕ) : ℤ_[2])) ⟨∅, Finset.empty_subset _⟩) ⟨∅, Finset.empty_subset _⟩
  rw [ArmsEven.entry_mul_add_smul_one, hP1, Matrix.smul_apply, mul_one] at hM
  have hP : ∀ t ∈ (∅ : Finset ℕ), t < 0 := by simp
  obtain ⟨Xk, hXk⟩ := DanceXi.T2 (Families.ds l) 1 0 ∅ hP ((2 ^ n : ℕ) : ℤ_[2]) _ hΓ
    DanceXi.finOneDnEmpty (fun _ _ => PsiC (2 ^ n)) (funext fun _ => funext fun _ => hP1.symm)
  obtain ⟨Vk, hVk⟩ := DanceXi.T2 (Families.ds l) 1 0 ∅ hP ((2 ^ n : ℕ) : ℤ_[2]) Γ' hΓ'g
    DanceXi.finOneDnEmpty _ rfl
  exact ⟨_, Xk, Vk, hM, hXk, hVk⟩

end EvenZero
