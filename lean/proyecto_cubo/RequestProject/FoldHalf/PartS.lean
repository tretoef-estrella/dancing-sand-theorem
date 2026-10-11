module

public import RequestProject.FoldHalf.Ops

/-!
# `C39_the_fold_on_the_half_lattice.md`: Part S — the operators

* (S1) `S1`: under (nil), `Sh N BN` is a unit, and `Sh * ShInv = 1 = ShInv * Sh`.
* (S2) `S2`: `parOp N d` squares to `1` and commutes with every `N.Fd s`, `Ch`, `Sh`, `ShInv`;
  `Ch`, `Sh`, `ShInv` commute pairwise. This holds without (nil) (more general).
* (S3) `S3`: `(2 : A) • Zop N d BN = Psi N d BN − Psi N (d + 1) BN`, without (nil).
* (S4) `S4`: composition of `glueOp`, for operators on any module.
-/

@[expose] public section

noncomputable section

namespace FoldHalf

open DPLattice Doubling Finset Fold

variable {A : Type*} [CommRing A]

lemma commute_ringInverse {R : Type*} [Ring R] {x y : R} (h : Commute x y) :
    Commute x (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hy]
    exact Commute.zero_right x

section S

variable (N : DPLattice A) (BN : ℕ)

lemma Fd_commute_Ch (r : ℕ) : Commute (N.Fd r) (Ch N BN) :=
  Commute.sum_right _ _ _ fun s _ => (Fd_commute N r s).smul_right _

lemma Fd_commute_Sh (r : ℕ) : Commute (N.Fd r) (Sh N BN) :=
  Commute.sum_right _ _ _ fun s _ => (Fd_commute N r s).smul_right _

lemma Ch_commute_Sh : Commute (Ch N BN) (Sh N BN) :=
  Commute.sum_left _ _ _ fun s _ => (Fd_commute_Sh N BN s).smul_left _

lemma parOp_commute_Ch (d : ℤ) : Commute (parOp N d) (Ch N BN) :=
  Commute.sum_right _ _ _ fun s _ => Commute.smul_right (parOp_comm_Fd N d s : Commute (parOp N d) (N.Fd s)) _

lemma parOp_commute_Sh (d : ℤ) : Commute (parOp N d) (Sh N BN) :=
  Commute.sum_right _ _ _ fun s _ => Commute.smul_right (parOp_comm_Fd N d s : Commute (parOp N d) (N.Fd s)) _

lemma parOp_commute_ShInv (d : ℤ) : Commute (parOp N d) (ShInv N BN) :=
  commute_ringInverse (parOp_commute_Sh N BN d)

lemma Ch_commute_ShInv : Commute (Ch N BN) (ShInv N BN) :=
  commute_ringInverse (Ch_commute_Sh N BN)

lemma Sh_commute_ShInv : Commute (Sh N BN) (ShInv N BN) :=
  commute_ringInverse (Commute.refl _)

/-- Under (nil), `F^{(s)}` is nilpotent for `s ≥ 1`. -/
lemma Fd_isNilpotent (hnil : ∀ s ≥ BN, N.Fd s = 0) (s : ℕ) (hs : 1 ≤ s) :
    IsNilpotent (N.Fd s) := by
  have key : ∀ k : ℕ, ∃ c : A, N.Fd s ^ (k + 1) = c • N.Fd (s * (k + 1)) := by
    intro k
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * ((s * (k + 1) + s).choose (s * (k + 1)) : ℕ), ?_⟩
      rw [pow_succ, hc, smul_mul_assoc, Fd_mul, smul_smul, show s * (k + 1) + s = s * (k + 2) by
        ring]
  refine ⟨BN + 1, ?_⟩
  obtain ⟨c, hc⟩ := key BN
  rw [hc, hnil _ (by nlinarith), smul_zero]

/-- **(S1)** of `C39_the_fold_on_the_half_lattice.md`: under (nil), `Sh N BN` is a unit of
`Module.End A (N.ι → A)`; hence `Sh N BN * ShInv N BN = 1 = ShInv N BN * Sh N BN`. -/
theorem S1 (hnil : ∀ s ≥ BN, N.Fd s = 0) :
    IsUnit (Sh N BN) ∧ Sh N BN * ShInv N BN = 1 ∧ ShInv N BN * Sh N BN = 1 := by
  have hu : IsUnit (Sh N BN) := by
    rcases BN with _ | b
    · have : (1 : Module.End A (N.ι → A)) = 0 := by rw [← N.isDP.P0_F]; exact hnil 0 le_rfl
      haveI := subsingleton_of_zero_eq_one this.symm
      exact isUnit_of_subsingleton _
    · rw [Sh, Finset.sum_range_succ']
      simp only [zero_add, N.isDP.P0_F]
      have h1 : dfi (A := A) 1 = 1 := by simp [dfi]
      rw [h1, one_smul]
      refine IsNilpotent.isUnit_add_one (Commute.isNilpotent_sum (fun s _ => ?_) fun s t _ _ => ?_)
      · exact (Fd_isNilpotent N _ hnil (s + 1) (by omega)).smul _
      · exact ((Fd_commute N _ _).smul_left _).smul_right _
  refine ⟨hu, Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu⟩

/-- **(S2)** of `C39_the_fold_on_the_half_lattice.md`: `parOp N d * parOp N d = 1`; `parOp N d`
commutes with every `N.Fd s`, with `Ch N BN`, `Sh N BN` and `ShInv N BN`; and `Ch`, `Sh`, `ShInv`
commute pairwise. (Holds without (nil): more general than the file.) -/
theorem S2 (d : ℤ) :
    parOp N d * parOp N d = 1 ∧
    (∀ s, parOp N d * N.Fd s = N.Fd s * parOp N d) ∧
    parOp N d * Ch N BN = Ch N BN * parOp N d ∧
    parOp N d * Sh N BN = Sh N BN * parOp N d ∧
    parOp N d * ShInv N BN = ShInv N BN * parOp N d ∧
    Ch N BN * Sh N BN = Sh N BN * Ch N BN ∧
    Ch N BN * ShInv N BN = ShInv N BN * Ch N BN ∧
    Sh N BN * ShInv N BN = ShInv N BN * Sh N BN :=
  ⟨parOp_mul_self N d, parOp_comm_Fd N d, parOp_commute_Ch N BN d, parOp_commute_Sh N BN d,
    parOp_commute_ShInv N BN d, Ch_commute_Sh N BN, Ch_commute_ShInv N BN, Sh_commute_ShInv N BN⟩

/-- **(S3)** of `C39_the_fold_on_the_half_lattice.md`:
`(2 : A) • Zop N d BN = Psi N d BN − Psi N (d + 1) BN` (holds without (nil)). -/
theorem S3 (d : ℤ) : (2 : A) • Zop N d BN = Psi N d BN - Psi N (d + 1) BN := by
  simp only [Zop, Psi, parOp_succ, sub_mul, sub_neg_eq_add, add_mul]
  push_cast
  module

end S

/-- **(S4)** of `C39_the_fold_on_the_half_lattice.md`:
`glueOp X Y Z ∘ₗ glueOp X' Y' Z' = glueOp (X ∘ₗ X') (Y ∘ₗ Y') (Z ∘ₗ X' + Y ∘ₗ Z')`
(for operators on any module `L`; the file uses `L = N.ι → A`). -/
theorem S4 {L : Type*} [AddCommGroup L] [Module A L] (X Y Z X' Y' Z' : Module.End A L) :
    glueOp X Y Z ∘ₗ glueOp X' Y' Z' = glueOp (X ∘ₗ X') (Y ∘ₗ Y') (Z ∘ₗ X' + Y ∘ₗ Z') := by
  apply LinearMap.ext; intro p
  simp only [LinearMap.comp_apply, glueOp_apply, LinearMap.add_apply, map_add, Prod.mk.injEq,
    true_and]
  abel

end FoldHalf
