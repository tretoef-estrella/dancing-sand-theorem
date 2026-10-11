module

public import RequestProject.FoldOdd.Defs

/-!
# `C49_the_fold_law_on_the_odd_families.md`: Part F — the formal operators

(F1), (F2), (F3), (F5), (F6). (F4) is in `PartF4.lean`.
-/

@[expose] public section

noncomputable section

namespace FoldOdd

open FormalOps Doubling Finset DPLattice

variable {A : Type*} [CommRing A]

/-! ### (F1) -/

/-- **(F1)** of `C49_the_fold_law_on_the_odd_families.md` (constant series): for `a b : ℕ → A`,
`cst a * cst b = cst (fun m => Σ_{a' ∈ range (m + 1)} C(m, a') * a a' * b (m − a'))`, and
`cst a * cst b = cst b * cst a`. -/
theorem F1 (a b : ℕ → A) :
    cst a * cst b = cst (fun m => ∑ a' ∈ range (m + 1), (m.choose a' : A) * a a' * b (m - a')) ∧
    cst a * cst b = cst b * cst a := by
  refine ⟨by ext m f; rfl, ?_⟩
  ext m f
  simp only [Bf.coef_mul, coef_cst]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show m + 1 - 1 - i = m - i by omega, show m - (m - i) = i by omega,
    Nat.choose_symm (by omega)]
  ring

/-! ### (F2) -/

/-- Auxiliary for (F2): `shC 0 = dfi 1 = 1`. -/
lemma shC_zero : shC (A := A) 0 = 1 := by simp [shC]

/-- **(F2)** of `C49_the_fold_law_on_the_odd_families.md` (`Sh` is a unit): in `Bf A`, for any
commutative ring `A`, `ShF * ShInvF = 1` and `ShInvF * ShF = 1`. -/
theorem F2 : ShF (A := A) * ShInvF = 1 ∧ ShInvF (A := A) * ShF = 1 := by
  have h1 : ShF (A := A) * ShInvF = 1 := by
    rw [ShF, ShInvF, (F1 _ _).1]
    ext m f
    simp only [coef_cst, Bf.coef_one]
    rcases m with _ | m
    · simp [shC_zero]
    · rw [if_neg (by omega), ← Finset.sum_range_reflect, Finset.sum_range_succ]
      simp only [show m + 1 + 1 - 1 - (m + 1) = 0 by omega, Nat.sub_zero, Nat.choose_zero_right,
        Nat.cast_one, shC_zero, one_mul]
      rw [shInvC_eq (m + 1) (by omega), ← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [show m + 1 + 1 - 1 - i = m + 1 - i by omega, show m + 1 - (m + 1 - i) = i by omega,
        Nat.choose_symm (by omega)]
  exact ⟨h1, by rw [ShF, ShInvF, ← (F1 _ _).2, ← ShF, ← ShInvF, h1]⟩

/-! ### (F3) -/

/-- Auxiliary for (F3): `act N W B (cst a) = Σ_{m ∈ range B} a m • N.Fd m`. -/
lemma act_cst (N : DPLattice A) (W : ℤ) (B : ℕ) (a : ℕ → A) :
    act N W B (cst a) = ∑ m ∈ range B, a m • N.Fd m := by
  unfold act
  refine Finset.sum_congr rfl fun m _ => ?_
  ext v i
  simp [flD_apply, Module.End.mul_apply]

/-- Auxiliary for (F3): under (nil) and `BN ≤ B`, `act N W B (cst a) = Σ_{m ∈ range BN} a m • N.Fd m`. -/
lemma act_cst_nil (N : DPLattice A) (W : ℤ) {BN B : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (hB : BN ≤ B) (a : ℕ → A) :
    act N W B (cst a) = ∑ m ∈ range BN, a m • N.Fd m := by
  rw [act_cst]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  rw [Finset.sum_range_add, add_eq_left]
  exact Finset.sum_eq_zero fun j _ => by rw [hnil (BN + j) (by omega), smul_zero]

/-- **(F3)** of `C49_the_fold_law_on_the_odd_families.md` (the action): for `N : DPLattice A`,
`W : ℤ`, `BN B : ℕ` with (nil) `∀ s ≥ BN, N.Fd s = 0`, `BN ≤ B` and `1 ≤ B`:
`act N W B ChF = FoldHalf.Ch N BN`, `act N W B ShF = FoldHalf.Sh N BN` and
`act N W B ShInvF = FoldHalf.ShInv N BN`. -/
theorem F3 (N : DPLattice A) (W : ℤ) (BN B : ℕ) (hnil : ∀ s ≥ BN, N.Fd s = 0) (hB : BN ≤ B)
    (hB1 : 1 ≤ B) :
    act N W B ChF = FoldHalf.Ch N BN ∧ act N W B ShF = FoldHalf.Sh N BN ∧
      act N W B ShInvF = FoldHalf.ShInv N BN := by
  have hCh : act N W B ChF = FoldHalf.Ch N BN := by
    rw [ChF, act_cst_nil N W hnil hB]; rfl
  have hSh : act N W B ShF = FoldHalf.Sh N BN := by
    rw [ShF, act_cst_nil N W hnil hB]; rfl
  refine ⟨hCh, hSh, ?_⟩
  have h1 : FoldHalf.Sh N BN * act N W B ShInvF = 1 := by
    rw [← hSh, ← act_mul hnil hB, F2.1, act_one hB1]
  have h2 : act N W B ShInvF * FoldHalf.Sh N BN = 1 := by
    rw [← hSh, ← act_mul hnil hB, F2.2, act_one hB1]
  let u : (Module.End A (N.ι → A))ˣ := ⟨FoldHalf.Sh N BN, act N W B ShInvF, h1, h2⟩
  rw [FoldHalf.ShInv, show FoldHalf.Sh N BN = (u : Module.End A (N.ι → A)) from rfl,
    Ring.inverse_unit]
  rfl

/-! ### (F5) -/

/-- Auxiliary for (F5): `(KF j).coef m f = kJ j m` (the coefficients of `KF j` do not depend on `f`). -/
lemma coef_KF (j m : ℕ) (f : ℤ) : (KF j).coef m f = kJ j m := by
  simp [kJ, KF, ChF, ShInvF]

/-- Auxiliary for (F5): `kJ j 0 = 1 − (−1)^j`. -/
lemma kJ_zero (j : ℕ) : kJ j 0 = 1 - (-1) ^ j := by
  simp [kJ, KF, ChF, ShInvF, chC]

/-- Auxiliary for (F5): `kJ j 1 = −(1 − (−1)^j) * dfi 2 + 1`. -/
lemma kJ_one (j : ℕ) : kJ j 1 = -(1 - (-1) ^ j) * dfi 2 + 1 := by
  have hs : shInvC (A := ℤ_[2]) 1 = -dfi 2 := by
    rw [shInvC_eq 1 le_rfl]; simp [shC]
  simp [kJ, KF, ChF, ShInvF, chC, Finset.sum_range_succ, hs]
  ring

/-- Auxiliary for (F5): `3 * dfi 2 = 1` in `ℤ_[2]`. -/
lemma three_mul_dfi_two : (3 : ℤ_[2]) * dfi 2 = 1 := by
  have h := OddUnits.hodd (A := ℤ_[2]) 1
  have h3 : (((2 * 2 - 1).doubleFactorial : ℕ) : ℤ_[2]) = 3 := by
    norm_num [Nat.doubleFactorial]
  rw [dfi, h3]
  exact Ring.mul_inverse_cancel _ (by simpa using h)

/-- **(F5)** of `C49_the_fold_law_on_the_odd_families.md` (both are of the form `Ξ`): for every
`j c : ℕ`, `PsiF j = Smith2.XiOpZ 2 ((j + 1) / 2) (kJ j 1) (fun m _ => kJ j m)` and
`IsUnit (kJ j 1)`; moreover `kJ j 1 = 1` if `Even j` and `3 * kJ j 1 = 1` if `Odd j`; and
`SigF c = Smith2.XiOpZ 2 c 1 (fun _ _ => 0)`. -/
theorem F5 (j c : ℕ) :
    (PsiF j = Smith2.XiOpZ 2 ((j + 1) / 2) (kJ j 1) (fun m _ => kJ j m) ∧
      IsUnit (kJ j 1) ∧ (Even j → kJ j 1 = 1) ∧ (Odd j → 3 * kJ j 1 = 1)) ∧
    SigF c = Smith2.XiOpZ 2 c 1 (fun _ _ => 0) := by
  have hev : Even j → kJ j 1 = 1 := fun h => by rw [kJ_one, h.neg_one_pow]; ring
  have hod : Odd j → 3 * kJ j 1 = 1 := fun h => by
    rw [kJ_one, h.neg_one_pow]; linear_combination (-2 : ℤ_[2]) * three_mul_dfi_two
  refine ⟨⟨?_, ?_, hev, hod⟩, ?_⟩
  · ext m f
    rcases m with _ | _ | m
    · simp only [PsiF, Bf.coef_add, Bf.coef_dg, if_true, coef_KF, kJ_zero, Smith2.XiOpZ]
      rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
      · rw [show (2 * k + 1) / 2 = k by omega, (even_two_mul k).neg_one_pow]
        push_cast; ring
      · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, (odd_two_mul_add_one k).neg_one_pow]
        push_cast; ring
    · simp [PsiF, coef_KF, Smith2.XiOpZ]
    · simp [PsiF, coef_KF, Smith2.XiOpZ]
  · rcases Nat.even_or_odd j with h | h
    · rw [hev h]; exact isUnit_one
    · exact IsUnit.of_mul_eq_one_right _ (hod h)
  · ext m f
    rcases m with _ | _ | m
    · norm_num [SigF, Smith2.XiOpZ]
    · simp [SigF, Smith2.XiOpZ]
    · simp [SigF, Smith2.XiOpZ]

/-! ### (F6) -/

/-- **(F6)** of `C49_the_fold_law_on_the_odd_families.md` (one slot): for `N : DPLattice A`,
`W : ℤ`, `B : ℕ` and `x : Bf A`, the cokernel of `FormalAct.sysAct N W B (fun _ _ => x)` on
`Fin 1 → N.ι → A` is isomorphic to the cokernel of `act N W B x` on `N.ι → A`. -/
theorem F6 (N : DPLattice A) (W : ℤ) (B : ℕ) (x : Bf A) :
    Nonempty (((Fin 1 → N.ι → A) ⧸ LinearMap.range (FormalAct.sysAct N W B (fun _ _ => x))) ≃ₗ[A]
      ((N.ι → A) ⧸ LinearMap.range (act N W B x))) := by
  let e : (Fin 1 → N.ι → A) ≃ₗ[A] (N.ι → A) := LinearEquiv.funUnique (Fin 1) A (N.ι → A)
  have hcomm : (e : (Fin 1 → N.ι → A) →ₗ[A] (N.ι → A)) ∘ₗ FormalAct.sysAct N W B (fun _ _ => x) =
      act N W B x ∘ₗ (e : (Fin 1 → N.ι → A) →ₗ[A] (N.ι → A)) := by
    refine LinearMap.ext fun v => ?_
    simp [e, LinearEquiv.funUnique]
  refine ⟨Submodule.Quotient.equiv _ _ e ?_⟩
  rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp_of_range_eq_top _ e.range]

end FoldOdd
