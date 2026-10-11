module

public import RequestProject.FoldOdd.PartF4

/-!
# `C49_the_fold_law_on_the_odd_families.md`: Part C — Corollary 10.17
-/

@[expose] public section

noncomputable section

namespace FoldOdd

open FormalOps Doubling Finset DPLattice

/-- The cokernel of `act (T l) l (l + 1) (XiOpZ 2 c η ζ)` is `FamilyGroup.X (Families.ds l) 2 c`
whenever (C48b) (R2) or (R0) applies: `1 ≤ c` and `IsUnit η`, `ζ` constant in the floor; or
`l = 0`. -/
lemma coker_act_XiOpZ (l c : ℕ) (η : ℤ_[2]) (z : ℕ → ℤ_[2])
    (h : (1 ≤ c ∧ IsUnit η) ∨ l = 0) :
    Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range
        (act (Filt.T ℤ_[2] l) (l : ℤ) (l + 1) (Smith2.XiOpZ 2 c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) 2 c) := by
  obtain ⟨e1⟩ := F6 (Filt.T ℤ_[2] l) (l : ℤ) (l + 1) (Smith2.XiOpZ 2 c η (fun m _ => z m))
  rcases h with ⟨hc, hη⟩ | rfl
  · obtain ⟨e2⟩ := DanceXi.R2 l 2 c le_rfl hc η hη z (l + 1) le_rfl
    exact ⟨e1.symm.trans e2⟩
  · obtain ⟨e2⟩ := DanceXi.R0 2 c (by norm_num) η (fun m _ => z m) (0 + 1) le_rfl
    rw [Nat.cast_zero] at e1 ⊢
    exact ⟨e1.symm.trans e2⟩

/-- **(C1)** of `C49_the_fold_law_on_the_odd_families.md` (the two cokernels on `T(l)`): for
`l j : ℕ` with `1 ≤ j ∨ l = 0`, the cokernel of `FoldHalf.Psi (Filt.T ℤ_[2] l) (l + j) (l + 1)`
is isomorphic to the cokernel of `FoldCube.SigmaOp (Filt.T ℤ_[2] l) (l + 2 * ((j + 1) / 2))`. -/
theorem C1 (l j : ℕ) (h : 1 ≤ j ∨ l = 0) :
    Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1))) ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range
        (FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ))))) := by
  set c := (j + 1) / 2 with hc
  rw [← (F4 l j c (l + 1) le_rfl).1, ← (F4 l j c (l + 1) le_rfl).2, (F5 j c).1.1, (F5 j c).2]
  have hη : IsUnit (kJ j 1) := (F5 j c).1.2.1
  obtain ⟨e1⟩ := coker_act_XiOpZ l c (kJ j 1) (kJ j)
    (h.imp (fun hj => ⟨by omega, hη⟩) id)
  obtain ⟨e2⟩ := coker_act_XiOpZ l c 1 (fun _ => 0)
    (h.imp (fun hj => ⟨by omega, isUnit_one⟩) id)
  exact ⟨e1.trans e2.symm⟩

/-- Corollary 10.17 for the odd family `2 l + 1` and the index `j`, from (C1):
C39 (A4_odd), then (C1), then C39b (O5_X) backwards. -/
lemma fold_odd_of (l j : ℕ) (h : 1 ≤ j ∨ l = 0) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)) := by
  obtain ⟨e1⟩ := FoldHalf.A4_odd l j
  obtain ⟨e2⟩ := C1 l j h
  obtain ⟨e3⟩ := FoldCube.O5_X l j
  exact ⟨e1.toAddEquiv.trans (e2.toAddEquiv.trans e3.symm)⟩

/-- **(C2)** of `C49_the_fold_law_on_the_odd_families.md` (Corollary 10.17 for `j ≥ 1`): for
every `l j : ℕ` with `1 ≤ j`,
`FoldGroup.XbarFam (2 * l + 1) j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)`. -/
theorem C2 (l j : ℕ) (hj : 1 ≤ j) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)) :=
  fold_odd_of l j (Or.inl hj)

/-- **(C3)** of `C49_the_fold_law_on_the_odd_families.md` (Corollary 10.17 for `l = 0`): for
every `j : ℕ`,
`FoldGroup.XbarFam (2 * 0 + 1) j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * 0 + 1)) 1 j)`. -/
theorem C3 (j : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * 0 + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * 0 + 1)) 1 j)) :=
  fold_odd_of 0 j (Or.inr rfl)

end FoldOdd
