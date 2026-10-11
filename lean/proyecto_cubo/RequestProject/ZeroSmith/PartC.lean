module

public import RequestProject.ZeroSmith.PartR
public import RequestProject.FoldOdd.All

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`, Part C — Corollary 10.17 for every index

(C4) `C4`; (C5) `C5`.

As in C49 (C1), each quotient is parenthesised: written exactly as in the file, Lean would group
`… ⧸ range Psi … ≃ₗ[ℤ_[2]] … ⧸ range SigmaOp …` differently.
-/

@[expose] public section

noncomputable section

namespace ZeroSmith

open FormalOps FoldOdd

/-- Proof of (C4) of `C49c_smith_form_and_cokernel_at_zero.md`: for every `l c`, every unit `η`
and every `z`, the cokernel of `act (T l) l (l + 1) (XiOpZ 2 c η (fun m _ => z m))` is
`FamilyGroup.X (Families.ds l) 2 c` (C49 (F6) and (R7)). -/
lemma coker_act_XiOpZ_all (l c : ℕ) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2]) :
    Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range
        (act (Filt.T ℤ_[2] l) (l : ℤ) (l + 1) (Smith2.XiOpZ 2 c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) 2 c) := by
  obtain ⟨e1⟩ := F6 (Filt.T ℤ_[2] l) (l : ℤ) (l + 1) (Smith2.XiOpZ 2 c η (fun m _ => z m))
  obtain ⟨e2⟩ := R7 l c 2 le_rfl η hη z (l + 1) le_rfl
  exact ⟨e1.symm.trans e2⟩

/-- **(C4)** of `C49c_smith_form_and_cokernel_at_zero.md` (C49 (C1) without its hypothesis): for
every `l j : ℕ`, the cokernel of `FoldHalf.Psi (Filt.T ℤ_[2] l) (l + j) (l + 1)` is isomorphic to
the cokernel of `FoldCube.SigmaOp (Filt.T ℤ_[2] l) (l + 2 * ((j + 1) / 2))`. -/
theorem C4 (l j : ℕ) :
    Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1))) ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range
        (FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ))))) := by
  set c := (j + 1) / 2 with hc
  rw [← (F4 l j c (l + 1) le_rfl).1, ← (F4 l j c (l + 1) le_rfl).2, (F5 j c).1.1, (F5 j c).2]
  have hη : IsUnit (kJ j 1) := (F5 j c).1.2.1
  obtain ⟨e1⟩ := coker_act_XiOpZ_all l c (kJ j 1) hη (kJ j)
  obtain ⟨e2⟩ := coker_act_XiOpZ_all l c 1 isUnit_one (fun _ => 0)
  exact ⟨e1.trans e2.symm⟩

/-- **(C5)** of `C49c_smith_form_and_cokernel_at_zero.md` (Corollary 10.17): for every
`l j : ℕ`,
`Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j))`
(C39 `A4_odd`, (C4), C39b `O5_X` read backwards). -/
theorem C5 (l j : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)) := by
  obtain ⟨e1⟩ := FoldHalf.A4_odd l j
  obtain ⟨e2⟩ := C4 l j
  obtain ⟨e3⟩ := FoldCube.O5_X l j
  exact ⟨e1.toAddEquiv.trans (e2.toAddEquiv.trans e3.symm)⟩

end ZeroSmith
