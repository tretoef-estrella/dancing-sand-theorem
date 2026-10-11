module

public import RequestProject.EvenZero.PartL

/-!
# `C50h_theorem_10_22_at_zero.md`: Part T — the fold law on every even family

(T0) `i = 0`: the assembly of C50g `T`, with (L) for the arm `U′` instead of C50g `M1`;
(TT) Theorem 10.22 for every `i`: (T0) and C50g `EvenFold.T`.
-/

@[expose] public section

noncomputable section

namespace EvenZero

open FormalOps FormalDance

/-- **(T0)** of `C50h_theorem_10_22_at_zero.md` (`i = 0`): for every `l : ℕ`,
`Nonempty (FoldGroup.XbarFam (2 * l + 2) 0 ≃+
FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 0))`. -/
theorem T0 (l : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) 0 ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 0)) := by
  have h21 : (2 : ℕ) = 2 * 1 := rfl
  obtain ⟨e1⟩ := FoldHalf.A4_even l 0
  obtain ⟨Xk, Yk, Zk, hP, hZ, he2⟩ := GlueEven.Q2 h21 l 0 0
  rw [pow_zero, one_smul] at he2
  obtain ⟨e2⟩ := he2
  obtain ⟨hXd, hYd, -⟩ := GlueDance.D1 _ hP
  obtain ⟨-, -, U, U', ZU, Uk, U'k, -, -, -, -, -, hU, hU', hZU, hPU⟩ := GlueEven.Q4 l 0
  obtain ⟨hUd, hU'd, -⟩ := GlueDance.D1 _ hPU
  obtain ⟨ZUk, hZUk, he3⟩ := GlueEven.Q3 h21 l 0 0 U U' ZU hU hU' hZU Uk U'k hPU
  rw [pow_zero, one_smul] at he3
  obtain ⟨Wm, hWm, hWm1, hWmf⟩ := EvenFold.M1 l (0 + 1) le_rfl (-2) (Or.inr rfl) U
    (by rw [hU, sub_eq_add_neg, neg_smul]) Xk Uk hXd hUd
  obtain ⟨Wp, hWp, hWp1, hWpf⟩ := L l U' hU' Yk U'k hYd hU'd
  obtain ⟨P, hPu, hPe⟩ := EvenFold.M2 h21 l Xk Yk Zk Uk U'k ZUk hZ hZUk Wm Wp hWm hWp hWm1
    hWp1 hWmf hWpf
  rw [hPe] at he3
  obtain ⟨e3⟩ := he3
  obtain ⟨eA⟩ := EvenFold.A
    (finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk)) P hPu
    ((2 : ℤ_[2]) ^ (0 + (Families.ds l).length))
  obtain ⟨e4⟩ := FoldCube.V6 l 0
  exact ⟨e1.toAddEquiv.trans (e2.toAddEquiv.trans
    (((LinearEquiv.refl ℤ_[2] (GlueEven.PF l 2 0)).prodCongr eA.symm).toAddEquiv.trans
      (e3.symm.toAddEquiv.trans e4.symm)))⟩

/-- **(TT)** of `C50h_theorem_10_22_at_zero.md` (Theorem 10.22, the fold law on every even
family): for all `l i : ℕ`,
`Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i))`. -/
theorem TT (l i : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i)) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact T0 l
  · exact EvenFold.T l i hi

end EvenZero
