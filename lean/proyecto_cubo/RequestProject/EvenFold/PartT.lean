module

public import RequestProject.EvenFold.PartM
public import RequestProject.EvenFold.PartA
public import RequestProject.FoldHalf.All
public import RequestProject.FoldCube.All

/-!
# `C50g_theorem_10_22_for_i_positive.md`: Part T — Theorem 10.22 for `i ≥ 1`

(T) the fold law on the even families, `i ≥ 1`: C39 `FoldHalf.A4_even`, then C50f `GlueEven.Q2`
at `h = 0`, then (M1) twice, (M2) and (A), then C50f `GlueEven.Q3` at `h = 0` (with the arms of
`GlueEven.Q4`), then C39b `FoldCube.V6` read backwards.
-/

@[expose] public section

noncomputable section

namespace EvenFold

open FormalOps FormalDance

/-- **(T)** of `C50g_theorem_10_22_for_i_positive.md` (the fold law on the even families,
`i ≥ 1`; paper v8, Theorem 10.22): for all `l i : ℕ` with `1 ≤ i`,
`Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i))`. -/
theorem T (l i : ℕ) (hi : 1 ≤ i) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i)) := by
  have h21 : (2 : ℕ) = 2 * 1 := rfl
  obtain ⟨e1⟩ := FoldHalf.A4_even l i
  obtain ⟨Xk, Yk, Zk, hP, hZ, he2⟩ := GlueEven.Q2 h21 l 0 i
  rw [pow_zero, one_smul] at he2
  obtain ⟨e2⟩ := he2
  obtain ⟨hXd, hYd, -⟩ := GlueDance.D1 _ hP
  obtain ⟨-, -, U, U', ZU, Uk, U'k, -, -, -, -, -, hU, hU', hZU, hPU⟩ := GlueEven.Q4 l i
  obtain ⟨hUd, hU'd, -⟩ := GlueDance.D1 _ hPU
  obtain ⟨ZUk, hZUk, he3⟩ := GlueEven.Q3 h21 l 0 i U U' ZU hU hU' hZU Uk U'k hPU
  rw [pow_zero, one_smul] at he3
  obtain ⟨Wm, hWm, hWm1, hWmf⟩ := M1 l (i + 1) (by omega) (-2) (Or.inr rfl) U
    (by rw [hU, sub_eq_add_neg, neg_smul]) Xk Uk hXd hUd
  obtain ⟨Wp, hWp, hWp1, hWpf⟩ := M1 l i hi 2 (Or.inl rfl) U' hU' Yk U'k hYd hU'd
  obtain ⟨P, hPu, hPe⟩ := M2 h21 l Xk Yk Zk Uk U'k ZUk hZ hZUk Wm Wp hWm hWp hWm1 hWp1
    hWmf hWpf
  rw [hPe] at he3
  obtain ⟨e3⟩ := he3
  obtain ⟨eA⟩ := A (finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk)) P hPu
    ((2 : ℤ_[2]) ^ (0 + (Families.ds l).length))
  obtain ⟨e4⟩ := FoldCube.V6 l i
  exact ⟨e1.toAddEquiv.trans (e2.toAddEquiv.trans
    (((LinearEquiv.refl ℤ_[2] (GlueEven.PF l 2 0)).prodCongr eA.symm).toAddEquiv.trans
      (e3.symm.toAddEquiv.trans e4.symm)))⟩

end EvenFold
