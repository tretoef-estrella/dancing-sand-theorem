module

public import RequestProject.ZeroSmith.All
public import RequestProject.EvenZero.All
public import RequestProject.FoldGroup.All
public import RequestProject.BaiCounts.All

/-!
# `C51_theorem_DW.md`: Part H (the fold law on every family) and Part D, (DW)

* (H) `H`: for every `lam ≥ 1` and every `i`,
  `XbarFam lam i ≃+ twoM (FamilyGroup.X (Families.ds lam) 1 i)`
  (C49c `ZeroSmith.C5` for odd `lam`, C50h `EvenZero.TT` for even `lam`).
* (DW) `DW`: Theorem DW, `Syl2 (KBar n) ≃+ twoM (Syl2 (K n))` for `n ≥ 1` (C38b `FoldGroup.P2`).
-/

@[expose] public section

noncomputable section

namespace FoldLaw

open CubeLaplacian Fold FoldGroup

/-- **(H)** of `C51_theorem_DW.md` (Part H, the fold law on every family): for every `lam ≥ 1`
and every `i`,
`Nonempty (FoldGroup.XbarFam lam i ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds lam) 1 i))`. -/
theorem H (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FoldGroup.XbarFam lam i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds lam) 1 i)) := by
  rcases Nat.even_or_odd lam with ⟨k, hk⟩ | ⟨l, hl⟩
  · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    have : lam = 2 * l + 2 := by omega
    subst this
    exact EvenZero.TT l i
  · subst hl
    exact ZeroSmith.C5 l i

/-- **(DW)** of `C51_theorem_DW.md` (Part D, Theorem DW): for every `n ≥ 1`,
`Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+
FoldGroup.twoM (CubeLaplacian.Syl2 (CubeLaplacian.K n)))`. -/
theorem DW (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+
      FoldGroup.twoM (CubeLaplacian.Syl2 (CubeLaplacian.K n))) :=
  FoldGroup.P2 H n hn

end FoldLaw
