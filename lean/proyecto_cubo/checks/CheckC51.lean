import RequestProject.FoldLaw.All

/-! Auditor's check file for Lean piece C51: Theorem DW and its consequences
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C51_theorem_DW.md`;
then `#print axioms`. -/

-- (H) the fold law on every family
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FoldGroup.XbarFam lam i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds lam) 1 i)) := FoldLaw.H lam hlam i

-- (DW) Theorem DW
example (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+
      FoldGroup.twoM (CubeLaplacian.Syl2 (CubeLaplacian.K n))) := FoldLaw.DW n hn

-- (DW') the equivalent form
example (n : ℕ) (hn : 2 ≤ n) :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
        (Fin (BaiCounts.aN n) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H := FoldLaw.DW' n hn

-- (L0)
example (M : Type) [AddCommGroup M] :
    BaiCounts.l0 (FoldGroup.twoM M) = BaiCounts.l1 M := FoldLaw.L0 M

-- (L1)
example (n : ℕ) (hn : 2 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) =
      2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n) := FoldLaw.L1 n hn

-- (R) the F_2-rank of the folded Laplacian
example (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) =
      BaiCounts.aN n := FoldLaw.R n hn

-- aN as defined (C34), for the reader
example (n : ℕ) : BaiCounts.aN n = 2 ^ (n - 2) - 2 ^ ((n - 2) / 2) := rfl

#print axioms FoldLaw.H
#print axioms FoldLaw.DW
#print axioms FoldLaw.DW'
#print axioms FoldLaw.L0
#print axioms FoldLaw.L1
#print axioms FoldLaw.R
