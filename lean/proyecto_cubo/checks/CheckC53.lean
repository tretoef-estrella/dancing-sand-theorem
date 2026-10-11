import RequestProject.SmallCases.All

/-! Auditor's check file for Lean piece C53: the small cases (Grepy Escribano, 11 Oct 2026).
Restated by hand from `C53_the_small_cases.md`; then `#print axioms`.
The item (L1-1) of the piece is the Lean name `SmallCases.L1_one` (a Lean name cannot contain `-`). -/

-- Part S, n = 1
-- (S0)
example : BaiCounts.aN 1 = 0 := SmallCases.S0

-- (S1)
example : Subsingleton (CubeLaplacian.Syl2 (CubeLaplacian.K 1)) := SmallCases.S1

-- (S2)
example : Subsingleton (CubeLaplacian.Syl2 (Fold.KBar 1)) := SmallCases.S2

-- (S3)
example (A : Type) [CommRing A] : Fold.lapBar A 1 = 0 := SmallCases.S3 A

-- (DW'1)
example :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 1) ≃+
        (Fin (BaiCounts.aN 1) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar 1) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H := SmallCases.DW'_one

-- (L1-1)
example :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar 1)) =
      2 ^ (2 ^ (1 - 1) - 1 - BaiCounts.aN 1) := SmallCases.L1_one

-- (R1)
example :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) 1)) = BaiCounts.aN 1 :=
  SmallCases.R1

-- Part T, n = 2
-- (T0)
example : Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 2) ≃+ ZMod 4) := SmallCases.T0

-- (T1)
example : PodiumCor.gmax 2 = 1 := SmallCases.T1

-- (G1-2)
example :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 2)) 1 : ℤ) =
        max (PodiumCor.gmax 2) ((Rulers.v2 2 : ℤ) + 2 - 1) ∧
      ∀ r, 2 ≤ r → r ≤ 2 - 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 2)) r : ℤ) = PodiumCor.gmax 2 :=
  SmallCases.G1_two

-- Part U, every n the paper states
example (n : ℕ) (hn : 1 ≤ n) :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
        (Fin (BaiCounts.aN n) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H := SmallCases.DW'_all n hn

example (n : ℕ) (hn : 1 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) =
      2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n) := SmallCases.L1_all n hn

example (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) = BaiCounts.aN n :=
  SmallCases.R_all n hn

example (n : ℕ) (hn : 2 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (PodiumCor.gmax n) ((Rulers.v2 n : ℤ) + n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n - 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = PodiumCor.gmax n :=
  SmallCases.G1_all n hn

#print axioms SmallCases.S0
#print axioms SmallCases.S1
#print axioms SmallCases.S2
#print axioms SmallCases.S3
#print axioms SmallCases.DW'_one
#print axioms SmallCases.L1_one
#print axioms SmallCases.R1
#print axioms SmallCases.T0
#print axioms SmallCases.T1
#print axioms SmallCases.G1_two
#print axioms SmallCases.DW'_all
#print axioms SmallCases.L1_all
#print axioms SmallCases.R_all
#print axioms SmallCases.G1_all
