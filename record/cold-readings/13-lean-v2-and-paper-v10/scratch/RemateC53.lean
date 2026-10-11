import RequestProject.SmallCases.All

/-! Grepy Remate's own check of C53. Typed by hand from `C53_the_small_cases.md`, Part T (T0) and Part U.
Universe-polymorphic (S3) as a bonus. -/

universe u

-- (T0)
example : Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 2) ≃+ ZMod 4) := SmallCases.T0

-- (S3) at an arbitrary universe
example (A : Type u) [CommRing A] : Fold.lapBar A 1 = 0 := SmallCases.S3 A

-- DW'_all
example : ∀ n : ℕ, 1 ≤ n →
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+ (Fin (BaiCounts.aN n) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H :=
  fun n hn => SmallCases.DW'_all n hn

-- L1_all
example : ∀ n : ℕ, 1 ≤ n →
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) = 2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n) :=
  fun n hn => SmallCases.L1_all n hn

-- R_all
example : ∀ n : ℕ, 1 ≤ n →
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) = BaiCounts.aN n :=
  fun n hn => SmallCases.R_all n hn

-- G1_all, with the type of r written out
example : ∀ n : ℕ, 2 ≤ n →
    ((PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℕ) : ℤ) =
        max (PodiumCor.gmax n) ((Rulers.v2 n : ℤ) + (n : ℤ) - 1) ∧
      ∀ r : ℕ, 2 ≤ r → r ≤ n - 1 →
        ((PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℕ) : ℤ) = PodiumCor.gmax n :=
  fun n hn => SmallCases.G1_all n hn

-- the special cases recovered from the _all forms
example : BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar 1)) = 1 := by
  have h := SmallCases.L1_all 1 le_rfl
  rw [SmallCases.S0] at h
  simpa using h

-- the old hypotheses, as Lean prints them
#check @FoldLaw.DW
#check @FoldLaw.DW'
#check @FoldLaw.L1
#check @FoldLaw.R
#check @PodiumCor.G1
#check @PodiumCor.gmax_two
#check @SmallCases.G1_all
#check @SmallCases.S3

#print axioms SmallCases.T0
#print axioms SmallCases.S3
#print axioms SmallCases.DW'_all
#print axioms SmallCases.L1_all
#print axioms SmallCases.R_all
#print axioms SmallCases.G1_all
