module

public import RequestProject.SmallCases.PartS
public import RequestProject.SmallCases.PartT

/-!
# `C53_the_small_cases.md`: Part U — every `n` the paper states

* `DW'_all`, `L1_all`, `R_all`: Theorem DW′, (L1) and (R) for every `n ≥ 1` (the case `n = 1`
  from Part S, the case `n ≥ 2` from C51 `FoldLaw.DW'`, `FoldLaw.L1`, `FoldLaw.R`).
* `G1_all`: Gao et al.'s Theorem 4.1 for every `n ≥ 2` (the case `n = 2` from Part T, the case
  `n ≥ 3` from C36 `PodiumCor.G1`).
-/

@[expose] public section

noncomputable section

namespace SmallCases

/-- **`DW'_all`** of `C53_the_small_cases.md` (Part U): Theorem DW′ for every `n ≥ 1`.
`n = 1` is (DW'1) `DW'_one`; `n ≥ 2` is C51 `FoldLaw.DW'`. -/
theorem DW'_all (n : ℕ) (hn : 1 ≤ n) :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
        (Fin (BaiCounts.aN n) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h
  · exact DW'_one
  · exact FoldLaw.DW' n h

/-- **`L1_all`** of `C53_the_small_cases.md` (Part U): (L1) for every `n ≥ 1`.
`n = 1` is (L1-1) `L1_one`; `n ≥ 2` is C51 `FoldLaw.L1`. -/
theorem L1_all (n : ℕ) (hn : 1 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) =
      2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h
  · exact L1_one
  · exact FoldLaw.L1 n h

/-- **`R_all`** of `C53_the_small_cases.md` (Part U): (R) for every `n ≥ 1`.
`n = 1` is (R1) `R1`; `n ≥ 2` is C51 `FoldLaw.R`. -/
theorem R_all (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) = BaiCounts.aN n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h
  · exact R1
  · exact FoldLaw.R n h

/-- **`G1_all`** of `C53_the_small_cases.md` (Part U): `PodiumCor.G1` (Gao et al., Theorem 4.1)
for every `n ≥ 2`.  `n = 2` is (G1-2) `G1_two`; `n ≥ 3` is C36 `PodiumCor.G1`. -/
theorem G1_all (n : ℕ) (hn : 2 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (PodiumCor.gmax n) ((Rulers.v2 n : ℤ) + n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n - 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = PodiumCor.gmax n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | h
  · exact G1_two
  · exact PodiumCor.G1 n h

end SmallCases
