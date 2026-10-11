module

public import RequestProject.Smith2.All
public import RequestProject.FoldOdd.All
public import RequestProject.BendCor.All

/-!
# `C50g_theorem_10_22_for_i_positive.md`: Part P — the arms over `ℚ_[2]`

Folder `RequestProject/EvenFold/`, namespace `EvenFold`. The file adds no definition; nothing listed
in its Setting is redefined. Throughout, `ι` is `PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]` and
`Φ := Smith2.Bf.map ι` (both written out in full in the statements).

(P0) `Ψ_j` over `ℚ_[2]`; (P1) the halves over `ℚ_[2]`.
-/

@[expose] public section

noncomputable section

namespace EvenFold

open FormalOps

/-- **(P0)** of `C50g_theorem_10_22_for_i_positive.md` (`Ψ_j` over `ℚ_[2]`): for every `j`,
`Φ (FoldOdd.PsiF j) = PathSum.XiOp 2 ((j + 1) / 2) (kJ j 1 : ℚ_[2]) (fun m _ => (kJ j m : ℚ_[2]))`,
`‖(kJ j 1 : ℚ_[2])‖ = 1`, and `‖(kJ j m : ℚ_[2])‖ ≤ 1` for all `m`. -/
theorem P0 (j : ℕ) :
    Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) (FoldOdd.PsiF j) =
      PathSum.XiOp 2 ((j + 1) / 2) ((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2])
        (fun m _ => ((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2])) ∧
    ‖((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2])‖ = 1 ∧
    ∀ m, ‖((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2])‖ ≤ 1 := by
  obtain ⟨⟨hPsi, hU, -, -⟩, -⟩ := FoldOdd.F5 j 0
  refine ⟨?_, ?_, fun m => ?_⟩
  · rw [hPsi]
    exact (Smith2.M5 2 ((j + 1) / 2) (FoldOdd.kJ j 1) (fun m _ => FoldOdd.kJ j m)).1
  · rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp hU
  · rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _

/-- **(P1)** of `C50g_theorem_10_22_for_i_positive.md` (the halves over `ℚ_[2]`): for
`X V : Bf ℤ_[2]` and `t : ℤ_[2]` with `(2 : ℤ_[2]) • V = X * (X + t • 1)`:
`Φ V = BendCor.UOp (Φ X) (t : ℚ_[2])`. -/
theorem P1 (X V : Bf ℤ_[2]) (t : ℤ_[2])
    (h : (2 : ℤ_[2]) • V = X * (X + t • (1 : Bf ℤ_[2]))) :
    Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) V =
      BendCor.UOp (Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) X)
        ((t : ℤ_[2]) : ℚ_[2]) := by
  set φ := (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
  have h2 := congrArg (Smith2.Bf.map φ) h
  rw [Smith2.Bf.map_smul, Smith2.Bf.map_mul, Smith2.Bf.map_add, Smith2.Bf.map_smul,
    Smith2.Bf.map_one, map_ofNat] at h2
  change _ = (1 / 2 : ℚ_[2]) • (Smith2.Bf.map φ X * (Smith2.Bf.map φ X + φ t • (1 : Bf ℚ_[2])))
  rw [← h2, smul_smul]
  norm_num

end EvenFold
