module

public import RequestProject.EvenZero.Defs

/-!
# `C50h_theorem_10_22_at_zero.md`: Part M — any shift

(M0) `Ψ_0` is the arm at shift `0`; (M1′) one arm, any shift `c ≥ 1` (the proof of C50g `M1`, with
C46 `M5` applied to `XiOpZ 2 c η (fun m _ => z m)` directly).
-/

@[expose] public section

noncomputable section

namespace EvenZero

open FormalOps FormalDance

/-- **(M0)** of `C50h_theorem_10_22_at_zero.md` (`Ψ_0` is the arm at shift `0`):
`PsiC 0 = FoldOdd.PsiF 0` and `IsUnit (FoldOdd.kJ 0 1)`. -/
theorem M0 : PsiC 0 = FoldOdd.PsiF 0 ∧ IsUnit (FoldOdd.kJ 0 1) := by
  obtain ⟨⟨hPsi, hU, -, -⟩, -⟩ := FoldOdd.F5 0 0
  exact ⟨by rw [hPsi]; rfl, hU⟩

/-- **(M1′)** of `C50h_theorem_10_22_at_zero.md` (one arm, any shift `c ≥ 1`): let `l c : ℕ` with
`1 ≤ c`, `η : ℤ_[2]` with `IsUnit η`, `z : ℕ → ℤ_[2]`, `t : ℤ_[2]` with `t = 2 ∨ t = -2`, and put
`Ξ := Smith2.XiOpZ 2 c η (fun m _ => z m)`. Let `V : Bf ℤ_[2]` with
`(2 : ℤ_[2]) • V = Ξ * (Ξ + t • 1)`, and `Xk Vk` with
`DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Xk` and `DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`.
Then there is `W'` over `ℤ_[2]` with `IsUnit W'.det`, `‖((W' - 1) s s' : ℚ_[2])‖ ≤ 1 / 2` for all
`s s'`, and `finalM Vk = W' * finalM Xk`. -/
theorem M1' (l c : ℕ) (hc : 1 ≤ c) (η : ℤ_[2]) (hηu : IsUnit η) (z : ℕ → ℤ_[2]) (t : ℤ_[2])
    (ht : t = 2 ∨ t = -2) (V : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = Smith2.XiOpZ 2 c η (fun m _ => z m) *
      (Smith2.XiOpZ 2 c η (fun m _ => z m) + t • (1 : Bf ℤ_[2])))
    (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hXk : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ 2 c η (fun m _ => z m)) Xk)
    (hVk : DanceRel (Families.ds l) 1 (fun _ _ => V) Vk) :
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit W'.det ∧ (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
        finalM Vk = W' * finalM Xk := by
  have hP0 : Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
      (Smith2.XiOpZ 2 c η (fun m _ => z m)) =
      PathSum.XiOp 2 c ((η : ℤ_[2]) : ℚ_[2]) (fun m _ => ((z m : ℤ_[2]) : ℚ_[2])) :=
    (Smith2.M5 2 c η (fun m _ => z m)).1
  have hη : ‖((η : ℤ_[2]) : ℚ_[2])‖ = 1 := by
    rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp hηu
  have hζ : ∀ m, ‖((z m : ℤ_[2]) : ℚ_[2])‖ ≤ 1 := fun m => by
    rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
  have hP1 := EvenFold.P1 _ V t hV
  rw [hP0] at hP1
  have htn : ‖((t : ℤ_[2]) : ℚ_[2])‖ = 1 / 2 := by
    rcases ht with rfl | rfl
    · simpa using PathSum.norm_two_padic
    · simpa using PathSum.norm_two_padic
  obtain ⟨-, hM4d, hM4f⟩ := Smith2.M4 (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
  have hGΨ : DanceRel (Families.ds l) 1 (fun _ _ =>
      Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
        (Smith2.XiOpZ 2 c η (fun m _ => z m))) _ :=
    hM4d _ _ _ _ hXk
  have hGU : DanceRel (Families.ds l) 1 (fun _ _ =>
      Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) V) _ :=
    hM4d _ _ _ _ hVk
  rw [hP0] at hGΨ
  rw [hP1] at hGU
  obtain ⟨Y, hY1, hY2⟩ := Conjugation.I (PathSum.XiOp 2 c
    ((η : ℤ_[2]) : ℚ_[2]) (fun m _ => ((z m : ℤ_[2]) : ℚ_[2])))
    (fun f hf => by rw [PathSum.XiOp_coef_zero]; exact PathSum.piF_ne_zero hc hf)
  obtain ⟨-, -, Yt, hYt1, hYt2⟩ := Bend.Y0 (le_refl 2) hη (fun m _ f => hζ m) htn
  have hB : l + 1 ≤ l + 1 := le_rfl
  obtain ⟨hfin, -, -, -⟩ := BendCor.W2 hB (le_refl 2) hc hη (fun m _ f => hζ m) htn Y Yt
    hY1 hY2 hYt1 hYt2 _ _ hGΨ hGU
  obtain ⟨W', hW'map, hW'u, hW'b⟩ := BendCor.W3 hB (le_refl 2) hc hη (fun m _ f => hζ m) htn
    Y Yt hY1 hY2 hYt1 hYt2 _ _ hGΨ hGU
  refine ⟨W', hW'u, fun s s' => by rw [EvenFold.coe_sub_one_apply]; exact hW'b s s', ?_⟩
  rw [hM4f] at hW'map
  rw [hM4f, hM4f, ← hW'map] at hfin
  have hinj : Function.Injective (fun z : ℤ_[2] => (z : ℚ_[2])) := Subtype.coe_injective
  apply Matrix.map_injective hinj
  change (finalM Vk).map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) =
    (W' * finalM Xk).map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
  rw [hfin, Matrix.map_mul]
  rfl

end EvenZero
