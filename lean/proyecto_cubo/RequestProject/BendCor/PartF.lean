module

public import RequestProject.BendCor.PartA

/-!
# `C50e_corollary_10_21.md`: Part F — the final matrices

* (F1) `F1`: `(finalM GU)⁻¹ = (2 / t) • ((finalM GΨ)⁻¹ - Nmat l B Y_t)`, by C50d `Nmat_eq_inv`
  twice (for `Ψ` with `Y`, and for `UOp Ψ t` with `(2/t) • (Y − Y_t)` by (A1)) and (A2).
* (F2) `F2`: `IsUnit (1 - E).det` and `finalM GU = ((t / 2) • (1 - E)⁻¹) * finalM GΨ`, with
  `E = finalM GΨ * Nmat l B Y_t` (C42 `C109` for both final matrices).
-/

@[expose] public section

noncomputable section

namespace BendCor

open FormalOps FormalDance

/-- **(F1)** of `C50e_corollary_10_21.md`: let `l + 1 ≤ B`, `Ψ Y Y_t : Bf ℚ_[2]`, `t ≠ 0` with
`Agree (Ψ * Y) 1`, `Agree (Y * Ψ) 1`, `Agree ((Ψ + t • 1) * Y_t) 1`,
`Agree (Y_t * (Ψ + t • 1)) 1`, and let `GΨ`, `GU` satisfy
`DanceRel (Families.ds l) 1 (fun _ _ => Ψ) GΨ` and
`DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ t) GU`. Then
`(finalM GU)⁻¹ = (2 / t) • ((finalM GΨ)⁻¹ - Bend.Nmat l B Y_t)`. -/
theorem F1 {l B : ℕ} (hB : l + 1 ≤ B) (Ψ Y Yt : Bf ℚ_[2]) {t : ℚ_[2]} (ht : t ≠ 0)
    (h1 : Agree (Ψ * Y) 1) (h2 : Agree (Y * Ψ) 1)
    (h3 : Agree ((Ψ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (Ψ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => Ψ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ t) GU) :
    (finalM GU)⁻¹ = (2 / t) • ((finalM GΨ)⁻¹ - Bend.Nmat l B Yt) := by
  obtain ⟨hU1, hU2⟩ := A1 Ψ Y Yt ht h1 h2 h3 h4
  rw [← Bend.Nmat_eq_inv l B hB _ _ hU1 hU2 GU hGU, (A2 l B (Y - Yt) Yt (2 / t)).2.2,
    (A2 l B Y Yt 0).2.1, Bend.Nmat_eq_inv l B hB Ψ Y h1 h2 GΨ hGΨ]

/-- **(F2)** of `C50e_corollary_10_21.md`: in the setting of (F1), with
`E := finalM GΨ * Bend.Nmat l B Y_t`, `IsUnit (1 - E).det` and
`finalM GU = ((t / 2) • (1 - E)⁻¹) * finalM GΨ`. -/
theorem F2 {l B : ℕ} (hB : l + 1 ≤ B) (Ψ Y Yt : Bf ℚ_[2]) {t : ℚ_[2]} (ht : t ≠ 0)
    (h1 : Agree (Ψ * Y) 1) (h2 : Agree (Y * Ψ) 1)
    (h3 : Agree ((Ψ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (Ψ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => Ψ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ t) GU) :
    IsUnit (1 - finalM GΨ * Bend.Nmat l B Yt).det ∧
      finalM GU = ((t / 2) • (1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹) * finalM GΨ := by
  obtain ⟨hU1, hU2⟩ := A1 Ψ Y Yt ht h1 h2 h3 h4
  have hM := (InvFloors.C109 l B hB Ψ Y h1 h2 GΨ hGΨ).1
  have hMU := (InvFloors.C109 l B hB _ _ hU1 hU2 GU hGU).1
  have hF1 := F1 hB Ψ Y Yt ht h1 h2 h3 h4 GΨ GU hGΨ hGU
  set M := finalM GΨ
  set MU := finalM GU
  set E := M * Bend.Nmat l B Yt
  have key : M * MU⁻¹ = (2 / t) • (1 - E) := by
    rw [hF1, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_nonsing_inv M hM]
  have hc : t / 2 * (2 / t) = 1 := by field_simp
  have h1E : 1 - E = (t / 2) • (M * MU⁻¹) := by
    rw [key, smul_smul, hc, one_smul]
  have hunit : IsUnit (1 - E).det := by
    rw [h1E, Matrix.det_smul, Matrix.det_mul]
    refine (IsUnit.pow _ ?_).mul (hM.mul (Matrix.isUnit_nonsing_inv_det MU hMU))
    rw [isUnit_iff_ne_zero]
    exact div_ne_zero ht two_ne_zero
  refine ⟨hunit, ?_⟩
  have hA : ((t / 2) • (1 - E)⁻¹ * M) * MU⁻¹ = 1 := by
    rw [Matrix.mul_assoc, key, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul,
      Matrix.nonsing_inv_mul _ hunit]
  calc MU = ((t / 2) • (1 - E)⁻¹ * M) * MU⁻¹ * MU := by rw [hA, Matrix.one_mul]
    _ = (t / 2) • (1 - E)⁻¹ * M := by
      rw [Matrix.mul_assoc _ MU⁻¹, Matrix.nonsing_inv_mul _ hMU, Matrix.mul_one]

end BendCor
