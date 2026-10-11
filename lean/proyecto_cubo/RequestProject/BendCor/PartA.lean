module

public import RequestProject.BendCor.Defs

/-!
# `C50e_corollary_10_21.md`: Part A — partial fractions

* (A0) `A0`: `t • 1` is central, and `Ψ` commutes with `Ψ + t • 1`.
* (A1) `A1`: `(2/t) • (Y − Y_t)` inverts `UOp Ψ t` on both sides.
* (A2) `A2`: `Bend.Nmat l B` is linear in `Y` (for all `l B`, through C40c `sysAct_add`,
  `sysAct_sub`, `sysAct_smul`).
-/

@[expose] public section

noncomputable section

namespace BendCor

open FormalOps FormalDance FormalAct Filt

/-- **(A0)** of `C50e_corollary_10_21.md` (`t • 1` is central): for `t : ℚ_[2]` and
`x : Bf ℚ_[2]`, `(t • 1) * x = x * (t • 1)`; also `Ψ * (Ψ + t • 1) = (Ψ + t • 1) * Ψ`. -/
theorem A0 (t : ℚ_[2]) :
    (∀ x : Bf ℚ_[2], (t • (1 : Bf ℚ_[2])) * x = x * (t • (1 : Bf ℚ_[2]))) ∧
      ∀ Ψ : Bf ℚ_[2], Ψ * (Ψ + t • (1 : Bf ℚ_[2])) = (Ψ + t • (1 : Bf ℚ_[2])) * Ψ := by
  have h : ∀ x : Bf ℚ_[2], (t • (1 : Bf ℚ_[2])) * x = x * (t • (1 : Bf ℚ_[2])) := fun x => by
    rw [Bf.smul_mul, Bf.mul_smul, one_mul, mul_one]
  exact ⟨h, fun Ψ => by rw [mul_add, add_mul, h Ψ]⟩

/-- **(A1)** of `C50e_corollary_10_21.md` (the inverse of `U_t`): for `Ψ Y Y_t : Bf ℚ_[2]` and
`t ≠ 0` with `Agree (Ψ * Y) 1`, `Agree (Y * Ψ) 1`, `Agree ((Ψ + t • 1) * Y_t) 1` and
`Agree (Y_t * (Ψ + t • 1)) 1`: `Agree (UOp Ψ t * ((2 / t) • (Y - Y_t))) 1` and
`Agree (((2 / t) • (Y - Y_t)) * UOp Ψ t) 1`. -/
theorem A1 (Ψ Y Yt : Bf ℚ_[2]) {t : ℚ_[2]} (ht : t ≠ 0) (h1 : Agree (Ψ * Y) 1)
    (h2 : Agree (Y * Ψ) 1) (h3 : Agree ((Ψ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (Ψ + t • (1 : Bf ℚ_[2]))) 1) :
    Agree (UOp Ψ t * ((2 / t) • (Y - Yt))) 1 ∧ Agree (((2 / t) • (Y - Yt)) * UOp Ψ t) 1 := by
  have hcomm := (A0 t).2 Ψ
  have hfin : (2 / t : ℚ_[2]) • ((1 / 2 : ℚ_[2]) • (Ψ + t • (1 : Bf ℚ_[2])) -
      (1 / 2 : ℚ_[2]) • Ψ) = 1 := by
    rw [← smul_sub, add_sub_cancel_left, smul_smul, smul_smul,
      show (2 / t * (1 / 2) * t : ℚ_[2]) = 1 by field_simp, one_smul]
  refine ⟨?_, ?_⟩
  · have e1 : UOp Ψ t * Y = (1 / 2 : ℚ_[2]) • ((Ψ + t • (1 : Bf ℚ_[2])) * (Ψ * Y)) := by
      rw [UOp, hcomm, smul_mul_assoc, mul_assoc]
    have e2 : UOp Ψ t * Yt = (1 / 2 : ℚ_[2]) • (Ψ * ((Ψ + t • (1 : Bf ℚ_[2])) * Yt)) := by
      rw [UOp, smul_mul_assoc, mul_assoc]
    rw [mul_smul_comm, mul_sub, e1, e2]
    refine Agree.trans (Agree.smul _ (Agree.sub (Agree.smul _ ?_) (Agree.smul _ ?_)))
      (Agree.of_eq hfin)
    · simpa using Agree.mul (Agree.refl (Ψ + t • (1 : Bf ℚ_[2]))) h1
    · simpa using Agree.mul (Agree.refl Ψ) h3
  · have e1 : Y * UOp Ψ t = (1 / 2 : ℚ_[2]) • ((Y * Ψ) * (Ψ + t • (1 : Bf ℚ_[2]))) := by
      rw [UOp, mul_smul_comm, mul_assoc]
    have e2 : Yt * UOp Ψ t = (1 / 2 : ℚ_[2]) • ((Yt * (Ψ + t • (1 : Bf ℚ_[2]))) * Ψ) := by
      rw [UOp, hcomm, mul_smul_comm, mul_assoc]
    rw [smul_mul_assoc, sub_mul, e1, e2]
    refine Agree.trans (Agree.smul _ (Agree.sub (Agree.smul _ ?_) (Agree.smul _ ?_)))
      (Agree.of_eq hfin)
    · simpa using Agree.mul h2 (Agree.refl (Ψ + t • (1 : Bf ℚ_[2])))
    · simpa using Agree.mul h4 (Agree.refl Ψ)

/-- **(A2)** of `C50e_corollary_10_21.md` (`Nmat` is linear): for all `l B`, `Y Y'` and
`a : ℚ_[2]`, `Nmat l B (Y + Y') = Nmat l B Y + Nmat l B Y'`,
`Nmat l B (Y - Y') = Nmat l B Y - Nmat l B Y'` and `Nmat l B (a • Y) = a • Nmat l B Y`
(no hypothesis on `B` is needed). -/
theorem A2 (l B : ℕ) (Y Y' : Bf ℚ_[2]) (a : ℚ_[2]) :
    Bend.Nmat l B (Y + Y') = Bend.Nmat l B Y + Bend.Nmat l B Y' ∧
      Bend.Nmat l B (Y - Y') = Bend.Nmat l B Y - Bend.Nmat l B Y' ∧
      Bend.Nmat l B (a • Y) = a • Bend.Nmat l B Y := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j
  · have : (fun _ _ => Y + Y' : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) =
        (fun _ _ => Y) + (fun _ _ => Y') := rfl
    rw [Bend.Nmat_apply, Matrix.add_apply, Bend.Nmat_apply, Bend.Nmat_apply, this, sysAct_add,
      LinearMap.add_apply, map_add, Pi.add_apply, mul_add]
  · have : (fun _ _ => Y - Y' : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) =
        (fun _ _ => Y) - (fun _ _ => Y') := rfl
    rw [Bend.Nmat_apply, Matrix.sub_apply, Bend.Nmat_apply, Bend.Nmat_apply, this, sysAct_sub,
      LinearMap.sub_apply, map_sub, Pi.sub_apply, mul_sub]
  · have : (fun _ _ => a • Y : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) =
        a • (fun _ _ => Y : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) := rfl
    rw [Bend.Nmat_apply, Matrix.smul_apply, Bend.Nmat_apply, this, sysAct_smul,
      LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

end BendCor
