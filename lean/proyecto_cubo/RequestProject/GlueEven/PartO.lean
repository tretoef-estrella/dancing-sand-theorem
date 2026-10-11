module

public import RequestProject.GlueEven.PartS

/-!
# `C50f_the_glued_system_on_T.md`: Part O — the arms on `T(l)`

(O1) the lower-left arm `ZF i` of the fold side: `2 • ZF i = PsiF i − PsiF (i + 1)`, and `ZF i`
acts on `T(l)` as `Zop (l + i)`; (O2) the cube side: halves `U`, `U'`, `ZU` of
`PsiF (i+1) (PsiF (i+1) − 2)`, `PsiF i (PsiF i + 2)` and `U' − U` act as `thX − thY`, `thX + thY`
and `thY`.
-/

@[expose] public section

noncomputable section

namespace GlueEven

open FormalOps FormalAct FormalDance

/-- Helper for (O2) of `C50f_the_glued_system_on_T.md`: operators on `V → ℤ_[2]` have no
`2`-torsion. -/
lemma two_smul_cancel {V : Type*} {f g : Module.End ℤ_[2] (V → ℤ_[2])}
    (h : (2 : ℤ_[2]) • f = (2 : ℤ_[2]) • g) : f = g :=
  LinearMap.ext fun v => funext fun j => by
    have := congrFun (LinearMap.congr_fun h v) j
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ two_ne_zero this

/-- Helper for (O1) of `C50f_the_glued_system_on_T.md`: the first identity, coefficientwise. -/
lemma two_smul_ZF (i : ℕ) :
    (2 : ℤ_[2]) • ZF i = FoldOdd.PsiF i - FoldOdd.PsiF (i + 1) := by
  ext m f
  have hk := ArmsEven.kJ_succ_sub i m
  simp only [ZF, FoldOdd.PsiF, Bf.coef_smul, Bf.coef_sub, Bf.coef_neg, Bf.coef_one,
    Bf.coef_add, Bf.coef_dg, FoldOdd.coef_KF, FoldOdd.ShInvF, FoldOdd.coef_cst]
  split_ifs <;> push_cast <;> linear_combination hk

/-- **(O1)** of `C50f_the_glued_system_on_T.md` (the lower-left arm of the fold side): for
`l i B : ℕ` with `l + 1 ≤ B`, `(2 : ℤ_[2]) • ZF i = PsiF i - PsiF (i + 1)` and
`act (T l) l B (ZF i) = Zop (T l) (l + i) (l + 1)`. -/
theorem O1 (l i B : ℕ) (hB : l + 1 ≤ B) :
    (2 : ℤ_[2]) • ZF i = FoldOdd.PsiF i - FoldOdd.PsiF (i + 1) ∧
    act (Filt.T ℤ_[2] l) (l : ℤ) B (ZF i) =
      FoldHalf.Zop (Filt.T ℤ_[2] l) ((l : ℤ) + i) (l + 1) := by
  refine ⟨two_smul_ZF i, ?_⟩
  have hnil := (FoldHalf.A3 ℤ_[2] l).2
  have hB1 : 1 ≤ B := by omega
  obtain ⟨-, -, hShInv⟩ := FoldOdd.F3 (Filt.T ℤ_[2] l) (l : ℤ) (l + 1) B hnil hB hB1
  rw [ZF, act_sub', act_smul, hShInv, FoldHalf.Zop, FoldOdd.parOp_T, smul_mul_assoc, one_mul,
    show act (Filt.T ℤ_[2] l) (l : ℤ) B (-(1 : Bf ℤ_[2])) = -1 by
      rw [show (-(1 : Bf ℤ_[2])) = 0 - 1 by rw [zero_sub], act_sub', act_zero', act_one hB1,
        zero_sub]]

/-- Helper for (O2) of `C50f_the_glued_system_on_T.md`: `act (Ψ * (Ψ + t • 1))` on `T(l)`. -/
lemma act_psi_mul (l j B : ℕ) (hB : l + 1 ≤ B) (t : ℤ_[2]) :
    act (Filt.T ℤ_[2] l) (l : ℤ) B (FoldOdd.PsiF j * (FoldOdd.PsiF j + t • (1 : Bf ℤ_[2]))) =
      FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1) *
        (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1) + t • 1) := by
  have hnil := (FoldHalf.A3 ℤ_[2] l).2
  have hB1 : 1 ≤ B := by omega
  rw [act_mul hnil hB, act_add, act_smul, act_one hB1, (FoldOdd.F4 l j 0 B hB).1]

/-- Helper for (O2) of `C50f_the_glued_system_on_T.md`: `act (Ψ * (Ψ - t • 1))` on `T(l)`. -/
lemma act_psi_mul_sub (l j B : ℕ) (hB : l + 1 ≤ B) (t : ℤ_[2]) :
    act (Filt.T ℤ_[2] l) (l : ℤ) B (FoldOdd.PsiF j * (FoldOdd.PsiF j - t • (1 : Bf ℤ_[2]))) =
      FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1) *
        (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1) - t • 1) := by
  have hnil := (FoldHalf.A3 ℤ_[2] l).2
  have hB1 : 1 ≤ B := by omega
  rw [act_mul hnil hB, act_sub', act_smul, act_one hB1, (FoldOdd.F4 l j 0 B hB).1]

/-- **(O2)** of `C50f_the_glued_system_on_T.md` (the cube side): for `l i B : ℕ` with
`l + 1 ≤ B` and `U U' ZU : Bf ℤ_[2]` with `2 • U = PsiF (i + 1) * (PsiF (i + 1) - 2 • 1)`,
`2 • U' = PsiF i * (PsiF i + 2 • 1)` and `Agree (U' - U) (2 • ZU)`, writing
`thX = FoldCube.thX (T l) (l + 1) (l + i) (2 * l + 2)` and `thY` likewise:
`act (T l) l B U = thX - thY`, `act (T l) l B U' = thX + thY` and `act (T l) l B ZU = thY`. -/
theorem O2 (l i B : ℕ) (hB : l + 1 ≤ B) (U U' ZU : Bf ℤ_[2])
    (hU : (2 : ℤ_[2]) • U =
      FoldOdd.PsiF (i + 1) * (FoldOdd.PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hU' : (2 : ℤ_[2]) • U' = FoldOdd.PsiF i * (FoldOdd.PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hZU : Agree (U' - U) ((2 : ℤ_[2]) • ZU)) :
    act (Filt.T ℤ_[2] l) (l : ℤ) B U =
        FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) -
          FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) ∧
      act (Filt.T ℤ_[2] l) (l : ℤ) B U' =
        FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) +
          FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) ∧
      act (Filt.T ℤ_[2] l) (l : ℤ) B ZU =
        FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) := by
  have hnil := (FoldHalf.A3 ℤ_[2] l).2
  obtain ⟨-, hplus, hminus⟩ := FoldCube.V3c (Filt.T ℤ_[2] l) (l + 1) hnil ((l : ℤ) + i)
    (2 * l + 2) (by omega)
  have h2 : (2 : ℤ_[2]) • (1 : Module.End ℤ_[2] ((Filt.T ℤ_[2] l).ι → ℤ_[2])) = 2 := by
    rw [two_smul, one_add_one_eq_two]
  set X := FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2)
  set Y := FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2)
  have hA : act (Filt.T ℤ_[2] l) (l : ℤ) B U = X - Y := by
    apply two_smul_cancel
    have hc : ((l : ℤ) + ((i + 1 : ℕ) : ℤ)) = (l : ℤ) + i + 1 := by push_cast; ring
    rw [← act_smul, hU, act_psi_mul_sub l (i + 1) B hB, hminus, hc, h2, mul_sub, sub_mul, mul_two, two_mul]
  have hA' : act (Filt.T ℤ_[2] l) (l : ℤ) B U' = X + Y := by
    apply two_smul_cancel
    rw [← act_smul, hU', act_psi_mul l i B hB, hplus, h2]
  refine ⟨hA, hA', ?_⟩
  apply two_smul_cancel
  have htop := (FormalAct.N2 (A := ℤ_[2]) l).1
  rw [← act_smul, ← C4 htop hZU B, act_sub', hA, hA']
  rw [two_smul]
  abel

end GlueEven
