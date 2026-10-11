module

public import RequestProject.EvenFold.PartP
public import RequestProject.GlueEven.All
public import RequestProject.Bend.All
public import RequestProject.Conjugation.All

/-!
# `C50g_theorem_10_22_for_i_positive.md`: Part M — the final matrices

(M1) one arm; (M2) the glue. Notation as in `PartP.lean`; `h21 : (2 : ℕ) = 2 * 1` is an argument
of (M2) (any two proofs of it are equal).
-/

@[expose] public section

noncomputable section

namespace EvenFold

open FormalOps FormalDance

/-- Auxiliary for (M1) and (M2) of `C50g_theorem_10_22_for_i_positive.md`: the coercion of an
entry of `W - 1` over `ℤ_[2]` is the entry of `W.map coe - 1` over `ℚ_[2]`. -/
lemma coe_sub_one_apply {n : Type*} [DecidableEq n] (W : Matrix n n ℤ_[2]) (s s' : n) :
    (((W - 1) s s' : ℤ_[2]) : ℚ_[2]) =
      ((W s s' : ℤ_[2]) : ℚ_[2]) - (1 : Matrix n n ℚ_[2]) s s' := by
  rw [Matrix.sub_apply, PadicInt.coe_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- **(M1)** of `C50g_theorem_10_22_for_i_positive.md` (one arm): let `l j : ℕ` with `1 ≤ j`,
`t : ℤ_[2]` with `t = 2 ∨ t = -2`, `V : Bf ℤ_[2]` with
`(2 : ℤ_[2]) • V = FoldOdd.PsiF j * (FoldOdd.PsiF j + t • 1)`, and `Xk Vk` with
`DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF j) Xk` and
`DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`. Then there is `W'` over `ℤ_[2]` with
`IsUnit W'.det`, `‖((W' - 1) s s' : ℚ_[2])‖ ≤ 1 / 2` for all `s s'`, and
`finalM Vk = W' * finalM Xk`. -/
theorem M1 (l j : ℕ) (hj : 1 ≤ j) (t : ℤ_[2]) (ht : t = 2 ∨ t = -2) (V : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = FoldOdd.PsiF j * (FoldOdd.PsiF j + t • (1 : Bf ℤ_[2])))
    (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hXk : DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF j) Xk)
    (hVk : DanceRel (Families.ds l) 1 (fun _ _ => V) Vk) :
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit W'.det ∧ (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
        finalM Vk = W' * finalM Xk := by
  obtain ⟨hP0, hη, hζ⟩ := P0 j
  have hP1 := P1 _ V t hV
  rw [hP0] at hP1
  have hc : 1 ≤ (j + 1) / 2 := by omega
  have htn : ‖((t : ℤ_[2]) : ℚ_[2])‖ = 1 / 2 := by
    rcases ht with rfl | rfl
    · simpa using PathSum.norm_two_padic
    · simpa using PathSum.norm_two_padic
  obtain ⟨-, hM4d, hM4f⟩ := Smith2.M4 (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
  have hGΨ : DanceRel (Families.ds l) 1 (fun _ _ =>
      Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) (FoldOdd.PsiF j)) _ :=
    hM4d _ _ _ _ hXk
  have hGU : DanceRel (Families.ds l) 1 (fun _ _ =>
      Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) V) _ :=
    hM4d _ _ _ _ hVk
  rw [hP0] at hGΨ
  rw [hP1] at hGU
  obtain ⟨Y, hY1, hY2⟩ := Conjugation.I (PathSum.XiOp 2 ((j + 1) / 2)
    ((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2]) (fun m _ => ((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2])))
    (fun f hf => by rw [PathSum.XiOp_coef_zero]; exact PathSum.piF_ne_zero hc hf)
  obtain ⟨-, -, Yt, hYt1, hYt2⟩ := Bend.Y0 (le_refl 2) hη (fun m _ f => hζ m) htn
  have hB : l + 1 ≤ l + 1 := le_rfl
  obtain ⟨hfin, -, -, -⟩ := BendCor.W2 hB (le_refl 2) hc hη (fun m _ f => hζ m) htn Y Yt
    hY1 hY2 hYt1 hYt2 _ _ hGΨ hGU
  obtain ⟨W', hW'map, hW'u, hW'b⟩ := BendCor.W3 hB (le_refl 2) hc hη (fun m _ f => hζ m) htn
    Y Yt hY1 hY2 hYt1 hYt2 _ _ hGΨ hGU
  refine ⟨W', hW'u, fun s s' => by rw [coe_sub_one_apply]; exact hW'b s s', ?_⟩
  rw [hM4f] at hW'map
  rw [hM4f, hM4f, ← hW'map] at hfin
  have hinj : Function.Injective (fun z : ℤ_[2] => (z : ℚ_[2])) := Subtype.coe_injective
  apply Matrix.map_injective hinj
  change (finalM Vk).map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) =
    (W' * finalM Xk).map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
  rw [hfin, Matrix.map_mul]
  rfl

/-- Auxiliary for (M2) of `C50g_theorem_10_22_for_i_positive.md` (C50 `D3`, read as matrices):
the final matrix of the glued dance is `gS (finalM Xk) (finalM Yk) (finalM Zk)` read through
`gE (S4 …)`, and `2 • finalM Zk = finalM Yk - finalM Xk`. -/
lemma finalM_glueC (h21 : (2 : ℕ) = 2 * 1) (l : ℕ)
    (Xk Yk Zk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hZ : MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)) :
    finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk) =
      (BendCor.gS (finalM Xk) (finalM Yk) (finalM Zk)).submatrix
        (GlueDance.gE (GlueDance.S4 (Families.ds l) h21)).symm
        (GlueDance.gE (GlueDance.S4 (Families.ds l) h21)).symm ∧
    2 • finalM Zk = finalM Yk - finalM Xk := by
  set E := GlueDance.gE (GlueDance.S4 (Families.ds l) h21)
  refine ⟨?_, ?_⟩
  · ext i j
    obtain ⟨⟨g, s⟩, rfl⟩ := E.surjective i
    obtain ⟨⟨g', s'⟩, rfl⟩ := E.surjective j
    rw [(GlueDance.D3 (GlueDance.S4 (Families.ds l) h21) hZ g g' s s').1]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, BendCor.gS]
  · ext s s'
    have := (GlueDance.D3 (GlueDance.S4 (Families.ds l) h21) hZ 0 0 s s').2
    rw [Matrix.smul_apply, Matrix.sub_apply, ← this, two_nsmul, two_mul]

/-- **(M2)** of `C50g_theorem_10_22_for_i_positive.md` (the glue): with
`n := Dance.slots (Families.ds l) 1`, let `Xk Yk Zk Uk U'k ZUk` be matrices over `Bf ℤ_[2]` on
`Fin n` with `MAgree (Yk - Xk) (2 • Zk)` and `MAgree (U'k - Uk) (2 • ZUk)`, and let
`Wm Wp : Matrix (Fin n) (Fin n) ℤ_[2]` satisfy `IsUnit Wm.det`, `IsUnit Wp.det`,
`‖((Wm - 1) s s' : ℚ_[2])‖ ≤ 1/2`, `‖((Wp - 1) s s' : ℚ_[2])‖ ≤ 1/2` for all `s s'`,
`finalM Uk = Wm * finalM Xk` and `finalM U'k = Wp * finalM Yk`. Then there is `P` on
`Fin (Dance.slots (Families.ds l) 2)` with `IsUnit P.det` and
`finalM (glueC (S4 (Families.ds l) h21) Uk U'k ZUk) =
P * finalM (glueC (S4 (Families.ds l) h21) Xk Yk Zk)`. -/
theorem M2 (h21 : (2 : ℕ) = 2 * 1) (l : ℕ)
    (Xk Yk Zk Uk U'k ZUk : Matrix (Fin (Dance.slots (Families.ds l) 1))
      (Fin (Dance.slots (Families.ds l) 1)) (Bf ℤ_[2]))
    (hZ : MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)) (hZU : MAgree (U'k - Uk) ((2 : ℤ_[2]) • ZUk))
    (Wm Wp : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      ℤ_[2])
    (hWm : IsUnit Wm.det) (hWp : IsUnit Wp.det)
    (hWm1 : ∀ s s', ‖(((Wm - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2)
    (hWp1 : ∀ s s', ‖(((Wp - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2)
    (hU : finalM Uk = Wm * finalM Xk) (hU' : finalM U'k = Wp * finalM Yk) :
    ∃ P : Matrix (Fin (Dance.slots (Families.ds l) 2)) (Fin (Dance.slots (Families.ds l) 2))
        ℤ_[2],
      IsUnit P.det ∧
        finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Uk U'k ZUk) =
          P * finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk) := by
  set E := GlueDance.gE (GlueDance.S4 (Families.ds l) h21)
  obtain ⟨hX, hXZ⟩ := finalM_glueC h21 l Xk Yk Zk hZ
  obtain ⟨hUg, hUZ⟩ := finalM_glueC h21 l Uk U'k ZUk hZU
  have hdiff : ∀ s s', ‖(((Wp - Wm) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2 := fun s s' => by
    have e : (Wp - Wm) s s' = (Wp - 1) s s' - (Wm - 1) s s' := by
      simp only [Matrix.sub_apply]; ring
    rw [e, PadicInt.coe_sub, sub_eq_add_neg]
    refine (Padic.nonarchimedean _ _).trans (max_le (hWp1 s s') ?_)
    rw [norm_neg]; exact hWm1 s s'
  obtain ⟨ZW, hZW⟩ := BendCor.G5 Wp Wm hdiff
  obtain ⟨Z₁, hmul, h2⟩ := BendCor.G4 _ _ _ Wm Wp ZW hXZ hZW
  have hZ₁ : Z₁ = finalM ZUk := by
    have e : 2 • Z₁ = 2 • finalM ZUk := by rw [h2, hUZ, hU, hU']
    ext s s'
    have := congrFun (congrFun e s) s'
    simp only [Matrix.smul_apply, two_nsmul] at this
    rw [← two_mul, ← two_mul] at this
    exact mul_left_cancel₀ two_ne_zero this
  refine ⟨(BendCor.gS Wm Wp ZW).submatrix E.symm E.symm, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self]; exact BendCor.G3 _ _ _ hWm hWp
  · rw [hUg, hX, Matrix.submatrix_mul_equiv, hmul, hZ₁, ← hU, ← hU']

end EvenFold
