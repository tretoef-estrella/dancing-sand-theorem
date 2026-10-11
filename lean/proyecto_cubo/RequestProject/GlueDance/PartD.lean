module

public import RequestProject.GlueDance.PartS

/-!
# `C50_the_glue_commutes_with_the_dance.md`: Part D — the dance of a glued system

(D1), (D2) (Lemma 10.19) and (D3) of the file. (D2) is proved by induction on `ds`, generalizing
`r r₂ h X Y Z Xk Yk`, exactly as in the sketch: `r₂` stays general, so no cast between
`Fin ((2 * r) * 2)` and `Fin (2 * (r * 2))` is needed, and the final index types are related by
(S4).
-/

@[expose] public section

noncomputable section

namespace GlueDance

open FormalOps FormalDance ContZero

/-- The first clause of every level of `PairRel`: the two arms are congruent modulo `2` (used for
(D1), (D2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma PairRel.head {ds : List Bool} {r : ℕ} {X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    {Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])}
    (h : PairRel ds r X Y Xk Yk) : MCong 1 Y X := by
  cases ds with
  | nil => exact h.1
  | cons d rest => cases d <;> exact h.1

/-- **(D1)** of `C50_the_glue_commutes_with_the_dance.md`:
`PairRel ds r X Y Xk Yk → DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧ MCong 1 Yk Xk`. -/
theorem D1 (ds : List Bool) {r : ℕ} {X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    {Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])}
    (h : PairRel ds r X Y Xk Yk) :
    DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧ MCong 1 Yk Xk := by
  induction ds generalizing r X Y with
  | nil =>
    obtain ⟨hc, hx, hy⟩ := h
    exact ⟨hx, hy, ((MCong.of_magree hy.symm).trans hc).trans (MCong.of_magree hx)⟩
  | cons d rest ih =>
    cases d with
    | false =>
      obtain ⟨-, X', Y', hX, hY, hr⟩ := h
      obtain ⟨a, b, c⟩ := ih hr
      exact ⟨⟨X', hX, a⟩, ⟨Y', hY, b⟩, c⟩
    | true =>
      obtain ⟨-, X'', Y'', hX, hY, hr⟩ := h
      obtain ⟨a, b, c⟩ := ih hr
      exact ⟨⟨X'', hX, a⟩, ⟨Y'', hY, b⟩, c⟩

/-- **(D2) Lemma 10.19** of `C50_the_glue_commutes_with_the_dance.md`: for every
`ds : List Bool`, `r r₂ : ℕ`, `h : r₂ = 2 * r`, `X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])`,
`Xk Yk` on `Fin (Dance.slots ds r)` with `PairRel ds r X Y Xk Yk`, and every `Z` with
`MAgree (Y - X) ((2 : ℤ_[2]) • Z)`: there is `Zk` with `MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)` and
`DanceRel ds r₂ (glueC h X Y Z) (glueC (S4 ds h) Xk Yk Zk)`. -/
theorem D2 (ds : List Bool) {r r₂ : ℕ} (h : r₂ = 2 * r) {X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    {Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])}
    (hP : PairRel ds r X Y Xk Yk) (Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z)) :
    ∃ Zk, MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧
      DanceRel ds r₂ (glueC h X Y Z) (glueC (S4 ds h) Xk Yk Zk) := by
  induction ds generalizing r r₂ X Y Z with
  | nil =>
    obtain ⟨-, hx, hy⟩ := hP
    refine ⟨Z, (hy.symm.sub hx.symm).trans hZ, ?_⟩
    intro j j'
    exact B3_mk hx hy (MAgree.refl Z) _ _
  | cons d rest ih =>
    cases d with
    | false =>
      obtain ⟨-, X', Y', hX, hY, hr⟩ := hP
      obtain ⟨W, hW⟩ := hr.head
      rw [pow_one] at hW
      have hC := Cleanliness.L1 (gE h).symm _ _ (G2 hX hY hZ hW)
      obtain ⟨Zk, hZk, hD⟩ := ih h hr W hW
      exact ⟨Zk, hZk, glueC h X' Y' W, hC, hD⟩
    | true =>
      obtain ⟨-, X'', Y'', hX, hY, hr⟩ := hP
      obtain ⟨Wr, hWr⟩ := hr.head
      rw [pow_one] at hWr
      set W'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2]) :=
        fun q q' => Wr (Dance.splitIso r (toLex q)) (Dance.splitIso r (toLex q'))
      have hrelab : relab W'' = Wr := by
        funext j j'
        simp [relab, W'']
      have hW'' : MAgree (Y'' - X'') ((2 : ℤ_[2]) • W'') := by
        intro q q'
        have := hWr (Dance.splitIso r (toLex q)) (Dance.splitIso r (toLex q'))
        simpa [relab, W''] using this
      have hC := Cleanliness.L1 (τ h) _ _ (G2 hX hY (S2 hZ) hW'')
      rw [← S1] at hC
      have h2 : r₂ * 2 = 2 * (r * 2) := by rw [h]; ring
      obtain ⟨Zk, hZk, hD⟩ := ih h2 hr (relab W'') (by rw [hrelab]; exact hWr)
      refine ⟨Zk, hZk, _, hC, ?_⟩
      show DanceRel rest (r₂ * 2) (relab (fun q q' => glueM X'' Y'' W'' (τ h q) (τ h q'))) _
      rw [S3 h h2]
      exact hD

/-- **(D3)** of `C50_the_glue_commutes_with_the_dance.md` (the final matrix): for
`h : r₂ = 2 * r`, `Xk Yk Zk : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` with
`MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)`, and all `g g' : Fin 2`, `s s' : Fin r`,
`finalM (glueC h Xk Yk Zk) (gE h (g, s)) (gE h (g', s'))` is `finalM Xk s s'`, `finalM Zk s s'`,
`finalM Yk s s'` or `0` according to the blocks, and
`2 * finalM Zk s s' = finalM Yk s s' - finalM Xk s s'`. -/
theorem D3 {r r₂ : ℕ} (h : r₂ = 2 * r) {Xk Yk Zk : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    (hZ : MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)) (g g' : Fin 2) (s s' : Fin r) :
    finalM (glueC h Xk Yk Zk) (gE h (g, s)) (gE h (g', s')) =
      (if g = 0 ∧ g' = 0 then finalM Xk s s' else if g = 1 ∧ g' = 0 then finalM Zk s s'
        else if g = 1 ∧ g' = 1 then finalM Yk s s' else 0) ∧
    2 * finalM Zk s s' = finalM Yk s s' - finalM Xk s s' := by
  constructor
  · simp only [finalM, glueC, Equiv.symm_apply_apply, glueM]
    split_ifs <;> rfl
  · have := hZ s s' 0 0 le_rfl
    simp only [Matrix.sub_apply, Matrix.smul_apply, Bf.coef_sub, Bf.coef_smul] at this
    simp only [finalM]
    exact this.symm

end GlueDance
