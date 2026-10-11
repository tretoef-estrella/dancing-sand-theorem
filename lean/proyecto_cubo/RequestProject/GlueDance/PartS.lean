module

public import RequestProject.GlueDance.PartG

/-!
# `C50_the_glue_commutes_with_the_dance.md`: Part S — one V-split, and the relabelling

(S1)–(S4) of the file. (S1) and (S3) are equalities of matrices, proved entry by entry; (S3) is
the index identity of the file (`index_S3`).
-/

@[expose] public section

noncomputable section

namespace GlueDance

open FormalOps FormalDance ContZero

/-- **(S1)** of `C50_the_glue_commutes_with_the_dance.md`: for `h : r₂ = 2 * r` and
`X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])`,
`vsplit (glueC h X Y Z) = fun q q' => glueM (vsplit X) (vsplit Y) (vsplit Z) (τ h q) (τ h q')`,
where `τ h q = (((gE h).symm q.1).1, (((gE h).symm q.1).2, q.2))` (`τ_apply`). -/
theorem S1 {r r₂ : ℕ} (h : r₂ = 2 * r) (X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) :
    vsplit (glueC h X Y Z) =
      fun q q' => glueM (vsplit X) (vsplit Y) (vsplit Z) (τ h q) (τ h q') := by
  funext q q'
  obtain ⟨j, b⟩ := q
  obtain ⟨j', b'⟩ := q'
  simp only [vsplit, glueC, τ_apply]
  generalize (gE h).symm j = p
  generalize (gE h).symm j' = p'
  obtain ⟨g, s⟩ := p
  obtain ⟨g', s'⟩ := p'
  fin_cases g <;> fin_cases g' <;> fin_cases b <;> fin_cases b' <;> simp [glueM, vsplit]

/-- `vsplit` commutes with differences (used for (S2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma vsplit_sub {n : Type*} (G H : Matrix n n (Bf ℤ_[2])) :
    vsplit (G - H) = vsplit G - vsplit H := by
  funext q q'
  simp only [vsplit, Matrix.sub_apply]
  split_ifs <;> simp [vplus_sub', vprime_sub']

/-- `vsplit` commutes with scalars (used for (S2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma vsplit_smul {n : Type*} (a : ℤ_[2]) (G : Matrix n n (Bf ℤ_[2])) :
    vsplit (a • G) = a • vsplit G := by
  funext q q'
  simp only [vsplit, Matrix.smul_apply]
  split_ifs
  · rfl
  · ext m f; simp
  · ext m f; simp
  · simp

/-- **(S2)** of `C50_the_glue_commutes_with_the_dance.md`: for
`X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])`,
`MAgree (Y - X) ((2 : ℤ_[2]) • Z) → MAgree (vsplit Y - vsplit X) ((2 : ℤ_[2]) • vsplit Z)`. -/
theorem S2 {r : ℕ} {X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z)) :
    MAgree (vsplit Y - vsplit X) ((2 : ℤ_[2]) • vsplit Z) := by
  have := hZ.vsplit
  rwa [vsplit_sub, vsplit_smul] at this

/-- The inverse of `Dance.splitIso r` is `toLex ∘ finProdFinEquiv.symm` (used for (S3) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma splitIso_symm_apply (r : ℕ) (j : Fin (r * 2)) :
    (Dance.splitIso r).symm j = toLex (finProdFinEquiv.symm j) := by
  rw [OrderIso.symm_apply_eq, Dance.splitIso_apply, ofLex_toLex, Equiv.apply_symm_apply]

/-- The inverse of `gE h` (used for (S3) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma gE_symm_apply {r r₂ : ℕ} (h : r₂ = 2 * r) (j : Fin r₂) :
    (gE h).symm j = finProdFinEquiv.symm (finCongr h j) := rfl

/-- The index identity of (S3) of `C50_the_glue_commutes_with_the_dance.md`: for
`j : Fin (r₂ * 2)`, `τ h ((splitIso r₂).symm j) = (g, (splitIso r).symm c)` where
`(g, c) = (gE h2).symm j` (since `j / (2r) = (j / 2) / r`, `(j % (2r)) / 2 = (j / 2) % r` and
`(j % (2r)) % 2 = j % 2`). -/
lemma index_S3 {r r₂ : ℕ} (h : r₂ = 2 * r) (h2 : r₂ * 2 = 2 * (r * 2)) (j : Fin (r₂ * 2)) :
    τ h (ofLex ((Dance.splitIso r₂).symm j)) =
      (((gE h2).symm j).1, ofLex ((Dance.splitIso r).symm ((gE h2).symm j).2)) := by
  simp only [τ_apply, splitIso_symm_apply, gE_symm_apply, ofLex_toLex]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> apply Fin.ext <;>
    simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat, finCongr_apply,
      Fin.val_cast]
  · rw [Nat.div_div_eq_div_mul, mul_comm r 2]
  · rw [mul_comm r 2, Nat.mod_mul_right_div_self]
  · rw [Nat.mod_mul_left_mod]

/-- **(S3)** of `C50_the_glue_commutes_with_the_dance.md`: for `h : r₂ = 2 * r`,
`h2 : r₂ * 2 = 2 * (r * 2)` and `X'' Y'' W'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])`,
`relab (fun q q' => glueM X'' Y'' W'' (τ h q) (τ h q')) =
glueC h2 (relab X'') (relab Y'') (relab W'')`. -/
theorem S3 {r r₂ : ℕ} (h : r₂ = 2 * r) (h2 : r₂ * 2 = 2 * (r * 2))
    (X'' Y'' W'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])) :
    relab (fun q q' => glueM X'' Y'' W'' (τ h q) (τ h q')) =
      glueC h2 (relab X'') (relab Y'') (relab W'') := by
  funext j j'
  simp only [relab, glueC]
  rw [index_S3 h h2 j, index_S3 h h2 j']
  simp only [glueM]
  split_ifs <;> rfl

/-- **(S4)** of `C50_the_glue_commutes_with_the_dance.md`: for `h : r₂ = 2 * r`,
`Dance.slots ds r₂ = 2 * Dance.slots ds r` for every `ds` (from `Dance.slots_eq`). -/
theorem S4 (ds : List Bool) {r r₂ : ℕ} (h : r₂ = 2 * r) :
    Dance.slots ds r₂ = 2 * Dance.slots ds r := by
  rw [Dance.slots_eq, Dance.slots_eq, h]; ring

end GlueDance
