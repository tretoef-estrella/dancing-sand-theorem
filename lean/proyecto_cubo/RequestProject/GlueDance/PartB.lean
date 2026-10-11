module

public import RequestProject.GlueDance.Defs

/-!
# `C50_the_glue_commutes_with_the_dance.md`: Part B — block algebra

(B1)–(B4) of the file, for `n` a `Fintype` with `DecidableEq` (only where needed: the product
needs `Fintype n`, the unit needs `DecidableEq n`; the other identities hold for every `n`).
-/

@[expose] public section

noncomputable section

namespace GlueDance

open FormalOps FormalDance ContZero

section Entries

variable {n : Type*} (X Y Z : Matrix n n (Bf ℤ_[2])) (s s' : n)

/-- Entries of `glueM` (used for (B1)–(B3) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma glueM_00 : glueM X Y Z (0, s) (0, s') = X s s' := rfl
/-- Entries of `glueM` (used for (B1)–(B3) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma glueM_10 : glueM X Y Z (1, s) (0, s') = Z s s' := rfl
/-- Entries of `glueM` (used for (B1)–(B3) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma glueM_11 : glueM X Y Z (1, s) (1, s') = Y s s' := rfl
/-- Entries of `glueM` (used for (B1)–(B3) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma glueM_01 : glueM X Y Z (0, s) (1, s') = 0 := rfl

end Entries

variable {n : Type*}

/-- Extensionality on `Fin 2 × n` block by block (used for Part B of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma ext_blocks {G H : Matrix (Fin 2 × n) (Fin 2 × n) (Bf ℤ_[2])}
    (h00 : ∀ s s', G (0, s) (0, s') = H (0, s) (0, s'))
    (h01 : ∀ s s', G (0, s) (1, s') = H (0, s) (1, s'))
    (h10 : ∀ s s', G (1, s) (0, s') = H (1, s) (0, s'))
    (h11 : ∀ s s', G (1, s) (1, s') = H (1, s) (1, s')) : G = H := by
  funext ⟨g, s⟩ ⟨g', s'⟩
  fin_cases g <;> fin_cases g'
  · exact h00 s s'
  · exact h01 s s'
  · exact h10 s s'
  · exact h11 s s'

/-- (B1) of `C50_the_glue_commutes_with_the_dance.md`: the product rule. -/
theorem B1_mul [Fintype n] (X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])) :
    glueM X Y Z * glueM X' Y' Z' = glueM (X * X') (Y * Y') (Z * X' + Y * Z') := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- (B1) of `C50_the_glue_commutes_with_the_dance.md`: the unit, `glueM 1 1 0 = 1`. -/
theorem B1_one [DecidableEq n] : glueM (1 : Matrix n n (Bf ℤ_[2])) 1 0 = 1 := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp [Matrix.one_apply]

/-- (B1) of `C50_the_glue_commutes_with_the_dance.md`: the sum rule. -/
theorem B1_add (X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])) :
    glueM X Y Z + glueM X' Y' Z' = glueM (X + X') (Y + Y') (Z + Z') := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp

/-- (B1) of `C50_the_glue_commutes_with_the_dance.md`: the difference rule. -/
theorem B1_sub (X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])) :
    glueM X Y Z - glueM X' Y' Z' = glueM (X - X') (Y - Y') (Z - Z') := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp

/-- (B1) of `C50_the_glue_commutes_with_the_dance.md`: the scalar rule. -/
theorem B1_smul (a : ℤ_[2]) (X Y Z : Matrix n n (Bf ℤ_[2])) :
    a • glueM X Y Z = glueM (a • X) (a • Y) (a • Z) := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp

/-- **(B1)** of `C50_the_glue_commutes_with_the_dance.md`: for `n` a `Fintype` with
`DecidableEq` and `X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])`,
`glueM X Y Z * glueM X' Y' Z' = glueM (X * X') (Y * Y') (Z * X' + Y * Z')`, `glueM 1 1 0 = 1`,
the sum and difference rules, and `a • glueM X Y Z = glueM (a • X) (a • Y) (a • Z)`. -/
theorem B1 [Fintype n] [DecidableEq n] (X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])) :
    glueM X Y Z * glueM X' Y' Z' = glueM (X * X') (Y * Y') (Z * X' + Y * Z') ∧
    glueM (1 : Matrix n n (Bf ℤ_[2])) 1 0 = 1 ∧
    glueM X Y Z + glueM X' Y' Z' = glueM (X + X') (Y + Y') (Z + Z') ∧
    glueM X Y Z - glueM X' Y' Z' = glueM (X - X') (Y - Y') (Z - Z') ∧
    ∀ a : ℤ_[2], a • glueM X Y Z = glueM (a • X) (a • Y) (a • Z) :=
  ⟨B1_mul X Y Z X' Y' Z', B1_one, B1_add X Y Z X' Y' Z', B1_sub X Y Z X' Y' Z',
    fun a => B1_smul a X Y Z⟩

/-! ### (B2) -/

/-- `tw10 0 = 0` (used for (B2) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma tw10_zero : tw10 (0 : Bf ℤ_[2]) = 0 := by ext q f; simp
/-- `tw11 0 = 0` (used for (B2) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma tw11_zero : tw11 (0 : Bf ℤ_[2]) = 0 := by ext q f; simp
/-- `tw00 0 = 0` (used for (B2) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma tw00_zero : tw00 (0 : Bf ℤ_[2]) = 0 := by ext q f; simp
/-- `tw01 0 = 0` (used for (B2) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma tw01_zero : tw01 (0 : Bf ℤ_[2]) = 0 := by
  ext q f; cases q <;> simp
/-- `vplus 0 = 0` (used for (S1) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma vplus_zero : vplus (0 : Bf ℤ_[2]) = 0 := by ext q f; simp
/-- `vprime 0 = 0` (used for (S1) of `C50_the_glue_commutes_with_the_dance.md`). -/
@[simp] lemma vprime_zero : vprime (0 : Bf ℤ_[2]) = 0 := by ext q f; simp

/-- (B2) of `C50_the_glue_commutes_with_the_dance.md` for `twP`. -/
theorem B2_twP (X Y Z : Matrix n n (Bf ℤ_[2])) :
    twP (glueM X Y Z) = glueM (twP X) (twP Y) (twP Z) := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp [twP]

/-- (B2) of `C50_the_glue_commutes_with_the_dance.md` for `twC`. -/
theorem B2_twC (X Y Z : Matrix n n (Bf ℤ_[2])) :
    twC (glueM X Y Z) = glueM (twC X) (twC Y) (twC Z) := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp [twC]

/-- (B2) of `C50_the_glue_commutes_with_the_dance.md` for `twB`. -/
theorem B2_twB (X Y Z : Matrix n n (Bf ℤ_[2])) :
    twB (glueM X Y Z) = glueM (twB X) (twB Y) (twB Z) := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp [twB]

/-- (B2) of `C50_the_glue_commutes_with_the_dance.md` for `twD`. -/
theorem B2_twD (X Y Z : Matrix n n (Bf ℤ_[2])) :
    twD (glueM X Y Z) = glueM (twD X) (twD Y) (twD Z) := by
  refine ext_blocks (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) <;>
    simp [twD]

/-- **(B2)** of `C50_the_glue_commutes_with_the_dance.md`:
`twP (glueM X Y Z) = glueM (twP X) (twP Y) (twP Z)`, and the same for `twC`, `twB`, `twD`. -/
theorem B2 (X Y Z : Matrix n n (Bf ℤ_[2])) :
    twP (glueM X Y Z) = glueM (twP X) (twP Y) (twP Z) ∧
    twC (glueM X Y Z) = glueM (twC X) (twC Y) (twC Z) ∧
    twB (glueM X Y Z) = glueM (twB X) (twB Y) (twB Z) ∧
    twD (glueM X Y Z) = glueM (twD X) (twD Y) (twD Z) :=
  ⟨B2_twP X Y Z, B2_twC X Y Z, B2_twB X Y Z, B2_twD X Y Z⟩

/-! ### (B3) -/

/-- (B3) of `C50_the_glue_commutes_with_the_dance.md`, forward direction. -/
theorem B3_mk {X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])} (hX : MAgree X X') (hY : MAgree Y Y')
    (hZ : MAgree Z Z') : MAgree (glueM X Y Z) (glueM X' Y' Z') := by
  rintro ⟨g, s⟩ ⟨g', s'⟩
  fin_cases g <;> fin_cases g'
  · exact hX s s'
  · exact Agree.refl _
  · exact hZ s s'
  · exact hY s s'

/-- **(B3)** of `C50_the_glue_commutes_with_the_dance.md`: agreement of glued matrices is
blockwise agreement (both directions). -/
theorem B3 (X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])) :
    (MAgree X X' → MAgree Y Y' → MAgree Z Z' → MAgree (glueM X Y Z) (glueM X' Y' Z')) ∧
    (MAgree (glueM X Y Z) (glueM X' Y' Z') → MAgree X X' ∧ MAgree Y Y' ∧ MAgree Z Z') :=
  ⟨B3_mk, fun h => ⟨fun s s' => h (0, s) (0, s'), fun s s' => h (1, s) (1, s'),
    fun s s' => h (1, s) (0, s')⟩⟩

/-! ### (B4) -/

/-- **(B4)** of `C50_the_glue_commutes_with_the_dance.md` (no `2`-torsion): for
`G H : Matrix n n (Bf ℤ_[2])`, `MAgree ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H) → MAgree G H`. -/
theorem B4 {G H : Matrix n n (Bf ℤ_[2])}
    (h : MAgree ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H)) : MAgree G H := by
  intro s s' m f hf
  have := h s s' m f hf
  simp only [Matrix.smul_apply, Bf.coef_smul] at this
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ_[2]) ≠ 0) this

end GlueDance
