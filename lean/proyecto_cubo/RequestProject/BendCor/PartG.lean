module

public import RequestProject.BendCor.Defs

/-!
# `C50e_corollary_10_21.md`: Part G — the scalar glue

* (G1) `G1`: the product of two glues.
* (G2) `G2`: the determinant, by reindexing along `eS : Fin 2 × n ≃ n ⊕ n` to
  `Matrix.fromBlocks X 0 Z Y`.
* (G3) `G3`, (G4) `G4`, (G5) `G5`.
-/

@[expose] public section

noncomputable section

namespace BendCor

/-- Auxiliary for (G2) of `C50e_corollary_10_21.md`: the relabelling `Fin 2 × n ≃ n ⊕ n`,
`(0, i) ↦ inl i`, `(1, i) ↦ inr i`. -/
def eS (n : Type*) : Fin 2 × n ≃ n ⊕ n where
  toFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  invFun := Sum.elim (fun i => (0, i)) (fun i => (1, i))
  left_inv p := by
    obtain ⟨a, i⟩ := p
    fin_cases a <;> simp
  right_inv s := by cases s <;> simp

/-- **(G1)** of `C50e_corollary_10_21.md` (product): for any ring `R` and any `Fintype n` with
`DecidableEq`, `gS X Y Z * gS X' Y' Z' = gS (X * X') (Y * Y') (Z * X' + Y * Z')`. -/
theorem G1 {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]
    (X Y Z X' Y' Z' : Matrix n n R) :
    gS X Y Z * gS X' Y' Z' = gS (X * X') (Y * Y') (Z * X' + Y * Z') := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [gS, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **(G2)** of `C50e_corollary_10_21.md` (determinant): for any commutative ring `R`,
`(gS X Y Z).det = X.det * Y.det`. -/
theorem G2 {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X Y Z : Matrix n n R) : (gS X Y Z).det = X.det * Y.det := by
  rw [← Matrix.det_reindex_self (eS n)]
  have : Matrix.reindex (eS n) (eS n) (gS X Y Z) = Matrix.fromBlocks X 0 Z Y := by
    ext (i | i) (j | j) <;> simp [eS, gS]
  rw [this, Matrix.det_fromBlocks_zero₁₂]

/-- **(G3)** of `C50e_corollary_10_21.md` (units): over `ℤ_[2]`, if `IsUnit X.det` and
`IsUnit Y.det`, then `IsUnit (gS X Y Z).det` for every `Z`. -/
theorem G3 {n : Type*} [Fintype n] [DecidableEq n] (X Y Z : Matrix n n ℤ_[2])
    (hX : IsUnit X.det) (hY : IsUnit Y.det) : IsUnit (gS X Y Z).det := by
  rw [G2]; exact hX.mul hY

/-- **(G4)** of `C50e_corollary_10_21.md` (the paper's identity
`glue(W₋, W₊)·glue(X, Y) = glue(W₋X, W₊Y)`): over `ℤ_[2]`, if `2 • Z = Y - X` and
`2 • Z_W = W₊ - W₋`, then `gS W₋ W₊ Z_W * gS X Y Z = gS (W₋ * X) (W₊ * Y) Z₁` for some `Z₁`
with `2 • Z₁ = W₊ * Y - W₋ * X`. -/
theorem G4 {n : Type*} [Fintype n] [DecidableEq n] (X Y Z Wm Wp ZW : Matrix n n ℤ_[2])
    (hZ : 2 • Z = Y - X) (hZW : 2 • ZW = Wp - Wm) :
    ∃ Z₁ : Matrix n n ℤ_[2], gS Wm Wp ZW * gS X Y Z = gS (Wm * X) (Wp * Y) Z₁ ∧
      2 • Z₁ = Wp * Y - Wm * X := by
  refine ⟨ZW * X + Wp * Z, G1 _ _ _ _ _ _, ?_⟩
  rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, hZ, hZW, Matrix.sub_mul,
    Matrix.mul_sub]
  abel

/-- **(G5)** of `C50e_corollary_10_21.md` (the half exists): over `ℤ_[2]`, if
`‖((W₊ - W₋) s s' : ℚ_[2])‖ ≤ 1/2` for all `s s'`, then there is `Z_W` with
`2 • Z_W = W₊ - W₋`. -/
theorem G5 {n : Type*} (Wp Wm : Matrix n n ℤ_[2])
    (h : ∀ s s', ‖(((Wp - Wm) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) :
    ∃ ZW : Matrix n n ℤ_[2], 2 • ZW = Wp - Wm := by
  have hd : ∀ s s', (2 : ℤ_[2]) ∣ (Wp - Wm) s s' := fun s s' => by
    have := (PadicInt.norm_lt_one_iff_dvd ((Wp - Wm) s s')).1
      (by rw [PadicInt.norm_def]; linarith [h s s'])
    exact_mod_cast this
  choose ZW hZ using hd
  refine ⟨fun s s' => ZW s s', ?_⟩
  ext s s'
  simp [hZ s s', two_mul]

end BendCor
