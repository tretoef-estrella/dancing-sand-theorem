module

public import RequestProject.ContZero.All
public import RequestProject.Cleanliness.All
public import RequestProject.DanceXi.All

/-!
# `C50_the_glue_commutes_with_the_dance.md`: Definitions (new)

Namespace `GlueDance`. Nothing listed in the Setting of the file is redefined: `Bf`, `tw00`,
`tw11`, `tw10`, `tw01`, `vplus`, `vprime` are C40's (`FormalOps`); `Agree`, `MAgree`, `twP`, `twC`,
`twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`, `finalM` are C40b's (`FormalDance`); `slots`,
`slots_eq`, `splitIso` are C13's (`Dance`); `MCong` is C49b's (`ContZero`); `L1` is C48's
(`Cleanliness`).

The new definitions `glueM`, `gE`, `glueC`, `relab`, `τ` and `PairRel` are written exactly as in
the file. Matrices are Mathlib's `Matrix n n (Bf ℤ_[2])`, entry `[p, p']` mapping the source slot
`p'` to the coordinate slot `p`; the glue index is the first component of `Fin 2 × n`.
`gE h : Fin 2 × Fin r ≃ Fin r₂` is `finProdFinEquiv` followed by `finCongr h.symm`, so
`(g, s) ↦ s + r g` (the glue index is the top digit). The equivalence `τ h` of (S1) is stated as a
definition: `((gE h).symm × id)` followed by the associator.
-/

@[expose] public section

noncomputable section

namespace GlueDance

open FormalOps FormalDance ContZero

/-- Definitions (new) of `C50_the_glue_commutes_with_the_dance.md`: the glued matrix
`[[X, 0], [Z, Y]]` on `Fin 2 × n` (the glue index on top), i.e. the operator
`(m, m') ↦ (X m, Z m + Y m')`. -/
def glueM {n : Type*} (X Y Z : Matrix n n (Bf ℤ_[2])) :
    Matrix (Fin 2 × n) (Fin 2 × n) (Bf ℤ_[2]) :=
  fun p p' => if p.1 = 0 ∧ p'.1 = 0 then X p.2 p'.2
    else if p.1 = 1 ∧ p'.1 = 0 then Z p.2 p'.2
    else if p.1 = 1 ∧ p'.1 = 1 then Y p.2 p'.2 else 0

/-- Definitions (new) of `C50_the_glue_commutes_with_the_dance.md`: the relabelling
`Fin 2 × Fin r ≃ Fin r₂`, `(g, s) ↦ s + r g` (the glue index is the top digit). -/
def gE {r r₂ : ℕ} (h : r₂ = 2 * r) : Fin 2 × Fin r ≃ Fin r₂ :=
  finProdFinEquiv.trans (finCongr h.symm)

/-- Definitions (new) of `C50_the_glue_commutes_with_the_dance.md`: the glued matrix read on
`Fin r₂` through `gE h`. -/
def glueC {r r₂ : ℕ} (h : r₂ = 2 * r) (X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) :
    Matrix (Fin r₂) (Fin r₂) (Bf ℤ_[2]) :=
  fun j j' => glueM X Y Z ((gE h).symm j) ((gE h).symm j')

/-- Definitions (new) of `C50_the_glue_commutes_with_the_dance.md`: the relabelling inside C40b
`DanceRel`, a matrix on `Fin r × Fin 2` read on `Fin (r * 2)` through
`ofLex ∘ (Dance.splitIso r).symm`. -/
def relab {r : ℕ} (M : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])) :
    Matrix (Fin (r * 2)) (Fin (r * 2)) (Bf ℤ_[2]) :=
  fun j j' => M (ofLex ((Dance.splitIso r).symm j)) (ofLex ((Dance.splitIso r).symm j'))

/-- The equivalence `τ h : Fin r₂ × Fin 2 ≃ Fin 2 × (Fin r × Fin 2)` of (S1) of
`C50_the_glue_commutes_with_the_dance.md`,
`q ↦ (((gE h).symm q.1).1, (((gE h).symm q.1).2, q.2))`. -/
def τ {r r₂ : ℕ} (h : r₂ = 2 * r) : Fin r₂ × Fin 2 ≃ Fin 2 × (Fin r × Fin 2) :=
  ((gE h).symm.prodCongr (Equiv.refl (Fin 2))).trans (Equiv.prodAssoc _ _ _)

/-- (S1) of `C50_the_glue_commutes_with_the_dance.md`: `τ h` acts as stated in the file. -/
@[simp] lemma τ_apply {r r₂ : ℕ} (h : r₂ = 2 * r) (q : Fin r₂ × Fin 2) :
    τ h q = (((gE h).symm q.1).1, (((gE h).symm q.1).2, q.2)) := rfl

/-- Definitions (new) of `C50_the_glue_commutes_with_the_dance.md`: two dances side by side, with
the two arms congruent modulo `2` at every level (by recursion on `ds`). -/
def PairRel : (ds : List Bool) → (r : ℕ) → (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) →
    (Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])) → Prop
  | [], _, X, Y, Xk, Yk => MCong 1 Y X ∧ MAgree X Xk ∧ MAgree Y Yk
  | false :: rest, r, X, Y, Xk, Yk => MCong 1 Y X ∧ ∃ X' Y', CleanStep X X' ∧ CleanStep Y Y' ∧
      PairRel rest r X' Y' Xk Yk
  | true :: rest, r, X, Y, Xk, Yk => MCong 1 Y X ∧
      ∃ X'' Y'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2]),
      CleanStep (vsplit X) X'' ∧ CleanStep (vsplit Y) Y'' ∧
      PairRel rest (r * 2) (relab X'') (relab Y'') Xk Yk

end GlueDance
