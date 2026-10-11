module

public import RequestProject.FormalDance.Defs
public import RequestProject.Doubling.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# `C43_path_sum.md`: Setting and Definitions (new)

Namespace `PathSum`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
`FormalOps.Bf` (`x.coef m f` = coefficient of `F^{(m)}` at the target floor `f`, product
`(x * y).coef m f = Σ_{a ≤ m} C(m, a) x.coef a f * y.coef (m − a) (f − a)`), `Agree` is C40b's
`FormalDance.Agree` and `OddUnits` is C20's `Doubling.OddUnits`.

* Setting: the project had no instance `OddUnits ℚ_[2]`; `instOddUnitsPadicTwo` provides it
  (an odd natural number is non-zero in a field of characteristic zero).
* Definitions (new): `piF`, `XiOp`, `SigOp`, `sL`, written exactly as in the file.
-/

@[expose] public section

noncomputable section

namespace PathSum

open FormalOps FormalDance Doubling Finset

/-- Setting of `C43_path_sum.md`: the instance `OddUnits ℚ_[2]` (every odd natural number is
non-zero, hence a unit, in the field `ℚ_[2]` of characteristic zero). -/
instance instOddUnitsPadicTwo : OddUnits ℚ_[2] :=
  ⟨fun k => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))⟩

/-- Definitions (new) of `C43_path_sum.md`: `piF α c d = 2 ^ α * (d + c)` (written `π(d)` in
the file). -/
def piF (α c : ℕ) (d : ℤ) : ℚ_[2] := 2 ^ α * ((d : ℚ_[2]) + c)

/-- Definitions (new) of `C43_path_sum.md`: the operator `Ξ`, with `coef 0 f = piF α c f`,
`coef 1 f = η` and `coef m f = ζ m f` for `m ≥ 2`. -/
def XiOp (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) : Bf ℚ_[2] :=
  ⟨fun m f => if m = 0 then piF α c f else if m = 1 then η else ζ m f⟩

/-- Definitions (new) of `C43_path_sum.md`: the operator `Σ = XiOp α c η 0`. -/
def SigOp (α c : ℕ) (η : ℚ_[2]) : Bf ℚ_[2] := XiOp α c η (fun _ _ => 0)

/-- Definitions (new) of `C43_path_sum.md`:
`sL α c η L f = (−1)^L * L! * η^L / ∏_{i ∈ range (L + 1)} piF α c (f − i)` (the product over the
floors `f − L, …, f`). -/
def sL (α c : ℕ) (η : ℚ_[2]) (L : ℕ) (f : ℤ) : ℚ_[2] :=
  (-1) ^ L * (L.factorial : ℚ_[2]) * η ^ L / ∏ i ∈ range (L + 1), piF α c (f - i)

/-- Definitions (new) of `C43_path_sum.md` (simp lemma): coefficient `0` of `XiOp`. -/
@[simp] lemma XiOp_coef_zero (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) (f : ℤ) :
    (XiOp α c η ζ).coef 0 f = piF α c f := rfl

/-- Definitions (new) of `C43_path_sum.md` (simp lemma): coefficient `1` of `XiOp`. -/
@[simp] lemma XiOp_coef_one (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) (f : ℤ) :
    (XiOp α c η ζ).coef 1 f = η := rfl

/-- Definitions (new) of `C43_path_sum.md`: coefficient `m ≥ 2` of `XiOp`. -/
lemma XiOp_coef_ge_two (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) {m : ℕ} (hm : 2 ≤ m)
    (f : ℤ) : (XiOp α c η ζ).coef m f = ζ m f := by
  simp only [XiOp]
  rw [if_neg (by omega), if_neg (by omega)]

end PathSum
