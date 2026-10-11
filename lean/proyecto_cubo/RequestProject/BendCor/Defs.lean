module

public import RequestProject.Bend.All

/-!
# `C50e_corollary_10_21.md`: Definitions (new) — `UOp` and `gS`

Namespace `BendCor`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
`FormalOps.Bf`, `Agree`, `DanceRel`, `finalM` are C40b's, `InvFloors.C109` is C42's,
`PathSum.XiOp`, `PathSum.piF`, `PathSum.norm_two_padic` and the instance `OddUnits ℚ_[2]` are
C43's, and `Bend.Nmat`, `Bend.Nmat_apply`, `Bend.N2`, `Bend.Nmat_eq_inv`, `Bend.Y0`, `Bend.B1`
are C50d's.

* `UOp Ψ t = (1/2) • (Ψ * (Ψ + t • 1))` (the paper's `Ψ(Ψ + t)/2`).
* `gS X Y Z` is the scalar glue `[[X, 0], [Z, Y]]` on `Fin 2 × n`, written exactly like C50
  `GlueDance.glueM`.
-/

@[expose] public section

noncomputable section

namespace BendCor

open FormalOps

/-- **Definitions (new)** of `C50e_corollary_10_21.md`: `UOp Ψ t := (1/2) • (Ψ * (Ψ + t • 1))`. -/
def UOp (Ψ : Bf ℚ_[2]) (t : ℚ_[2]) : Bf ℚ_[2] :=
  (1 / 2 : ℚ_[2]) • (Ψ * (Ψ + t • (1 : Bf ℚ_[2])))

/-- **Definitions (new)** of `C50e_corollary_10_21.md`: the scalar glue `[[X, 0], [Z, Y]]`,
written exactly like C50 `GlueDance.glueM`. -/
def gS {R : Type*} [Ring R] {n : Type*} (X Y Z : Matrix n n R) :
    Matrix (Fin 2 × n) (Fin 2 × n) R :=
  fun p p' => if p.1 = 0 ∧ p'.1 = 0 then X p.2 p'.2
    else if p.1 = 1 ∧ p'.1 = 0 then Z p.2 p'.2
    else if p.1 = 1 ∧ p'.1 = 1 then Y p.2 p'.2 else 0

end BendCor
