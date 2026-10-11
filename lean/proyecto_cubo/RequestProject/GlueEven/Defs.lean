module

public import RequestProject.ArmsEven.All
public import RequestProject.FormalProp.All
public import RequestProject.GlueDance.All

/-!
# `C50f_the_glued_system_on_T.md`: Definitions (new) — `ZF`, `pairE`, `PF`

Namespace `GlueEven`. Nothing listed in the Setting of the file is redefined: `Bf`, `act` are
C40's (`FormalOps`); `Agree`, `MAgree`, `DanceRel`, `finalM` are C40b's (`FormalDance`); `sysAct` is
C40c's (`FormalAct`); `Q1` is C40d's (`FormalProp`); `Psi`, `Zop`, `glueOp`, `parOp`, `ShInv` are
C39's (`FoldHalf`); `thX`, `thY` are C39b's (`FoldCube`); `PsiF`, `KF`, `ShInvF` are C49's
(`FoldOdd`); `glueC`, `glueM`, `gE`, `PairRel`, `S4` are C50's (`GlueDance`); `covSys` is C47's
(`RingK`); `Good` is C48's (`Cleanliness`); `Cong2` is C50b's (`DanceMod2`); `E2` is C50c's
(`ArmsEven`); `T` is C29's `Filt.T`; `ds` is C32's `Families.ds`; `slots`, `mCount` are C13's
(`Dance`).

The three new definitions are written exactly as in the file:
* `ZF i := −1 − ((−1)^i) • ShInvF`;
* `pairE V : (Fin 2 → V) ≃ₗ[ℤ_[2]] V × V`, `v ↦ (v 0, v 1)` (Mathlib's `LinearEquiv.finTwoArrow`);
* `PF l r h`, the first factor of C40d `Q1`, as an `abbrev` (so that its module instances are
  found by unfolding).

The hypothesis `h21 : (2 : ℕ) = 2 * 1` of the file is taken as an argument of each statement
that uses it (any two proofs of it are equal).
-/

@[expose] public section

noncomputable section

namespace GlueEven

open FormalOps Pointwise

/-- **Definitions (new)** of `C50f_the_glued_system_on_T.md`: the lower-left arm of the fold side,
`ZF i := -(1 : Bf ℤ_[2]) - ((-1 : ℤ_[2]) ^ i) • FoldOdd.ShInvF`. -/
def ZF (i : ℕ) : Bf ℤ_[2] := -(1 : Bf ℤ_[2]) - ((-1 : ℤ_[2]) ^ i) • FoldOdd.ShInvF

/-- **Definitions (new)** of `C50f_the_glued_system_on_T.md`: the pairing
`pairE V : (Fin 2 → V) ≃ₗ[ℤ_[2]] V × V`, `pairE V v = (v 0, v 1)` (Mathlib's
`LinearEquiv.finTwoArrow`). -/
def pairE (V : Type*) [AddCommGroup V] [Module ℤ_[2] V] : (Fin 2 → V) ≃ₗ[ℤ_[2]] V × V :=
  LinearEquiv.finTwoArrow ℤ_[2] V

/-- **Definitions (new)** of `C50f_the_glued_system_on_T.md`: the defining formula
`pairE V v = (v 0, v 1)`. -/
@[simp] lemma pairE_apply (V : Type*) [AddCommGroup V] [Module ℤ_[2] V] (v : Fin 2 → V) :
    pairE V v = (v 0, v 1) := rfl

/-- **Definitions (new)** of `C50f_the_glued_system_on_T.md`: the factor of C40d `Q1`,
`PF l r h = Π a : Fin k, (Fin (r * 2 ^ (k + mCount ds − 1 − a)) → ℤ_[2]) ⧸ 2^(h + a) • ⊤`,
with `ds = Families.ds l` and `k = ds.length`. -/
abbrev PF (l r h : ℕ) : Type :=
  (a : Fin (Families.ds l).length) →
    (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]) ⧸
      (2 : ℤ_[2]) ^ (h + (a : ℕ)) • (⊤ : Submodule ℤ_[2]
        (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]))

end GlueEven
