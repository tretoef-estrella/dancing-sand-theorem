module

public import RequestProject.Conjugation.All
public import RequestProject.PathSum.All
public import RequestProject.Stability.All
public import RequestProject.InvFloors.All

/-!
# `C50d_the_bend.md`: Definitions (new) — the matrix `Nmat`

Namespace `Bend`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
`FormalOps.Bf`, `Agree`, `MAgree`, `DanceRel`, `finalM` are C40b's, `sysAct` is C40c's,
`InvBlock.inH`, `InvBlock.outH` are C41's, `InvFloors.gamma`, `InvFloors.entry_sysAct` are C42's,
`PathSum.piF`, `XiOp`, `SigOp`, `sL`, `sLOp` and the instance `OddUnits ℚ_[2]` are C43's, the
definitions of C44 (`Stability.hadOne`, `Wt`, `nest`, `nuA`, `Amat`, `F2d1`, `F2d2`) and C45 are
used unchanged.

* `Nmat l B Y` is the matrix whose column `X` is the image of the basis vector `X` under
  `2^k outH ∘ sysAct (fun _ _ => Y) ∘ inH` (`k = (Families.ds l).length`), written exactly as in
  the file; rows and columns are indexed by `Fin (Dance.slots (Families.ds l) 1)`.
-/

@[expose] public section

noncomputable section

namespace Bend

open FormalOps FormalDance FormalAct Filt

/-- **Definitions (new)** of `C50d_the_bend.md`: the matrix `N`,
`Nmat l B Y Y' X := 2 ^ (Families.ds l).length * InvBlock.outH l 1 (sysAct (T ℚ_[2] l) (l : ℤ) B
(fun _ _ => Y) (InvBlock.inH l 1 (Pi.single X 1))) Y'` (column `X` is the image of the basis
vector `X`; the paper's `2^k out ∘ Y ∘ in`). -/
def Nmat (l B : ℕ) (Y : Bf ℚ_[2]) :
    Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2] :=
  Matrix.of fun Y' X => 2 ^ (Families.ds l).length *
    InvBlock.outH l 1 (sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y)
      (InvBlock.inH l 1 (Pi.single X 1))) Y'

/-- Definitions (new) of `C50d_the_bend.md`: the defining formula of `Nmat`. -/
lemma Nmat_apply (l B : ℕ) (Y : Bf ℚ_[2]) (Y' X : Fin (Dance.slots (Families.ds l) 1)) :
    Nmat l B Y Y' X = 2 ^ (Families.ds l).length *
      InvBlock.outH l 1 (sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y)
        (InvBlock.inH l 1 (Pi.single X 1))) Y' := rfl

end Bend
