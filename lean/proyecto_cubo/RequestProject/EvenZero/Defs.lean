module

public import RequestProject.EvenFold.All

/-!
# `C50h_theorem_10_22_at_zero.md`: Definitions (new) — `PsiC`

Folder `RequestProject/EvenZero/`, namespace `EvenZero`. Nothing listed in the Setting of the file
is redefined; the only new definition is `PsiC`, written exactly as in the file. Throughout,
`ι := PadicInt.Coe.ringHom`, `Φ := Smith2.Bf.map ι`, `ds := Families.ds l`, `k := ds.length`,
`ns := Dance.slots ds 1` (all written out in full in the statements).
-/

@[expose] public section

noncomputable section

namespace EvenZero

open FormalOps

/-- Definitions (new) of `C50h_theorem_10_22_at_zero.md`: the arm `Ψ_0` with its shift replaced by
`c`, `PsiC c := Smith2.XiOpZ 2 c (FoldOdd.kJ 0 1) (fun m _ => FoldOdd.kJ 0 m)`. -/
def PsiC (c : ℕ) : Bf ℤ_[2] := Smith2.XiOpZ 2 c (FoldOdd.kJ 0 1) (fun m _ => FoldOdd.kJ 0 m)

end EvenZero
