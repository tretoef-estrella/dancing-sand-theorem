module

public import RequestProject.Cleanliness.Defs
public import RequestProject.Cleanliness.Inverse
public import RequestProject.Cleanliness.PartW
public import RequestProject.Cleanliness.PartV
public import RequestProject.Cleanliness.PartO

/-!
# `C48_cleanliness_one_move.md`: cleanliness, one move of the dance keeps the class

Namespace `Cleanliness`. Nothing listed as reused in the Setting is redefined: C47 `RingK`
(`KRep`, `Kr`, `theta`, `RS`, `oS`, `Dn`, `covSys`, `thetaSys`, `prodFun` and (K1)–(T3)), C40
`FormalOps` (`Bf`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`), C20 `Doubling.dfi` and the
instance `Doubling.OddUnits ℤ_[2]`, C40b `FormalDance` (`MAgree`, `twP`, `twC`, `twB`, `twD`,
`vsplit`, `CleanStep`) and C46 `Smith2.XiOpZ`.

* **Definitions (new)** (`Defs.lean`): `InK`, `PayA`, `CoefB`, `Good`, `GB`, `GC`, `GP`, `GD`,
  `vsplitG`, `splitDn`, `G0`, exactly as in the file.
* **Part W** (`PartW.lean`): `W1` (with `W1_B`, `W1_C`, `W1_P`, `W1_D`, equalities of matrices),
  `W2`, `W3` (the equalities are equalities of functions and of matrices), `W4`, `W5`.
  The inverse `GQ` of (W3) is the recursion of the proof sketch (`rinv`, in `Inverse.lean`); the
  left inverse used to get `Q P = 1` is the mirror recursion (`linv`).
* **Part V** (`PartV.lean`): `V0`, `V1` (an equality, entry by entry), `V2`, `V3`, `L1`.
* **Part O** (`PartO.lean`): `O1`, `O2` (an equality in `Bf ℤ_[2]`).

No statement needed a hypothesis beyond those given in the file. In (V2) the identity
`vsplitG h Γ {h} 0 = Γ ∅ 1` is stated without the hypothesis `Good Γ`, which it does not need.
-/
