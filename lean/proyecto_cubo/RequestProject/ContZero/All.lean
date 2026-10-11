module

public import RequestProject.ContZero.Defs
public import RequestProject.ContZero.PartK
public import RequestProject.ContZero.PartT
public import RequestProject.ContZero.PartC
public import RequestProject.ContZero.PartV

/-!
# `C49b_congruence_and_the_data_at_zero.md`: congruence along the dance, and the data of `Ξ`
# at `c = 0`

Folder `RequestProject/ContZero/`, namespace `ContZero`. Nothing listed in the Setting is
redefined: C40 `FormalOps` (`Bf`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`, `Bf.dg`,
`Bf.fd`), C40b `FormalDance` (`Agree`, `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`,
`CleanStep`, `DanceRel`, `finalM`, `paySys`, `ext0`, the congruence results on `Agree`/`MAgree`,
(L4) `L4_sigma`), C13 `Dance` (`pσ`, `κσ`, `slots`, `splitIso`, `mCount`, `dance`, `Mfin`),
C14 `Windows` (`finalMatrix`, `finalMatrix_eq_map`, `theorem_D_ii`, `Dset`), C15 `DanceSmith`
(`sl`, `zeroPos`, `final_row_zero`), C46 `Smith2` (`XiOpZ`, `slots_cast`, (V1)), C48b `DanceXi`
(T3) and C32 `Families.ds` are used unchanged.

## Definitions (new) — `Defs.lean`
`Cong` and `MCong`, written exactly as in the file.

## Where each item is
* **(K1)** `ContZero.K1` (`PartK.lean`).
* **(K2)** `ContZero.K2` (`PartK.lean`).
* **(K3)** `ContZero.K3` (`PartK.lean`).
* **(K4)** `ContZero.K4` (`PartK.lean`).
* **(K5)** `ContZero.K5` (`PartK.lean`).
* **(K6)** `ContZero.K6` (`PartK.lean`).
* **(T1)** `ContZero.T1` (`PartT.lean`).
* **(T2)** `ContZero.T2` (`PartT.lean`).
* **(T3)** `ContZero.T3` (`PartT.lean`).
* **(C1)** `ContZero.C1` (`PartC.lean`).
* **(C2)** `ContZero.C2` (`PartC.lean`).
* **(C3)** `ContZero.C3` (`PartC.lean`).
* **(V1)** `ContZero.V1` (`PartV.lean`).
* **(V2)** `ContZero.V2` (`PartV.lean`).
* **(V3)** `ContZero.V3` (`PartV.lean`).

The map `cs` of Part V is written out as `Fin.cast (Smith2.slots_cast (Families.ds l))`, and the
matrix `X` of (V3) as the function `fun s s' => finalM GkZ (cs s) (cs s')`.
-/
