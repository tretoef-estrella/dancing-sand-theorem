module

public import RequestProject.GlueDance.Defs
public import RequestProject.GlueDance.PartB
public import RequestProject.GlueDance.PartG
public import RequestProject.GlueDance.PartS
public import RequestProject.GlueDance.PartD

/-!
# `C50_the_glue_commutes_with_the_dance.md`: the glue commutes with the dance (Lemma 10.19)

Folder `RequestProject/GlueDance/`, namespace `GlueDance`. Nothing listed in the Setting is
redefined (C40 `FormalOps`, C40b `FormalDance`, C13 `Dance`, C49b `ContZero`, C48 `Cleanliness`,
C48b `DanceXi` are reused without change). The new definitions are `glueM`, `gE`, `glueC`, `relab`,
the equivalence `τ` of (S1) and `PairRel` (`Defs.lean`), written exactly as in the file.

Where each item is:
* **(B1)** `GlueDance.B1` (and its parts `B1_mul`, `B1_one`, `B1_add`, `B1_sub`, `B1_smul`),
  **(B2)** `GlueDance.B2` (`B2_twP`, `B2_twC`, `B2_twB`, `B2_twD`), **(B3)** `GlueDance.B3`,
  **(B4)** `GlueDance.B4` — `PartB.lean`.
* **(G2)** `GlueDance.G2` — `PartG.lean`.
* **(S1)** `GlueDance.S1`, **(S2)** `GlueDance.S2`, **(S3)** `GlueDance.S3`, **(S4)** `GlueDance.S4`
  — `PartS.lean`.
* **(D1)** `GlueDance.D1`, **(D2)** (Lemma 10.19) `GlueDance.D2`, **(D3)** `GlueDance.D3` —
  `PartD.lean`.

No statement needed a hypothesis beyond those given in the file. In (B1) the product needs only
`Fintype n` and the unit only `DecidableEq n`; the sum, difference and scalar rules, (B2), (B3) and
(B4) hold for every index type `n` (more general than stated).
-/
