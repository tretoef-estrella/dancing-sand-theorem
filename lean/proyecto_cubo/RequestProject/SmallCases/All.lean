module

public import RequestProject.SmallCases.PartS
public import RequestProject.SmallCases.PartT
public import RequestProject.SmallCases.PartU

/-!
# `C53_the_small_cases.md` — the small cases (namespace `SmallCases`)

Theorem DW′, (L1) and (R) at `n = 1`, and Gao et al.'s Theorem 4.1 at `n = 2`; then each of these
statements for every `n` the paper states it for.  Nothing listed in the Setting (`CubeLaplacian`,
`Fold`, `FoldGroup`, `BaiCounts`, `FoldLaw`, `PodiumCor`, `Rulers`) is redefined.

* **Part S** (`PartS.lean`, `n = 1`): (S0) `S0`; (S1) `S1`; (S2) `S2`; (S3) `S3`;
  (DW'1) `DW'_one`; (L1-1) `L1_one`; (R1) `R1`.
* **Part T** (`PartT.lean`, `n = 2`): (T0) `T0`; (T1) `T1`; (G1-2) `G1_two`.
* **Part U** (`PartU.lean`, every `n`): `DW'_all`, `L1_all`, `R_all`, `G1_all`.
-/
