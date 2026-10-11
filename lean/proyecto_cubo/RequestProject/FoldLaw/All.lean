module

public import RequestProject.FoldLaw.Groups
public import RequestProject.FoldLaw.PartH
public import RequestProject.FoldLaw.PartL
public import RequestProject.FoldLaw.PartD
public import RequestProject.FoldLaw.PartR

/-!
# `C51_theorem_DW.md` — Theorem DW, the fold law, and its consequences (paper v8 §1.3, §10.8)

Folder `RequestProject/FoldLaw/`, namespace `FoldLaw`. No new definition: everything listed in the
Setting of the file (C17 `CubeLaplacian`, C38 `Fold`, C38b `FoldGroup`, C34 `BaiCounts`, C49c
`ZeroSmith`, C50h `EvenZero`, C16 `FamilyGroup`, C32 `Families`) is reused, not redefined.

* Part H: (H) `FoldLaw.H` — `PartH.lean`.
* Part D: (DW) `FoldLaw.DW` — `PartH.lean`; (DW′) `FoldLaw.DW'` — `PartD.lean`.
* Part L: (L0) `FoldLaw.L0`, (L1) `FoldLaw.L1` — `PartL.lean`.
* Part R: (R) `FoldLaw.R` — `PartR.lean`.

`Groups.lean` holds auxiliary facts on finite abelian groups used in the proofs (layers of
`ZMod (2 ^ e)` and of `ℤ`, the structure of finite abelian `2`-groups, `ℓ_0(Syl2 T) = ℓ_0(T)`).
-/
