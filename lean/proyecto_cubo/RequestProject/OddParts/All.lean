module

public import RequestProject.OddParts.Defs
public import RequestProject.OddParts.PartQ
public import RequestProject.OddParts.PartF
public import RequestProject.OddParts.Transport
public import RequestProject.OddParts.PartB
public import RequestProject.OddParts.PartC

/-!
# `C52_odd_parts.md` — the odd parts: Bai's odd part of `K(Q_n)` and the odd part of the folded
cube (paper v8 §1.1, Corollary 1.4)

Folder `RequestProject/OddParts/`, namespace `OddParts`. Everything listed in the Setting of the
file (C17 `CubeLaplacian`, C38 `Fold`, C38b `FoldGroup`) is reused, not redefined.

* Definitions (`Defs.lean`): `Sylp`, `chi`, `fourier`, `ifourier`, `diagD`, `EvenS`, `chiBar`
  (through `Quotient.lift`), `fourierBar`, `ifourierBar`, `diagDBar`.
* Part Q (`PartQ.lean`): (Q0) `Q0`, (Q1) `Q1`, (Q2) `Q2`.
* Part F (`PartF.lean`): (X) `X`, (F1) `F1`, (F2) `F2`, (F3) `F3`.
* Part B (`PartB.lean`): (B0) `B0`, (B1) `B1`.
* Part C (`PartC.lean`): (X0) `X0`, (C1) `C1`, (C2) `C2`, (C3) `C3`, (C4) `C4`, (C5) `C5`.

`Transport.lean` holds auxiliary facts (cokernel of a diagonal map, `Sylp` of `ℤ/2k` versus `ℤ/k`
for odd `p`, reindexing of products of cyclic groups, grouping subsets by size).
-/
