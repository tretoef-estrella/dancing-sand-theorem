module

public import RequestProject.ZeroSmith.Defs
public import RequestProject.ZeroSmith.PartG
public import RequestProject.ZeroSmith.PartZ
public import RequestProject.ZeroSmith.PartV
public import RequestProject.ZeroSmith.PartR
public import RequestProject.ZeroSmith.PartC

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`: the Smith form and the cokernel of `Ξ` at `c = 0`;
# Theorem 10.16 and Corollary 10.17 for every index

Folder `RequestProject/ZeroSmith/`, namespace `ZeroSmith`. Nothing listed in the Setting is
redefined; the only new definition is `Data0` (`Defs.lean`), written exactly as in the file.

Where each item is:
* Definition (new) `Data0` — `Defs.lean` (its binders `s s'` are typed
  `Fin (2 ^ Dance.mCount ds)`, since `M' s s'` needs them there).
* **(G1)** `ZeroSmith.G1`, **(G2)** `ZeroSmith.G2` — `PartG.lean`.
* **(Z3)** `ZeroSmith.Z3` — `PartZ.lean`.
* **(V4)** `ZeroSmith.V4`, **(V5)** `ZeroSmith.V5`, **(V6)** `ZeroSmith.V6`, **(V7)** `ZeroSmith.V7`
  — `PartV.lean`. The matrix `X` of the file is written out as
  `(finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
  (Fin.cast (Smith2.slots_cast (Families.ds l)))`.
* **(R6)** `ZeroSmith.R6`, **(R7)** `ZeroSmith.R7` (Theorem 10.16) — `PartR.lean`.
* **(C4)** `ZeroSmith.C4`, **(C5)** `ZeroSmith.C5` (Corollary 10.17) — `PartC.lean`. In (C4) each
  quotient is parenthesised, as in C49 (C1).

Encodings: "isomorphic" is `Nonempty (… ≃ₗ[ℤ_[2]] …)` (`≃+` in (C5)); cokernels are quotients by
`LinearMap.range`; "unit determinant" is `IsUnit P.det`.
-/
