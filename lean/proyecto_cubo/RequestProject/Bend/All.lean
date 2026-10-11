module

public import RequestProject.Bend.Defs
public import RequestProject.Bend.PartN
public import RequestProject.Bend.PartY
public import RequestProject.Bend.PartW
public import RequestProject.Bend.Aux
public import RequestProject.Bend.PartB

/-!
# `C50d_the_bend.md` — Lemma 10.20: the bend (paper v8 §10.7)

Folder `RequestProject/Bend/`, namespace `Bend`. Nothing listed in the Setting of the file is
redefined; the only new definition is `Nmat` (`Defs.lean`).

* Definitions (new): `Nmat` — `Defs.lean`.
* Part N: (N0) `N0`, (N1) `N1`, (N2) `N2` — `PartN.lean`.
* Part Y: (Y0) `Y0`, (Y1) `Y1` — `PartY.lean`.
* Part B: (W) `W` — `PartW.lean`; (B1) `B1`, (B2) `B2` — `PartB.lean` (with the auxiliary norm
  computations of `Aux.lean`).
-/
