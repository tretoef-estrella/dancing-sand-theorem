module

public import RequestProject.DanceMod2.Defs
public import RequestProject.DanceMod2.PartR
public import RequestProject.DanceMod2.PartK
public import RequestProject.DanceMod2.PartM
public import RequestProject.DanceMod2.PartD

/-!
# `C50b_the_dance_modulo_two.md` (paper v8 §10.7, Lemma 10.18)

Namespace `DanceMod2`. Every part of the file:

* `Defs.lean`: the new definitions `RA` (with `RA.one`, `RA.mul`), `red4`, `kap`, `Cong2`;
* `PartR.lean`: (R1) `RA.instCommRing`, `RA.mul_apply`, `RA.one_apply`, `R1`; (R2) `R2`;
* `PartK.lean`: (K1) `K1`; (K2) `K2` (with `K2_mul`, `K2_add`, `K2_sub`, `K2_one`); (K3) `K3`;
  (K4) `K4`;
* `PartM.lean`: (M1)–(M6) `M1`, …, `M6`;
* `PartD.lean`: (D0) `D0`; (D1) Lemma 10.18 `D1`; (D2) `D2`; (D3) `D3`.
-/
