module

public import RequestProject.RingK.Defs
public import RequestProject.RingK.PartK
public import RequestProject.RingK.PartS
public import RequestProject.RingK.PartR
public import RequestProject.RingK.PartT

/-!
# `C47_the_ring_K_and_covariant_systems.md`: the ring `𝒦_r` and the covariant systems

Namespace `RingK`. Nothing of the project is redefined: `Bf` is C40's `FormalOps.Bf`.

* **Definitions (new)** (`Defs.lean`): `KRep`, `KRep.eval`, `Kr`, `S`, `red`, `thetaRep`, `theta`,
  `RS` (pointwise `+`; unit `RS.one`, product `RS.mul` of Definition 7), `oS`, `Dn`, `covSys`,
  `thetaSys`, `prodFun`. Two instances are added so that `S` is a commutative ring:
  `IsCentralScalar (ZMod 2) (PowerSeries (ZMod 2))` (the left and right actions agree) and the
  shortcut `CommRing S`.
* **Part K** (`PartK.lean`): `K1`, `K2`, `K3` (with `K3_const`, `K3_add`, `K3_sub`, `K3_neg`,
  `K3_mul`, `K3_smul`, `K3_pow_mul`), `K4`, `K5`, `K6`. The representations used are the formulas
  of the file (`K3_add_rep`, `K3_mul_rep`, `K4_rep`, and inside `K5`).
* **Part S** (`PartS.lean`): `S0`, `S0_theta`, `S1` (with `S1_add`, `S1_mul`, `S1_one`,
  `S1_const`, `S1_smul`), `S2`, `S3`, `S4`, `S5`.
* **Part R** (`PartR.lean`): `RS.instCommRing` and `R1` (commutativity, associativity,
  `(2 : RS) = 0`), `R2`.
* **Part T** (`PartT.lean`): `T0`, `T1` (with `T1_mul`, `T1_add`, `T1_smul`, `T1_one`), `T2`,
  `T3`. The unit system `Γ₁` is written inline as `fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0`.

No statement needed a hypothesis beyond those given in the file.
-/
