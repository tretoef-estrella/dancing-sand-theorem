module

public import RequestProject.DanceXi.PartT
public import RequestProject.DanceXi.PartR

/-!
# `C48b_the_dance_of_Xi_is_clean.md`: the dance of `Ξ` is clean, and Theorem 10.16 for `c ≥ 1`

Namespace `DanceXi`. Nothing of the project is redefined. Reused without change: C48
`Cleanliness` (`Good`, `splitDn`, `G0`, (V0), (V3), (W5), (L1), (O1), (O2)); C47 `RingK` (`Dn`,
`covSys`); C40 `FormalOps` (`Bf`, `vplus`, `vprime`); C40b `FormalDance` (`MAgree`, `vsplit`,
`CleanStep`, `DanceRel`, `finalM`); C13 `Dance` (`slots`, `splitIso`, `SysT`, `sigma`, `F`, `pσ`,
`κσ`); C46 `Smith2` (`XiOpZ`, (R5)); C40c `FormalAct.sysAct`; C40d `FormalProp.Q2_zero`; C29
`Filt.T`, `Filt.T_zero`; C32 `Families.ds`; C16 `FamilyGroup.X`; C11 `Payment.G`.

The only new declarations are proof auxiliaries: `finOneDnEmpty` (the unique equivalence
`Fin 1 ≃ Dn ∅`), `quotSmulEquiv`, `mulVecLin_finalM_XiOpZ`, `sigma_nil`, `finOneSysTNil`.

## Where each item is
* **(T1)** `DanceXi.T1` (`PartT.lean`), an equality of matrices.
* **(T2)** `DanceXi.T2` (`PartT.lean`).
* **(T3)** `DanceXi.T3` (`PartT.lean`).
* **(R0)** `DanceXi.R0` (`PartR.lean`).
* **(R1)** `DanceXi.R1` (`PartR.lean`).
* **(R2)** `DanceXi.R2` (`PartR.lean`).

All statements are as in the file; no hypothesis was added. Existentials "there is `Gk` with …"
are `∃ Gk, …`, and "the cokernel is isomorphic to …" is `Nonempty (… ≃ₗ[ℤ_[2]] …)`.
-/
