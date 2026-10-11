module

public import RequestProject.Conjugation.Defs
public import RequestProject.Conjugation.PartC1
public import RequestProject.Conjugation.PartC2
public import RequestProject.Conjugation.PartC4
public import RequestProject.Conjugation.PartD
public import RequestProject.Conjugation.PartX
public import RequestProject.Conjugation.PartT

/-!
# `C45_conjugation_and_general_eta.md` — conjugation by `η^D` along the dance, invertibility, and
# Theorem 10.12, first half, for every unit `η` (paper v8 §10.4)

Folder `RequestProject/Conjugation/`, namespace `Conjugation`. Nothing listed in the Setting is
redefined. Used directly: C40 `FormalOps.Bf` (its ring structure, `coef`, the scalar action,
`Bf.smul_mul`, `Bf.mul_smul`), `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`; C40b
`FormalDance.Agree`, `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`,
`finalM`, `paySys`, `L4_sigma`, `L5`; C13 `Dance.slots`, `Dance.slots_eq`, `Dance.splitIso`,
`Dance.mCount`; C3 `Rulers.oE`; C14 `Windows.Dset`, `Windows.Ids`; C32 `Families.ds`; C10
`Deficit.Mc`; C42 `InvFloors.oE_Dset_cons_false`, `InvFloors.oE_Dset_cons_true` (the floors of a
slot for `d :: ds`); C43 `PathSum.piF`, `XiOp`, `SigOp`, `coef_mul_split`,
`instOddUnitsPadicTwo`; C44 `Stability.hadOne`, `Stability.nest`, `Stability.F1`, `F1_gen`,
`Stability.T1`, `Stability.T2`, `Stability.sigOp_magree_paySys`.

## Encodings
* `cj u x` (`(cj u x).coef j f = u ^ j * x.coef j f`) and
  `cjSys c u w G s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj u (G s s')` are written exactly as in
  the file (`Defs.lean`).
* In (C4) the slot `q j = ⌊j / 2^m⌋` is `qSlot ds r j : Fin r`, and the final weights are
  `fun j => w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j)`, exactly as in the file. The
  recursive description `wkRec` is proved equal to it for every `r` (`wkRec_eq`).
* The bound `2^{−(α−1)}` is `(2 : ℝ) ^ (-(α - 1 : ℤ))` (norm of `ℚ_[2]`), as in C44; the nested
  pairs of (F1η) are C44's `Stability.nest ds s s'` (`D_{s'} ⊆ D_s`); the exponent of (F1η) is
  the integer `o(D_s) − o(D_{s'}) − (2^k − 1)` (`zpow`).

## Where each part is
* **(C1)** `PartC1.lean`: `cj_one`, `cj_add`, `cj_mul`, `cj_smul`, `cj_cj`, `cj_one_left`,
  `agree_cj`, `cjSys_one`, `cjSys_mul`, `cjSys_sub`, `cjSys_smul`, `magree_cjSys`; collected in
  `C1`.
* **(C2)** `PartC2.lean`: `twP_cjSys`, `twC_cjSys`, `twB_cjSys`, `twD_cjSys`, `vsplit_cjSys`, all
  **exact equalities**; collected in `C2`.
* **(C3)** `PartC2.lean`: `cleanStep_cjSys`, `cleanStep_vsplit_cjSys`; collected in `C3`.
* **(C4)** `PartC4.lean`: `C4` (and `C4_rec`, `wkRec_eq`).
* **(C5)** `PartC4.lean`: `finalM_cjSys`, `C5_one`; collected in `C5`.
* **(D0)** `PartD.lean`: `D0`. **(I)** `PartD.lean`: `I` (right inverse `rinv`, left inverse
  `linv`).
* **(X1)** `PartX.lean`: `X1_xi`, `X1_sig`, collected in `X1`. **(X2)** `X2`.
* **(T1η), (T2η), (F1η)** `PartT.lean`: `T_eta` (one `GSig` for all three), `T1eta`, `T2eta`,
  `F1eta`; `F1eta_gen` (more general).

## Hypotheses and generality
* (C1)–(C5), (D0): over any commutative ring `A`; `Fintype`/`DecidableEq` only where products or
  `1` of matrices occur. (I): over any field `K`.
* (X1): the `SigOp` half holds without `η ≠ 0` (`X1_sig`).
* Part T: all hypotheses of the file are used by `T_eta`. In particular «`Ξ`, `Σ` have two-sided
  inverses» and «the dance of `Σ` is clean» are not assumed: they are proved by (I) and by C40b
  (L4) with (D0). (F1η) alone needs only `α ≥ 1` and `η ≠ 0` and holds for every `GSig`
  (`F1eta_gen`).
-/
