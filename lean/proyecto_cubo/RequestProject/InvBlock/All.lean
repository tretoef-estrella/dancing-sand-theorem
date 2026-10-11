module

public import RequestProject.InvBlock.Defs
public import RequestProject.InvBlock.PartV1
public import RequestProject.InvBlock.PartV3

/-!
# `C41_inverse_block.md` — Lemma 10.8: the inverse block, as a lift identity along the dance
# (paper v8 §10.4)

Folder `RequestProject/InvBlock/`, namespace `InvBlock`. Nothing listed in the Setting is
redefined. Used directly: C13 `Dance.slots`, `Dance.splitIso` (through C40d's
`FormalProp.splitEquiv`); C18 `DPLattice`, `DPLattice.one`; C29 `Filt.T` (`T_zero` and its
defining equation); C32 `Families.ds` (`ds_zero` and its defining equation); C40 `FormalOps.Bf`;
C40b `FormalDance.MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `DanceRel`,
`finalM`; C40c `FormalAct.sysAct`, `pack`, `vpack`, `unitEquiv`, `N1`, `N2`, `A1`, `sysAct_mul`,
`sysAct_one`, `sysAct_sub`, `sysAct_smul`, `A3_conj`, `A4_apply`, `T1`, `T2`; the induction
pattern of C40d `FormalProp.Q1_aux`.

Encodings:
* A vector of `N^{⊕n}` is a function `n → N.ι → A`, a vector of `A^{ns}` a function
  `Fin ns → A`; linear maps are Mathlib's `→ₗ[A]`.
* `inj₀ x = pack (x, 0)` is `inj0`, `out₁ w = (pack.symm w).2` is `out1`,
  `lift v = pack (−sysAct N W B' (Q * twC G) v, v)` is `lift N W B' Q G`.
* `inH l r`, `outH l r` (`Defs.lean`) are defined by recursion on `l` (following the defining
  equations of `Filt.T`, `Families.ds`), and depend only on `l` and `r`; the type equalities
  `T A (2l'+1) = phi (T A l')`, `T A (2l'+2) = tensorV (phi (T A l'))` and the slot equalities
  are transported by the auxiliary `castLat` and `ri`.
* `k` is written `(Families.ds l).length`.

Where each part is:
* Definitions (new): `inH`, `outH` (`Defs.lean`).
* (V1) `V1`, (V2) `V2` (`PartV1.lean`).
* (V3) `V3`, (V4) `V4`, (V5) `V5` (`PartV3.lean`).

Hypotheses: (V1) and (V2) do not need the half `MAgree (Q * twP G) 1` of the clean step, which
is omitted there (more general). All other hypotheses of the file are used. The instances
`[IsDomain A] [CharZero A] [OddUnits A]` are needed to form `phi` and `T`; in (V5) `IsDomain K`
comes from `Field K`.
-/
