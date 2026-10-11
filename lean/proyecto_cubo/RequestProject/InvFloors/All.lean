module

public import RequestProject.InvFloors.Digits
public import RequestProject.InvFloors.Defs
public import RequestProject.InvFloors.PartF
public import RequestProject.InvFloors.PartC
public import RequestProject.InvFloors.PartC109

/-!
# `C42_floors_and_corollary_10_9.md` — the floors of `inH`, `outH`, and Corollary 10.9
# (paper v8 §10.4)

Folder `RequestProject/InvFloors/`, namespace `InvFloors`. Nothing listed in the Setting is
redefined. Used directly: C3 `Rulers.oE`; C13 `Dance.slots`, `Dance.mCount`, `Dance.splitIso`
(through C40d's `FormalProp.splitEquiv`); C14 `Windows.Dset`, `Windows.Ids`, `Windows.rank`,
`Windows.Ids_cons`, `Windows.mem_Ids`; C18 `DPLattice` (`ι`, `wt`, `Fd`, the axiom (W)),
`DPLattice.one`, `wtV`, `tensorV`; C20 `Doubling.phi` (`phiWt`); C29 `Filt.T` (`T_zero`, and its
defining equation); C32 `Families.ds` (`ds_zero`, its defining equation, (B0b)); C40 `FormalOps.Bf`,
`act`, `flD`; C40b `FormalDance.Agree`, `MAgree`, `DanceRel`, `finalM`; C40c `FormalAct.sysAct`,
`N2`, `A1`, `sysAct_mul`, `sysAct_one`, `pack`, `vpack`, `unitEquiv`; C41 `InvBlock.inH`, `outH`,
`inj0`, `out1`, `relab`, `castLat`, `ri`, `V5`.

Encodings:
* A vector of `T(l)^{⊕r}` is `Fin r → (T A l).ι → A`, a vector of `A^{ns}` is `Fin ns → A`
  (as in C41); basis vectors are `Pi.single`.
* `slotOf`, `inIdx`, `outIdx` (`Defs.lean`) are defined by the same well-founded recursion along
  `l` as `InvBlock.inH`, `InvBlock.outH`, and depend only on `l` and `r`. `inIdx` and `outIdx`
  are the cases `b = 0` and `b = 1` of one recursion `ioIdx b` (twist step: the index `(b, i)` of
  `Fin 2 × ι`; split step: `(a, (b, i))`, `a` the second component of
  `FormalProp.splitEquiv r`, as in `vpack`). The equalities of lattices are crossed by `castIdx`
  (the index form of C41's `castLat`), the slot equalities by `Fin.cast` (as C41's `ri`).
* `k` is written `(Families.ds l).length` and `m` is `Dance.mCount (Families.ds l)`; a final slot
  `j : Fin _` is read by `Windows.Dset` through its value `(j : ℕ)`.
* The constants of the word `γ l X Y` are `gamma l X Y` (`PartC.lean`), written exactly as in the
  file; the field `K` of (C109) is any field with `[CharZero K] [OddUnits K]`.

Where each part is:
* Definitions (new): `slotOf`, `inIdx`, `outIdx` (with `ioIdx`), `Defs.lean`.
* (F1) `F1`, (F2) `F2`, (F3) `F3`, (F4) `F4`, (F5) `F5`, (F6) `F6` (`PartC.lean`), from the
  inductions `F1_aux`, `F2_aux`, `F3_aux`, `floor_ioIdx`, `F6_nat` (`PartF.lean`) and the bit
  bookkeeping of `Digits.lean`.
* The constants of the word: `gamma` (`PartC.lean`).
* (C109) `C109` (`PartC109.lean`).

Hypotheses: all hypotheses of the file are used. (F3) and (F6) hold for every `r` and `j` with
no ring at all (`slotOf` and the floors do not involve `A`); (F6) is also proved for every
natural number in place of `j` (`F6_nat`, more general). In (C109) the bound `B ≥ l + 1` is used
to form the action `sysAct (T K l) l B` to which (V5) is applied; the conclusion does not depend
on `B`. The instances `[IsDomain A] [CharZero A] [OddUnits A]` are needed to form `T`; in (C109)
`IsDomain K` comes from `Field K`.
-/
