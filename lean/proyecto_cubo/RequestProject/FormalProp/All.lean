module

public import RequestProject.FormalProp.Aux
public import RequestProject.FormalProp.PartQ0
public import RequestProject.FormalProp.PartQ1
public import RequestProject.FormalProp.PartQ

/-!
# `C40d_proposition_10_7.md` — Proposition 10.7: the cokernel of a system with a clean dance on
# `T(l)` (paper v8 §10.3)

Folder `RequestProject/FormalProp/`, namespace `FormalProp`. Nothing listed in the Setting is
redefined. Used directly: C13 `Dance.nLen` (as `List.length`), `Dance.mCount`, `Dance.slots`,
`Dance.slots_eq`, `Dance.splitIso`, `Dance.dance`, `Dance.Mfin`, `Dance.pσ`, `Dance.κσ` and the
helpers of `Dance.D2_clocks` (`Dance.PQ`, `Dance.pqCast`, `Dance.funFinEquiv`,
`Dance.quotSmulTopCongr`); C18 `DPLattice`, `DPLattice.one`; C29 `Filt.T` with `T_zero`, `T_odd`,
`T_even`; C32 `Families.ds` with `ds_zero`, `ds_odd`, `ds_even`; C34 `BaiCounts.S1` (for (Q0));
C40 `FormalOps.Bf`; C40b `FormalDance.MAgree`, `CleanStep`, `vsplit`, `DanceRel`, `finalM`,
`paySys`, `L4_sigma_clean`; C40c `FormalAct.sysAct`, `quotEquivConj`, `N2`, `A1`, `A3equiv`,
`A4equiv`, `A4`, `S1equivQ`, `S2equivQ`. (C13 `Dance.card_Idx` enters through C34's `S1`; C40's
`act_bound`, C40b's `L6` and C40c's `pack`, `vpack`, `N1`, `A2`, `T1`, `T2` enter only through
C40c's `S1equivQ`, `S2equivQ`, and are not needed directly.)

## Encodings
* `k = (Families.ds l).length` (`= Dance.nLen (Families.ds l)`, an `abbrev`) and
  `m = Dance.mCount (Families.ds l)` are written out in each statement.
* A vector of `T(l)^{⊕r}` is `Fin r → (T A l).ι → A`; the cokernel of `f` is
  `M ⧸ LinearMap.range f`; the submodule `c M` is `(c • ⊤ : Submodule A M)`; `(2 : A) ^ h • f` is
  the scalar multiple of a linear map, as in C40c.
* The direct sum `⊕_{a}` of the clocks is the dependent product `(a : Fin k) → …` (a finite
  product). In the proofs a clock `(Fin a → A) ⧸ 2^e·⊤` is C13's `Dance.PQ A a e` (an `abbrev`).
* The action on `T A l` is taken with top `W = (l : ℤ)` and any bound `B ≥ l + 1`.
* Each statement is "`Nonempty (… ≃ₗ[A] …)`".

## Where each part is
* **(Q0)** `Q0` (`PartQ0.lean`).
* **(Q1)** `Q1` (`PartQ.lean`), from the induction `Q1_aux` (`PartQ1.lean`).
* **(Q2)** `Q2` (`k ≥ 1`) and `Q2_zero` (`k = 0`) (`PartQ.lean`).
* **(Q3)** `Q3` (`PartQ.lean`).
* **(Q4)** `Q4` (`PartQ.lean`).

## Instances and hypotheses
* `[IsDomain A] [CharZero A] [OddUnits A]` are needed to form `Filt.T` (as the file says).
* In (Q1)–(Q4) every hypothesis is used. The bound `B ≥ l + 1` is used directly at every level
  (it is exactly the hypothesis `2 * BN ≤ B`, resp. `2 * BN + 1 ≤ B`, of C40c (S1), resp. (S2),
  and `1 ≤ B` of (A4)), so C40's `act_bound` is not needed.
* (Q2), case `k = 0`, is stated for `T A 0` and every `G` with `B ≥ 1`, without a dance
  hypothesis (more general: `DanceRel [] r G Gk` is not needed, `finalM G` is used directly).
-/
