module

public import RequestProject.FormalDance.Defs
public import RequestProject.FormalDance.PartC
public import RequestProject.FormalDance.PartL1
public import RequestProject.FormalDance.PartL2
public import RequestProject.FormalDance.PartL

/-!
# `C40b_the_formal_dance_of_payment_systems.md` — the formal dance of payment systems
# (paper v8 §10.3, Lemma 10.6)

Folder `RequestProject/FormalDance/`, namespace `FormalDance`. Nothing listed in the Setting is
redefined. Used directly: C40 `FormalOps.Bf` with `Bf.instRing`, its `A`-action and
`Bf.instAlgebra`, `Bf.fd`, `Bf.dg`, `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime`, `flD`,
`act`; C18 `DPLattice` (its weight condition (W), `isDP.W_F`, in (C4)); C20 `Doubling.dfi` (`dfi_zero`,
`dfi_one`); C11 `Payment.pT`, `Payment.κT`; C12 `Split.pSp`, `Split.κSp` (with their value
lemmas `pSp_A`, `pSp_C`, `κSp_AA`, `κSp_CC`, `κSp_CA`, `κSp_AC`, `shiftP`, `shiftK`); C13
`Dance.slots`, `Dance.slots_eq`, `Dance.splitIso`, `Dance.relabP`, `Dance.relabK`,
`Dance.danceAux`, `Dance.dance`, `Dance.Mfin`, `Dance.pσ`, `Dance.κσ`, `Dance.mCount`.
C40's theorems `B4`, `T1`, `V1` are the motivation of the definitions (the twist blocks and the
V-split are read off them) and are not needed in the proofs.

## Encodings (`Defs.lean`)
* A formal operator is `x : Bf A` (`x.coef m f`, coefficient of `F^{(m)}` at the floor `f`);
  matrices are Mathlib's `Matrix n n (Bf A)` with Mathlib's (non-commutative) ring structure and
  the entrywise action of `A`; `(2 : A) • G` is this action.
* `Agree`, `MAgree`, `ext0`, `paySys`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`,
  `Clean`, `finalM` are written exactly as in the file. Payment systems live on index types with a
  `LinearOrder` (whose decidable equality is used for `s = s'`).
* `DanceRel ds r G Gk` is defined by recursion on `ds` with exactly the three clauses of the
  file; `Gk` is a matrix on `Fin (Dance.slots ds r)`.
* In (L2) the split payment system is
  `PS = fun q q' => paySys (Split.pSp p) (Split.κSp p κ) (toLex q) (toLex q')`, a matrix on
  `n × Fin 2` read through `toLex` (with the lexicographic order on `Lex (n × Fin 2)`).

## Where each part is
* **Part C** (`PartC.lean`): `C1`, `C2`, `C3`, `C4` (with the individual lemmas `Agree.add`,
  `Agree.mul`, …, `MAgree.vsplit`).
* **Part L**: `L1` (`PartL1.lean`, also `L1_twP`, `L1_schur`), `L2` (`PartL2.lean`, also
  `L2_twP`, and the exact equality `L2_schur_eq`), `L3`, `L4` (with `L4_dance`, `finalM_paySys`,
  `L4_sigma`, `L4_sigma_clean`), `L5`, `L6` (`PartL.lean`).

## Hypotheses and generality
* (C4): only `N.wt i ≤ W` of (top W) is used; the parity half `Even (W − N.wt i)` is not needed.
* (L1), (L2): the pivot equalities `twP … = 1` hold without finiteness of `n`; the second
  equality of (L2) holds exactly, not only up to agreement (`L2_schur_eq`).
* (L5): the no-2-torsion hypothesis is used (to cancel the factor `2` in `CleanStep`).
* (L6): `IsUnit u` is used (to form `Q' = u⁻¹ • Q`).
-/
