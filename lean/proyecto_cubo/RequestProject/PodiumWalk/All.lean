module

public import RequestProject.PodiumWalk.Walk
public import RequestProject.PodiumWalk.Head
public import RequestProject.PodiumWalk.Steps
public import RequestProject.PodiumWalk.Shift1
public import RequestProject.PodiumWalk.Shift0

/-!
# `C35b_the_podium_walk.md` — the podium walk (Propositions 9.3, 9.4 and 9.6)

Folder `RequestProject/PodiumWalk/`, namespace `PodiumWalk`.  Nothing listed in the Setting is
redefined: C1 `fit`, `ifit`, `toR`, `levelSet`, `sum_levelSet_fit`, `fit_nonIncr`, `concat`,
`mirror`, (A2); C3 `Rulers.phi`, `oE`, `minOr`, `h`, `lam`, `clock`, `proposition_5_3`; C7
`TheoremF.dancer`, `lemma_0a`, `lemma_0b`, `xHseq`, `JHseq`, `dWalk`, `theorem_F0` (W1)–(W3),
`theorem_F1` (Cut); C8 `Potential.yhat`; C9 `CellFloor.lemma_7_9_I1`–`I3`, `cellClock`, `cellShift`,
`yhatSharp`, `dancer_inj`; C6 `Houses.JH`, `d1`, `tau`, `typ`, `kap`, `h_erase`, `h_max`,
`typ_kap_max`; C13 `Dance.mCount`; C14 `Windows.Ids`, `card_Ids`, `lt_of_mem_Ids`; C15
`DanceSmith.xClk`, `yHat`, `Cst`, `cellClock_eq_xClk`, `ifit_cellClock`; C16 `FamilyGroup.yPool`,
`yPool0`, `fit_add_const`, `R1`, `R2`; C32 `Families.ds`; C33 `MainTheorem.S1_lam`; C35 `Podium.psi`,
`P`, `tAt`, `Y`, `La`, `M5`, `P_card_self`, `card_P` are used directly.

## Encodings

* The family `λ` is `lam : ℕ`, `d = Families.ds lam`, `k = d.length`, `I = Windows.Ids d`,
  `s = I.card`, `N = 2 ^ Dance.mCount d` (`= 2 ^ s` by C14 `card_Ids`).
* `Y l` is `Podium.Y k I l`, `t₁` is `Podium.tAt k I 0`, the dancer of rank `p` is
  `TheoremF.dancer I p`, the pooled clocks are `FamilyGroup.yPool d i p` and
  `FamilyGroup.yPool0 d q`, and the raw clocks are `Rulers.clock k I i (TheoremF.dancer I q)`.
* A sum over `q < 2 ^ l` is a sum over `Finset.range (2 ^ l)`.
* A maximum is stated with an explicit witness: «`v = max_{l ∈ L} f l`» is
  `(∃ l₀ ∈ L, v = f l₀) ∧ ∀ l ∈ L, f l ≤ v`, the ranges `L` being written with `≤` bounds.
* Every statement is also proved for an arbitrary digit list `ds : List Bool` (names `*_ds`),
  with `λ` replaced by `Rulers.lam k I` in (C1); the statements for `λ` follow by `d = ds λ`.
* Auxiliary (not in the file): `tailVal k I l := −ψ(I ∖ P_l)`, with `k + K + tailVal k I l = φ(Y_l)`
  (`phi_Y`, from C35 `La`), used for the walks of the houses `(I, k, 0, 1)` (`house_T`) and
  `(I, k, K − 1, 1)` (`house_Z`); `house_head` is the dyadic first level set of every house.

## Where each statement is

* **Part H** (`Head.lean`): (H1) `H1` (general: `H1_ds`); (H2) `H2` (`H2_ds`).
* **Part T** (`Shift1.lean`): (T1) `T1`; (T2) `T2`; (T3) `T3` (and `T1_ds`, `T2_ds`, `T3_ds`).
* **Part Z** (`Shift0.lean`): (Z1) `Z1`; (Z2) `Z2` (and `Z1_ds`, `Z2_ds`).
* **Part C** (`Head.lean`): (C1) `C1` (`C1_ds`).

## Hypotheses

* `λ ≥ 1` is used by none of the statements; it is omitted (all statements hold for every `λ`).
* (T2) is stated without `1 ≤ s` and (Z2) without `2 ≤ s`: they follow from `1 ≤ p < N` and from
  `1 ≤ q < N − 1` respectively.  (Z1) uses `1 ≤ s`; (T3) uses `0 ∈ I`; (H1), (H2), (C1) use
  `i ≥ 1`.
-/
