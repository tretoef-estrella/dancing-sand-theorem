module

public import RequestProject.PodiumCor.Defs
public import RequestProject.PodiumCor.Layers
public import RequestProject.PodiumCor.Dictionary
public import RequestProject.PodiumCor.Mult
public import RequestProject.PodiumCor.Shift2
public import RequestProject.PodiumCor.Aux
public import RequestProject.PodiumCor.Bounds
public import RequestProject.PodiumCor.Counting
public import RequestProject.PodiumCor.Corollary
public import RequestProject.PodiumCor.Gao

/-!
# `C36_the_podium_corollary.md` — the podium: Lemma 9.7 and Corollary 1.6

Folder `RequestProject/PodiumCor/`, namespace `PodiumCor`.  Nothing listed in the Setting is
redefined: C3 `Rulers.phi`, `v2`, `kappa`, `clock`, `oE`, `lam` (and `s2`, `xi`, `minOr`); C13
`Dance.mCount`; C14 `Windows.Ids`, `Ids_cons`, `card_Ids`; C16 `FamilyGroup.yPool`, `yPool0`, `Q`,
`SC`; C17 `CubeLaplacian.K`, `Syl2`; C31 `FamDec.Vdot`, `L`, `m` and its lemmas (`M3`, `L1`,
`m_self`, `mem_Vdot`, `count_succ_Vdot`, `count_map_odd`, `count_L_succ`,
`sum_map_eq_count_mul`); C32 `Families.ds`, `ds_zero`, `ds_odd`, `ds_even`; C33
`MainTheorem.XFam`, `M2`, `M3_support`, `S1_lam`, `S1_succ`, `S2_length`, `S3_subset`, `S3_card`,
`S4equiv` (the explicit form of (S4)); C34 `BaiCounts.twoPow`, `l0`, `l1` and the layer bookkeeping
(`card_quot_of_surj`, `card_quot_congr`, `card_quot_prod`, `card_quot_pi`, `mem_twoPow_*`,
`card_eq_two`, `mkQ_eq_zero`); C35 `Podium.P`, `tAt`, `Y`, `Ld`, `Ld_one`, `Y_add_oE_P`,
`card_P`, `P_zero`, `lam_add_one`, `two_pow_dvd_oE`; C35b `PodiumWalk.C1`, `T1`, `T2`, `T3`, `Z1`,
`Z2` are used directly.  Listed items that turned out not to be needed: C33 `M1`, `S4_Q0`; C34
`A3_pos`, `A3_zero`, `l0_congr`, `l0_prod`, `l0_pi`, `l0_padic`, `l0_Q` (Part D reproves them for
every layer); C35 `La`, `Lb`, `Lc_*` (used only through (Ld)); C35b `H1`, `H2`.

## Encodings

* `layer G j := Nat.card (twoPow G j ⧸ (twoPow G (j + 1)).addSubgroupOf (twoPow G j))` and
  `cExp G r := sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ layer G (e − 1)}`, exactly as in the file.
* `smallExps`, `bigExps`, `famExps`, `exps n` are `Multiset ℕ`, defined literally as in the file
  (`s = (Windows.Ids (ds λ)).card`, `N = 2 ^ s`; the big exponents as `Multiset.map` over
  `(Finset.range _).val`).
* `gmax N : ℤ` is `(Finset.Ico 1 N).sup' _ Rulers.phi` for `N ≥ 2` and `0` otherwise; (g0) is
  `g0`.
* `S n` is `CubeLaplacian.Syl2 (CubeLaplacian.K n)` (written out), `c r` is
  `cExp (S n) r : ℕ`, compared with integers via the cast `(c r : ℤ)`; `G = gmax (n − 1)` is
  written out.  Brackets `[P]` are `if P then 1 else 0`.  "The `r`-th largest exponent" is
  `((exps n).sort (fun a b => b ≤ a)).getD (r − 1) 0`.
* `N` for a family in Part B is `2 ^ Dance.mCount (ds λ)` (equal to `2 ^ s` by C33 `S3_card`), as
  in C35b.

## Where each statement is

* **Definitions**, (g0): `Defs.lean` (`layer`, `cExp`, `smallExps`, `bigExps`, `famExps`, `exps`,
  `gmax`, `g0`).
* **Part D** (`Layers.lean`): (D0) `D0` (`D0_zero`, `D0_one`); (D1) `D1` (`layer_congr`,
  `layer_prod`, `layer_pi`, `layer_padic`, `layer_Q`).
* **Part E** (`Dictionary.lean`): (E1) `E1`; (E2) `E2`; (E3) `E3`; general forms `cExp_le_iff`,
  `cExp_eq_getD` (for any group whose layers are `2 ^ #{x ∈ M : j < x}`).
* **Part L** (`Mult.lean`): (L1) `L1`; (L2) `L2`; (L3) `L3`.
* **Part W** (`Shift2.lean`): (W1) `W1`; (W2) `W2`.
* **Part B** (`Bounds.lean`): `B0`, `B1`, `B2`, `B3`, `B4`, `B5`, `B6`, `B7`, `B8`.
* **Part P** (`Corollary.lean`, with the counting in `Counting.lean`): (P1) `P1`; (P2) `P2`;
  (P3) `P3`.
* **Part G** (`Gao.lean`): (G1) `G1`; (G2) `G2`; (G3) `G3` (the case `n = 3` through
  `exps_three : exps 3 = {3, 3, 1}`).

## Hypotheses

* (L1): `1 ≤ n` is kept but not used (`m n n = 1` for every `n`).
* (B0), (B1): `λ ≥ 1` is kept but not used (it follows from `m λ n ≠ 0` by C31 (M3)).
* (B3): the file's `s ≥ 1` is omitted; both parts hold without it.
* All other stated hypotheses are used.
-/
