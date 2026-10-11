module

public import RequestProject.Mirror.Families
public import RequestProject.Mirror.Clocks
public import RequestProject.Mirror.Theorem
public import RequestProject.Mirror.Fit
public import RequestProject.Mirror.Exps
public import RequestProject.Mirror.Group

/-!
# `C37_the_mirror_that_doubles.md` — the mirror that doubles: Lemmas 9.8–9.9, Theorem 9.10 and
Corollary 1.7

Folder `RequestProject/Mirror/`, namespace `Mirror`.  Nothing listed in the Setting is redefined:
C1 `AntitonicFit.fit`, `ifit`, `toR`, `levelSet` (and the characterization `fit_kkt`,
`fit_eq_of_kkt`); C3 `Rulers.phi`, `v2`, `s2`, `kappa`, `oE`, `minOr`, `next`, `h`, `t1`, `hSum`,
`lam`, `xi`, `clock`; C7 `TheoremF.dancer`; C13 `Dance.mCount`; C14 `Windows.Ids`, `card_Ids`;
C16 `FamilyGroup.SC`, `Q`, `yPool`, `yPool0`; C17 `CubeLaplacian.K`, `Syl2`; C31 `FamDec.Vdot`,
`Vdot_odd`, `L`, `L_succ`, `m`, `M3`, `m_self`; C32 `Families.ds`, `ds_zero`, `ds_odd`, `ds_even`;
C33 `MainTheorem.XFam`, `M2equiv`, `S1_succ`, `S3_subset`, `S4equiv`, `castQ`; C36
`PodiumCor.smallExps`, `bigExps`, `famExps`, `exps` are used directly.  Listed items that turned
out not to be needed by name: C31 `M4`; C32 `B0b` (used through C33 `S1_succ`); C33 `M2`, `S1_lam`,
`S1_xi`, `S3_card` (used through `card_Ids`); C36 `E1`.

## Encodings

* Sequences are functions `ℕ → ℝ` / `ℕ → ℤ` read below their length, as in C1; the doubled
  sequence of `x` is `fun j => x (j / 2)`, of length `2 * N`.
* In Parts B, C, X, the quantities `J = i + o_D`, the shift `i = (2^e − 1 − λ) / 2`, `k`, `I`,
  `k'`, `I'` are written out; the identities of Part B are in `ℤ`.
* `S n` is written out as `CubeLaplacian.Syl2 (CubeLaplacian.K n)`; an isomorphism is
  `Nonempty (… ≃+ …)`.

## Where each statement is

* **Part A** (`Families.lean`): (A1) `A1` (items `A1_odd`, `A1_map`, `A1_m_succ`, `A1_m_zero`);
  (A2) `A2` (`A2_length`, `A2_zero_notMem`, `A2_Ids`, `A2_mCount`); (A3) `A3` (`A3_even`,
  `A3_odd`); (A4) `A4`; (A5) `A5` (`A5_h`, `A5_h_zero`, `A5_hSum`, `A5_hSum_insert`).
* **Part B** (`Clocks.lean`): (B1) `B1`; (B2) `B2`.
* **Part C** (`Theorem.lean`): (C1) `C1`.
* **Part F** (`Fit.lean`): (F1) `F1`; (F2) `F2`.
* **Part X** (`Exps.lean`): (X1) `X1`; (X2) `X2`; (X3) `X3`; (X4) `X4`; (X5) `X5`.
* **Part Y** (`Group.lean`): (Y1) `Y1`; (Y2) `Y2` (through `Y_core`, the torsion cancellation
  `cancel_torsion` and `QequivZMod : Q a ≃+* ZMod (2 ^ a)`).

## Hypotheses

* (A5): the items `h' t = h t` and `h'(D) = h(D)` do not need `I ⊆ range k` (stated without it);
  the items about `h' 0` and `h'(D ∪ {0})` use it.
* (C1), (X1)–(X3): `e ≥ 1` is kept as in the file; it follows from `λ < 2^e − 1`.
* (F1), (F2), (A3), (B1), (B2), (A1)–(A4), (X4), (X5), (Y1), (Y2): every stated hypothesis is used.
-/
