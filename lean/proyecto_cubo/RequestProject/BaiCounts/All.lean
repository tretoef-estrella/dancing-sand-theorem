module

public import RequestProject.BaiCounts.Layers
public import RequestProject.BaiCounts.Clocks
public import RequestProject.BaiCounts.Counts
public import RequestProject.BaiCounts.Family
public import RequestProject.BaiCounts.Corollary

/-!
# `C34_bais_counts.md` — Bai's two counts (Lemma 9.1 and Corollary 1.5)

Folder `RequestProject/BaiCounts/`, namespace `BaiCounts`.  Nothing listed in the Setting is
redefined: C1 `AntitonicFit.ifit`; C3 `Rulers.clock`, `xi`, `oE`, `hSum`, `phi`, `kappa` (and
`lam` through `xi`); C7 `TheoremF.dancer` (through the pooled clocks), `lemma_0a`; C13
`Dance.mCount`, `Idx`; C14 `Windows.Ids`; C16 `FamilyGroup.SC`, `Q`, `yPool`, `yPool0`; C17
`CubeLaplacian.K`, `Syl2`; C31 `FamDec.L`, `m`, `Vdot`, `M3`, `L3`, `L4`; C32 `Families.ds`,
`ds_zero`, `ds_odd`, `ds_even`, `B0b`; C33 `MainTheorem.XFam`, `M2`, `S2_length`, `S3_subset`,
`S4` (through its explicit equivalence `S4equiv`) and `S4_Q0` are used directly.  Listed items
that turned out not to be needed: C31 `M4`, `L1`, `L2` and C33 `M1`, `S1_lam`, `S2`, `S3_card`.

## Encodings

* `twoPow G j : AddSubgroup G` is `2^j G = {2^j • x | x ∈ G}`; the layers are
  `l0 G = Nat.card (G ⧸ twoPow G 1)` and
  `l1 G = Nat.card (twoPow G 1 ⧸ (twoPow G 2).addSubgroupOf (twoPow G 1))` (`Layers.lean`).
* `λ` is written `lam`; `k λ = (ds λ).length`, `|I λ| = Dance.mCount (ds λ)`,
  `N λ = 2 ^ Dance.mCount (ds λ)` are written out.
* `c1 lam` is `c₁(λ)`; `aN n` is `a n = 2 ^ (n − 2) − 2 ^ ((n − 2) / 2)`.
* Sums over the positions of `L n` are sums over `j : Fin (FamDec.L n).length`, with
  `λ_j = (FamDec.L n).get j`.
* `ℤ_[2]` is `PadicInt 2`; `S n` is `CubeLaplacian.Syl2 (CubeLaplacian.K n)`, written out.

## Index

* **Part A** (`Clocks.lean`): (A1) `A1` (and the more general `A1_general`, without the
  hypothesis `1 ≤ i ∨ D ≠ ∅`); (A2) `A2`; (A3) `A3_pos`, `A3_zero`.
* **Part F** (`Family.lean`): (F1) `F1`; (F2) `F2`.  The bookkeeping (`Layers.lean`):
  `l0_congr`, `l1_congr`, `l0_prod`, `l1_prod`, `l0_pi`, `l1_pi`, `l0_Q`, `l0_Q_zero`, `l1_Q`,
  `l1_Q_le_one`, `l0_padic`, `l1_padic`.
* **Part S** (`Counts.lean`): (S1) `S1`; (S2) `S2`; (S3) `S3`, `S3_short`.
* **Part B** (`Corollary.lean`): (B1) `B1`; (B2) `B2`.

Unused hypothesis: in (A1) the hypothesis `1 ≤ i ∨ D ≠ ∅` is kept as in the file but is not used
(`A1_general`).  The hypothesis `1 ≤ k` is needed: `A1_k_zero` shows that for `k = 0`,
`I = D = ∅`, `i = 1` the clock is `1`.
-/
