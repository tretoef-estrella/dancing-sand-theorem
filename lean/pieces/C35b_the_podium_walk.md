# C35b — The podium walk (Propositions 9.3, 9.4 and 9.6)

Piece C35b of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §9.2). Folder `RequestProject/PodiumWalk/`, namespace `PodiumWalk`.

The arithmetic of §9.2 is C35 (`Podium`). This piece is the part that walks through the fit of §7: the pooled big clocks at shift `1` (Proposition 9.3), at shift `0` (Proposition 9.4), and the ceiling of every big clock at every shift `i ≥ 1` (Proposition 9.6, including its step (H): the head of the fit is dyadic).

## Setting (reused, not redefined)

- C1 (`AntitonicFit`): `fit`, `ifit`, `toR`, `levelSet`, `NonIncr`, `IsLevelInterval`, the level-set lemmas, `lemma_7_1`, `sum_levelSet_fit`.
- C3 (`Rulers`): `phi`, `kappa`, `oE`, `minOr`, `h`, `lam`, `clock`, `proposition_5_3`, `proposition_5_4_c`.
- C7–C9 (`TheoremF`, `Potential`, `CellFloor`): `dancer`, `lemma_0a`–`lemma_0e`, the houses and the walk `theorem_F0` (W0)–(W3), `theorem_F1` (Λ), (Cut), `Lemma 7.9` (`lemma_7_9_I1`–`I3`), `yhatSharp`, `xSharp`.
- C13 (`Dance`): `mCount`. C14 (`Windows`): `Ids`, `card_Ids`, `lt_of_mem_Ids`.
- C15 (`DanceSmith`): `xClk`, `yHat`, `Cst`, `yHatS`. C16 (`FamilyGroup`): `yPool`, `yPool0`, `R0`, `R1`, `R2`.
- C32 (`Families`): `ds`. C33 (`MainTheorem`): `S1_lam`, `S2_length`, `S3_subset`, `S3_card`, `S5_order`, `S5_zero`.
- C35 (`Podium`): `psi`, `P`, `tAt`, `Y`, `clear`, `P0`, `La`, `Lb`, `Lc_*`, `Ld`, `Ld_one`, `K`, `M1`–`M5`.

Throughout: `λ ≥ 1`; `d := Families.ds λ`, `k := d.length` (so `k ≥ 1`), `I := Windows.Ids d` (so `I ⊆ range k`, `Rulers.lam k I = λ`), `s := I.card = Dance.mCount d`, `N := 2 ^ s`. `Y l := Podium.Y k I l`, `t₁ := Podium.tAt k I 0 = Rulers.minOr k I`. The dancer of rank `p` is `TheoremF.dancer I p`; the pooled big clocks are `FamilyGroup.yPool d i p` (`p < N`, shift `i ≥ 1`) and `FamilyGroup.yPool0 d q` (`q < N − 1`, the dancer of rank `q + 1`, shift `0`). Maxima are written with explicit witnesses (no `sup`).

## Part H — the head of the fit is dyadic (step (H) of Proposition 9.6)

**(H1)** For `i ≥ 1`: there is `l ≤ s` such that for every `p < 2 ^ l`,
`2 ^ l * FamilyGroup.yPool d i p = Σ_{q < 2 ^ l} Rulers.clock k I i (TheoremF.dancer I q)`.
(The first level set of the real fit of the raw clocks is `{D : D ⊆ P_l}`, i.e. the positions `0, …, 2^l − 1`, and its mean is an integer.)

**(H2)** For `i ≥ 1` and `p < N`: `FamilyGroup.yPool d i p ≤ FamilyGroup.yPool d i 0`.

*Sketch.* In the base cell, by induction along step 1 of the proof of Theorem 7.8 (C7 `theorem_F0` (W3): the fit of the house is the concatenation of `max(Z₁, 0)` and the mirrored `min(…, 0)`), which keeps the level sets of the fit of the smaller house `H'` because `d₁` changes only at strict cuts (Lemma 7.2(b)); if `Z₁ ≤ 0` on the whole first half, the first level set is everything. The penalty shift of a real cell changes only at strict cuts (Theorem 7.8 (Cut)), so it keeps the level sets. The mean is an integer by Lemma 7.9 (C9). (H2) is the antitonicity of the integer fit.

## Part T — shift 1 (Proposition 9.3)

**(T1)** `FamilyGroup.yPool d 1 0 = Rulers.phi (Y l₀)` for some `l₀ ≤ s`, and `Rulers.phi (Y l) ≤ FamilyGroup.yPool d 1 0` for every `l ≤ s`. (`e(∅) = max_{0≤l≤s} φ(Y_l)`.)

**(T2)** If `1 ≤ s`, for every `1 ≤ p < N` there is `l` with `1 ≤ l ≤ s` and `FamilyGroup.yPool d 1 p ≤ Rulers.phi (Y l)`. (`e(D) ≤ max_{1≤l≤s} φ(Y_l)` for `D ≠ ∅`.)

**(T3)** If `0 ∈ I`: `FamilyGroup.yPool d 1 1 = Rulers.phi (Y l₁)` for some `1 ≤ l₁ ≤ s`, and `Rulers.phi (Y l) ≤ FamilyGroup.yPool d 1 1` for every `1 ≤ l ≤ s`. (`e({0}) = max_{1≤l≤s} φ(Y_l)`; the dancer of rank `1` is `{t₁} = {0}`.)

*Sketch.* At `i = 1`, `m = 0`, `ℓ = 0`: in the house `(I, k, 0, 1)` every window has type `0` with `κ_t = 1`, no carry is born (Lemma 7.6) and `J ≡ 0`, so the cell is its base cell and step 1 at level `j` (digit `t_j`) reads `ŷ_j(D₀) = max(ŷ_{j−1}(D₀) − ψ_{t_j}, 0)`, `ŷ_j(D₀ ∪ {t_j}) = min(ŷ_{j−1}(D₀) + ψ_{t_j}, 0)`; `e(D) = k + K + ŷ_s(D)` and `k + K = φ(λ + 1) + ψ(I)`; then Lemma 9.2(a) (C35 `La`).

## Part Z — shift 0 (Proposition 9.4)

**(Z1)** If `1 ≤ s`: with `v := FamilyGroup.yPool0 d 0` (the dancer `{t₁}`),
`Rulers.phi (Y 1) − 2 ^ t₁ ≤ v`, `Rulers.phi (Y l) ≤ v` for every `2 ≤ l ≤ s`, and
`v = Rulers.phi (Y 1) − 2 ^ t₁ ∨ ∃ l, 2 ≤ l ∧ l ≤ s ∧ v = Rulers.phi (Y l)`.

**(Z2)** If `2 ≤ s`, for every `1 ≤ q < N − 1` there is `l` with `2 ≤ l ≤ s` and `FamilyGroup.yPool0 d q ≤ Rulers.phi (Y l)`.

*Sketch.* By Theorem 7.10 / C16 `R2`, the clocks are those of the house `H^♯ = (I, k, K − 1, 1)` shifted by `k + K`, with the dancer `∅` deleted after pooling. In `H^♯` every window has type `1` and is saturated (`κ_t = h_t`, `τ_t = −2^t`), and `J' = [D₀ ≠ ∅]` at every level, so `d₁(D₀) = 2^{t_j} − h_{t_j}[D₀ ≠ ∅]`. At level 1, `ŷ₁({t₁}) = −2^{t₁}`; at levels `j ≥ 2` a dancer `D₀ ≠ ∅` of the first half follows `y_j = max(y_{j−1} − ψ_{t_j}, 0)`; and `k + K − Σ_{j>l} ψ_{t_j} = φ(Y_l)`.

## Part C — the ceiling (Proposition 9.6)

**(C1)** For `i ≥ 1` and `p < N` there is `y` with `1 ≤ y ≤ λ + i` and `FamilyGroup.yPool d i p ≤ Rulers.phi y`.

(In the cube `Q_n` the family `λ` sits at shift `i = (n − λ)/2`, so `λ + i = n − i`: every big clock at a shift `i ≥ 1` is at most `g(n − i + 1) = max_{1≤y≤n−i} φ(y)`.)

*Sketch.* (H2) and (H1) reduce to the mean over `D ⊆ P_l`; C35 `M2`, `M5` with `G := max_{1≤y≤λ+i} φ(y)`.

## Notes

- Nothing is cited. The arithmetic is C35; the fit and the walk are C1, C7–C9; the pooled clocks are C16.
- The dancer of rank `p < 2^l` is a subset of `P_l` (the bits of `p` placed on the `l` smallest digits), so «positions `0, …, 2^l − 1`» and «`D ⊆ P_l`» are the same set (C7 `lemma_0c`, `lemma_0e`).
- Brute force (`chkC35b.py`, from §1.2 only, independent of the Lean files): (T1)–(T3), (Z1), (Z2), (C1) and (H) (first PAVA block of size `2^l`, mean of the raw clocks) for every `1 ≤ λ < 1100`, `1 ≤ i ≤ 8`: 22 447 checks, 0 failures. Controls that fire: (T1) with the maximum over `l ≥ 1`; (Z1) without `− 2^{t₁}`; (C1) with the range `[1, λ + i − 1]`; (H) «the first level set is a single dancer».
