# C40d — Proposition 10.7: the cokernel of a system with a clean dance on T(l) (paper v8 §10.3)

*Lean piece C40d of the Dancing Sand Theorem. Grepy Escribano, 9 October 2026. Folder `RequestProject/FormalProp/`, namespace `FormalProp`. Do not change any earlier file.*

Proposition 10.7: if the dance of a system `G` of size `r` on `T(l)` is clean, then `coker(G on T(l)^{⊕r}) ≅ ⊕_{a=1}^{k−1} (ℤ/2^a)^{r·2^{|I|+k−1−a}} ⊕ coker(2^k M_w(G))`. C40c proved one move (a twist move and a split move) as a Schur step on cokernels; this piece runs the induction along `T(l)` and counts the ranks, as Proposition 4.3 (C13 `Dance.D1_scaled_dance`, `Dance.D2_clocks`) does for payment systems.

## Setting (reuse; do not redefine)

- C13 `Dance.nLen`, `Dance.mCount`, `Dance.slots`, `Dance.slots_eq`, `Dance.splitIso`, `Dance.dance`, `Dance.Mfin`, `Dance.pσ`, `Dance.κσ`, `Dance.card_Idx`, and the proof pattern of `Dance.D1_aux`, `Dance.D2_clocks`.
- C18 `DPLattice` (with `Fintype ι`), `DPLattice.one`.
- C29 `Filt.T` (`T_zero`, `T_odd`, `T_even`); C32 `Families.ds` (`ds_zero`, `ds_odd`, `ds_even`); C34 `BaiCounts.S1`.
- C40 `FormalOps.Bf`, `act` (with `act_bound`).
- C40b `FormalDance.MAgree`, `CleanStep`, `vsplit`, `DanceRel`, `Clean`, `finalM`, `paySys`, `L4_sigma_clean`, `L6`.
- C40c `FormalAct.sysAct`, `pack`, `vpack`, and the theorems `N1`, `N2`, `A1`, `A2`, `A3`, `A4`, `T1`, `T2`, `S1`, `S2` (with their explicit equivalences `S1equivQ`, `S2equivQ`, `A3equiv`, `A4equiv`).

`A` is a commutative ring with `[IsDomain A] [CharZero A] [OddUnits A]` (needed by `Filt.T`). Write `k := (Families.ds l).length = Dance.nLen (Families.ds l)` and `m := Dance.mCount (Families.ds l)` (`m = |I|`). The action on `T A l` is taken with top `W = (l : ℤ)` and any bound `B ≥ l + 1` (C40c (N2)).

## Statements to prove

- **(Q0)** For every `l`, `Fintype.card (T A l).ι = 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l))`.
- **(Q1) Proposition 10.7, scaled.** For all `l r : ℕ`, `G : Matrix (Fin r) (Fin r) (Bf A)`, `Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf A)` with `DanceRel (Families.ds l) r G Gk`, every `B ≥ l + 1` and every `h : ℕ`:
  `Nonempty (((Fin r → (T A l).ι → A) ⧸ LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B G)) ≃ₗ[A] (((a : Fin k) → (Fin (r * 2 ^ (k + m − 1 − a)) → A) ⧸ (2 : A) ^ (h + (a : ℕ)) • (⊤ : Submodule A (Fin (r * 2 ^ (k + m − 1 − a)) → A))) × ((Fin (Dance.slots (Families.ds l) r) → A) ⧸ LinearMap.range ((2 : A) ^ (h + k) • Matrix.mulVecLin (finalM Gk)))))`.
- **(Q2) Proposition 10.7 as printed** (`h = 0`, the factor `a = 0` is the zero module). For `l`, `r`, `G`, `Gk`, `B` as in (Q1) and `k ≥ 1`:
  `Nonempty (((Fin r → (T A l).ι → A) ⧸ LinearMap.range (sysAct (T A l) (l : ℤ) B G)) ≃ₗ[A] (((a : Fin (k − 1)) → (Fin (r * 2 ^ (k + m − 2 − a)) → A) ⧸ (2 : A) ^ ((a : ℕ) + 1) • (⊤ : Submodule A (Fin (r * 2 ^ (k + m − 2 − a)) → A))) × ((Fin (Dance.slots (Families.ds l) r) → A) ⧸ LinearMap.range ((2 : A) ^ k • Matrix.mulVecLin (finalM Gk)))))`.
  For `k = 0` (`l = 0`): `Nonempty (((Fin r → (T A 0).ι → A) ⧸ LinearMap.range (sysAct (T A 0) 0 B G)) ≃ₗ[A] ((Fin r → A) ⧸ LinearMap.range (Matrix.mulVecLin (finalM G))))`.
- **(Q3) Associated final matrices.** For `G₁ G₂ : Matrix (Fin r) (Fin r) (Bf A)` with `DanceRel (Families.ds l) r G₁ Gk₁`, `DanceRel (Families.ds l) r G₂ Gk₂`, and matrices `P Q : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) A` with `IsUnit P.det`, `IsUnit Q.det` and `finalM Gk₂ = P * finalM Gk₁ * Q`: for every `B ≥ l + 1` and every `h`, the cokernels of `(2 : A) ^ h • sysAct (T A l) (l : ℤ) B G₁` and `(2 : A) ^ h • sysAct (T A l) (l : ℤ) B G₂` are isomorphic (`Nonempty (… ≃ₗ[A] …)`). («Two systems of the same size on `T(l)` with clean dances and final matrices of equal Smith form have isomorphic cokernels.»)
- **(Q4) The operator `σ`.** For all `l α i : ℕ`, every `B ≥ l + 1` and every `h`, with `ds := Families.ds l`, `k`, `m` as above and `M := Dance.Mfin (Dance.dance ds 1 (Dance.pσ α i) Dance.κσ).1 (Dance.dance ds 1 (Dance.pσ α i) Dance.κσ).2` (a matrix on `Fin (1 * 2 ^ m)`):
  `Nonempty (((Fin 1 → (T A l).ι → A) ⧸ LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B (paySys (Dance.pσ α i) Dance.κσ))) ≃ₗ[A] (((a : Fin k) → (Fin (1 * 2 ^ (k + m − 1 − a)) → A) ⧸ (2 : A) ^ (h + (a : ℕ)) • ⊤) × ((Fin (1 * 2 ^ m) → A) ⧸ LinearMap.range ((2 : A) ^ (h + k) • Matrix.mulVecLin M))))`.

## Proof sketch
- (Q0): induction on `l` with `T_zero`, `T_odd`, `T_even`, `ds_zero`, `ds_odd`, `ds_even` (`Fin 2 × ι` doubles; `tensorV ∘ phi` multiplies by 4), or through `BaiCounts.S1` and a bijection `(T A l).ι ≃ Dance.Idx (ds l)`.
- (Q1): strong induction on `l` (or on `ds l`), for all `r`, `G`, `Gk`, `h` and every `B ≥ l + 1` at once.
  - `l = 0`: `ds 0 = []`, `DanceRel [] r G Gk = MAgree G Gk`, `slots [] r = r`; by C40c (N2) `T A 0 = one A` has (top 0), so (A1) gives `sysAct G = sysAct Gk`; then (A4) with `c = 2^h`; the product over `Fin 0` is trivial.
  - `l = 2l' + 1`: `ds l = false :: ds l'`, `T A l = phi (T A l')`; `DanceRel` gives `G'` with `CleanStep G G'` and `DanceRel (ds l') r G' Gk`. Apply C40c (S1) with `N = T A l'`, `W = l'`, `BN = l' + 1` (C40c (N2)), `B' = l' + 1`, then the induction hypothesis at `h + 1` with `B' = l' + 1`. The new factor `(Fin r → (T A l').ι → A) ⧸ 2^h⊤` has `r * 2^{(k−1)+m}` coordinates by (Q0): it is the factor `a = 0`; the factors `a ≥ 1` are those of `l'` shifted by one.
  - `l = 2l' + 2`: `ds l = true :: ds l'`, `T A l = tensorV (phi (T A l'))`; `DanceRel` gives `G''` on `Fin r × Fin 2` with `CleanStep (vsplit G) G''` and `DanceRel (ds l') (r * 2) G''_e Gk`, `G''_e j j' = G'' (ofLex ((splitIso r).symm j)) (ofLex ((splitIso r).symm j'))`. Apply C40c (S2) (`2 * (l' + 1) + 1 = l + 1 ≤ B`), relabel the next system from `Fin r × Fin 2` to `Fin (r * 2)` with C40c (A3) (`e : Fin (r * 2) ≃ Fin r × Fin 2`, `j ↦ ofLex ((splitIso r).symm j)`), and use the induction hypothesis at `h + 1` with `r * 2`. The new factor `(Fin r × Fin 2 → (T A l').ι → A) ⧸ 2^h⊤` has `r * 2 * 2^{(k−1)+(m−1)} = r * 2^{k+m−1}` coordinates.
  - The bound: `act` does not depend on `B ≥ BN` (C40 `act_bound`), so the induction may fix `B = l + 1` at every level and transfer to any `B ≥ l + 1`.
  - Flatten the product of factors as in C13 `Dance.D2_clocks` (reindex `Fin (k' + 1)` as `Fin 1` plus `Fin k'`; casts of `Fin` sizes by equalities of naturals).
- (Q2): (Q1) at `h = 0`; the factor `a = 0` is `M ⧸ 1 • ⊤ = 0`; reindex `a ↦ a + 1`.
- (Q3): (Q1) for both, and `coker(c • mulVecLin (P M Q)) ≅ coker(c • mulVecLin M)` for invertible `P`, `Q`.
- (Q4): C40b `L4_sigma_clean` gives `Gk` with `DanceRel ds 1 (paySys (pσ α i) κσ) Gk` and `finalM Gk` read along `Fin.cast (slots_eq ds 1).symm` equal to `M`; then (Q1) and the cast `Fin (slots ds 1) ≃ Fin (1 * 2^m)`.

## Checks done before sending
- Brute force `chkC40d.py` (definitions as in `chkC40c.py`: independent lattice model of `T(λ)`, `Φ`, `V ⊗ −` over `ℚ`, formal operators as tables, 2-adic Smith forms over `ℤ`; the data dance by C11 `pT`, `κT` and C12 `pSp`, `κSp`): (Q0) `l ≤ 15`; (Q1) payment systems with random data on `T(l)`, `l ≤ 7`, sizes 1–3 (`r · dim ≤ 48`), `h = 0, 1, 2`, two data each, and the flat count of the clocks against `r·2^{k+m−1−a}`; (Q4) `σ^{(α)}_i` for `l ≤ 7`, `α = 1, 2, 3`, `i = 0, 1, 2, 5`, `h = 0, 1`; (Q3) unit multiples and random pairs with equal final Smith forms. **493 checks, 0 failures.** `logs/chkC40d.log`.
- Controls (all five fire): every clock at `2^h` (no shift `a`); the final matrix scaled by `2^{h+k−1}`; the split move counted with `r` instead of `2r` slots; each clock counted with the lattice of the move instead of the next lattice; (Q0) with `2^{length}` instead of `2^{length+m}`. Two controls of my first version could not fire (the factor `a = 0` vanishes at `h = 0`; a reversed digit order gave the same Smith form by chance); they were replaced before the send.

## Notes
- This piece closes §10.3 (Proposition 10.7). Next: §10.4–§10.6 (rigidity Theorem 10.12, the ring 𝒦 and cleanliness Theorem 10.15), then the odd and even families (Theorems 10.16, 10.22) and the fold law.
