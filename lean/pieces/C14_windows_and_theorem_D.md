# The windows and Theorem D (Theorem 4.4, §4.4–§4.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §4.4 (Theorem 4.4, the final matrix in closed form, «windows»), §4.5 (Lemma 4.5 and Theorem D). This piece identifies the final matrix produced by the dance (piece C13) with the closed form `Mc` of piece C10, entry by entry, and assembles Theorem D.

This file reuses, without changing them:
- piece C10 (`RequestProject/Deficit/`): `Deficit.starMul`, `Deficit.a`, `Deficit.c`, `Deficit.pi0`, `Deficit.Mc`, `Deficit.B1_rescaling`, `Deficit.C2_integrality_valuation`;
- piece C3 (`RequestProject/Rulers/`): `Rulers.oE`, `Rulers.delta`, `Rulers.v2`;
- piece C11 (`RequestProject/Payment/`): `Payment.pT`, `Payment.κT`;
- piece C12 (`RequestProject/Split/`): `Split.pSp`, `Split.κSp`;
- piece C13 (`RequestProject/Dance/`): `Dance.mCount`, `Dance.Idx`, `Dance.fl`, `Dance.F`, `Dance.SysT`, `Dance.splitIso`, `Dance.relabP`, `Dance.relabK`, `Dance.danceAux`, `Dance.dance`, `Dance.Mfin`, `Dance.pσ`, `Dance.κσ`, `Dance.sigma`, `Dance.proposition_4_3`.

## Setting

**The family of a digit list.** For `ds : List Bool` put `k := length ds`, `m := mCount ds` and
  `I(ds) := {t < k : ds[t] = true}` (a `Finset ℕ`; `ds[t]` is the `t`-th entry, the lowest digit first).
Every `t ∈ I(ds)` satisfies `t < k`. Write `rank(t) := #{u ∈ I(ds) : u < t}`, so `rank` is the increasing enumeration `I(ds) = {t_0 < t_1 < ⋯ < t_{m−1}}`, `rank(t_ℓ) = ℓ`.

**The dancers of a slot.** The dance of C13 with `r = 1` ends on slots `Fin (1 · 2^m)`. A split move at the digit `t_ℓ` sends a slot `s` to the slots `2s` (the slot `A`) and `2s + 1` (the slot `C`); twist moves do not change slots. So a final slot `s < 2^m` has binary digits `s = Σ_{ℓ<m} j_ℓ 2^{m−1−ℓ}`, `j_ℓ ∈ {0, 1}`, where `j_ℓ = 1` iff the slot came from the slot `C` at the digit `t_ℓ`. Define
  `D(ds, s) := {t ∈ I(ds) : Nat.testBit s (m − 1 − rank(t)) = true}`  (for `s < 2^m`).
So `D(ds, ·)` is a bijection from `{0, …, 2^m − 1}` onto the subsets of `I(ds)`, and `D(ds, s') ⊆ D(ds, s)` implies `s' ≤ s`.

**Prefixes.** For `h ≤ k`, `ds.take h` is the digit list of the first `h` moves; `I(ds.take h) = {t ∈ I(ds) : t < h}`.

**Scalars.** Over `ℚ`, `π_0(d) := Deficit.pi0 α i d = 2^α (i + d)`, `c_h := Deficit.c (I(ds)) h`. The halved payments of `σ` are `pσ α i _ f = 2^{α−1}(i + f) = π_0(f)/2` (for `α ≥ 1`).

## Part H — the dance commutes with ring homomorphisms

**(H1)** For a ring homomorphism `φ : A →+* B`, the twisted data, the split data, the relabelled data and the dance commute with `φ`: `pT (φ ∘ p) = φ ∘ pT p`, `κT (φ ∘ p) (φ ∘ κ) = φ ∘ κT p κ`, likewise `pSp`, `κSp`, `relabP`, `relabK`, and
  `dance ds r (φ ∘ p) (φ ∘ κ) = (φ ∘ (dance ds r p κ).1, φ ∘ (dance ds r p κ).2)`
(`φ ∘ p` means `fun s f => φ (p s f)`, and similarly for `κ`).
**(H2)** `Mfin (φ ∘ p) (φ ∘ κ) = (Mfin p κ).map φ`, and `pσ α i` over `B` is `φ ∘ pσ α i` over `A`.
**(H3)** Consequently, for every commutative ring `A`, the final matrix of `dance ds 1 (pσ α i) κσ` over `A` is the image under `Int.castRingHom A` of the same matrix over `ℤ`.

*Proof.* Each definition is a polynomial expression in the data with integer coefficients (`−`, `+`, `*`, sums over finite sets, `2^{α−1}`, the casts of `i` and `f`); induction on `ds` for the dance. ∎

## Part W — the windows (Theorem 4.4)

**(W) The windows after `h` moves.** Let `ds : List Bool`, `α ≥ 1`, `i ∈ ℕ`, and `h ≤ length ds`. Over `A = ℚ`, let `(p^{(h)}, κ^{(h)}) := dance (ds.take h) 1 (pσ α i) κσ` (data on `Fin (1 · 2^{m_h})`, `m_h := mCount (ds.take h)`), and for a slot `s` write `D_s := D(ds.take h, s)`. Then for every floor `f ∈ ℕ` and all slots `s' < s`:
  `p^{(h)}_s(f) = ½ c_h(∅) · ∏_{d ∈ [2^h f + o(D_s), 2^h f + o(D_s) + 2^h)} π_0(d)`,
  `κ^{(h)}_{s s'}(f) = ½ c_h(D_s ∖ D_{s'}) · ∏_{d ∈ [2^h f + o(D_s), 2^h f + o(D_{s'}) + 2^h)} π_0(d)`  if `D_{s'} ⊆ D_s`,
  `κ^{(h)}_{s s'}(f) = 0`  if `D_{s'} ⊄ D_s`,
where `o = Rulers.oE`, the products are over `Finset.Ico`, and `c_h = Deficit.c (I(ds)) h` (for `h ≤ k` it only reads the digits `t < h` of `I(ds)`).

*Proof (the paper's, in halved form).* Induction on `h`. For `h = 0` there is one slot, `D = ∅`, `p(f) = π_0(f)/2`, `c_0(∅) = 1`, and there is no pair `s' < s`. Step `h → h + 1`, digit `ds[h]`:
- *Twist move* (`ds[h] = false`): `pT`, `κT` of C11. Each term is a product over two **adjacent** windows of level `h` whose union is the window of level `h + 1`: `p_s(2f) p_s(2f+1)` multiplies over `[2^{h+1}f + o_D, ⋯ + 2^h)` and `[2^{h+1}f + 2^h + o_D, ⋯ + 2^h)`; in `κT`, `p_{s'}(2f+1) κ_{ss'}(2f)`, `κ_{ss'}(2f+1) p_s(2f)` and `κ_{us'}(2f+1) κ_{su}(2f)` (`s' < u < s`) all multiply over `[2^{h+1}f + o_{D_s}, 2^{h+1}f + o_{D_{s'}} + 2^{h+1})` (the term with `u` is non-zero only if `D_{s'} ⊆ D_u ⊆ D_s`). So `p^{(h+1)}_s = −¼ c_h(∅)^2 · ∏` and `κ^{(h+1)}_{ss'} = −¼ Σ c_h(Δ_1) c_h(Δ_2) · ∏` over the ordered decompositions `D_s ∖ D_{s'} = Δ_1 ⊔ Δ_2` (the intermediate slot `u` has `D_u = D_{s'} ⊔ Δ_1`; `Δ_1 = ∅` and `Δ_2 = ∅` are the first two terms; `D(ds.take h, ·)` is a bijection onto the subsets, so every `Δ_1` occurs exactly once). Since `−¼ (c ⋆ c)(Δ) = ½ · (−½ (c ⋆ c)(Δ))` and `h ∉ I(ds)`, this is `½ c_{h+1}`. If `D_{s'} ⊄ D_s`, every term has a factor `κ` on a non-nested pair, so `κ^{(h+1)}_{ss'} = 0`.
- *Split move* (`ds[h] = true`): `pSp`, `κSp` of C12, relabelled by `(s, j) ↦ 2s + j`; `D(ds.take (h+1), 2s) = D_s`, `D(ds.take (h+1), 2s+1) = D_s ∪ {h}`, `o(D ∪ {h}) = o(D) + 2^h`. The diagonal payments have the windows `[2^{h+1}f + o_D, ⋯ + 2^{h+1})` and `[2^{h+1}f + o_D + 2^h, ⋯ + 2^{h+1})`; the coupling `−p_{s'}(2f+1)` from `(s', A)` to `(s', C)` and the coupling `−κ_{ss'}(2f+1)` from `(s', A)` to `(s, C)` have the windows `[2^{h+1}f + o_{D'} + 2^h, ⋯ + 2^{h+1})` and `[2^{h+1}f + o_D + 2^h, 2^{h+1}f + o_{D'} + 2^{h+1})`, which are the windows of the new pairs, with coefficients `−½ c_h(∅)` and `−½ c_h(D ∖ D')`, i.e. `½` of the coefficients of `x_h` and `x_h x^{D∖D'}` in `−x_h c_h`; the `A`–`A` and `C`–`C` couplings are the twisted couplings, as in the twist move. This is `½ c_{h+1}`. There is no coupling from a slot `C` to a slot `A`, and indeed `h ∈ D(2s+1)` and `h ∉ D(2s'')` make that pair non-nested. ∎

**Theorem 4.4 (the final matrix in closed form).** Let `ds : List Bool`, `k := length ds`, `m := mCount ds`, `I := I(ds)`, `α ≥ 1`, `i ∈ ℕ`. Over `A = ℚ`, let `M := Mfin (dance ds 1 (pσ α i) κσ).1 (dance ds 1 (pσ α i) κσ).2`, read on `Fin (2^m)` through the cast `Fin (2^m) ≃ Fin (1 · 2^m)` as in `Dance.proposition_4_3`. Then for all `s, s' < 2^m`:
  `M s s' = Deficit.Mc I k α i (D(ds, s)) (D(ds, s'))`  if `D(ds, s') ⊆ D(ds, s)`,
  `M s s' = 0`  otherwise.

*Proof.* (W) with `h = k` and `f = 0`: `Mfin` doubles the data, and `Deficit.B1_rescaling` gives `c_k(Δ) = −2^{1−K} 2^{o(Δ)} a_k(Δ)`, which turns `c_k(Δ) · ∏` into `Mc`. On the diagonal, `D(ds, s) = D(ds, s)` and `Mc I k α i D D = c_k(∅) · ∏_{[o_D, o_D + K)} π_0`. For `s < s'`, `Mfin` is `0`, and `D(ds, s') ⊄ D(ds, s)` because `D(ds,s') ⊆ D(ds,s)` forces `s' ≤ s`. ∎

## Part D — Theorem D

**Theorem D (assembly).** Let `ds : List Bool` with `k := length ds ≥ 1`, `m := mCount ds`, `I := I(ds)`, `α ≥ 1`, `i ∈ ℕ`, and let `M : Matrix (Fin (2^m)) (Fin (2^m)) ℤ` be the final matrix over `ℤ` (as in `Dance.proposition_4_3` with `A = ℤ`). Then:
**(D-i)** `Sys(T(ds), Fin 1) ⧸ range(σ^{(α)}_i) ≅ Π_{a<k} ((Fin (2^{k+m−1−a}) → ℤ) ⧸ 2^a·⊤) × (Fin (2^m) → ℤ) ⧸ range(2^k · Matrix.toLin' M)`  (this is `Dance.proposition_4_3` at `A = ℤ`);
**(D-ii)** for all `s, s'`: `(M s s' : ℚ) = Mc I k α i (D(ds,s)) (D(ds,s'))` if `D(ds,s') ⊆ D(ds,s)`, and `M s s' = 0` otherwise;
**(D-iii)** if `D(ds,s') ⊆ D(ds,s)` and `0 < i + o(D(ds,s))`, then `M s s' ≠ 0` and
  `padicValInt 2 (M s s') = 1 − 2^k + o(Δ) + Rulers.delta k Δ + Σ_{d ∈ [o(D(ds,s)), o(D(ds,s')) + 2^k)} (α + Rulers.v2 (i + d))`  (as integers), `Δ := D(ds,s) ∖ D(ds,s')`;
**(D-iv)** for every commutative ring `A`, the final matrix over `A` is `M.map (Int.castRingHom A)`.

*Proof.* (D-i) is Proposition 4.3; (D-ii) is Theorem 4.4 and (H3); (D-iii) is (D-ii) and `Deficit.C2_integrality_valuation` (with `D(ds,s) ⊆ I` and `t < k` for `t ∈ I`), with `padicValRat 2 (z : ℚ) = padicValInt 2 z`; (D-iv) is (H3). ∎

## Checks before formalization

`lean/chkC14.py` (log `logs/chkC14.log`), exact rationals: every digit list with `1 ≤ length ≤ 5` and `length + mCount ≤ 6`, `α ∈ {1, 2, 3}`, `i ∈ {0, 1, 2, 3}`, the dance of C13 iterated literally (`pT`, `κT`, `pSp`, `κSp`, relabelling `(s, j) ↦ 2s + j`). (W) at every `h ≤ length` and floors `f ∈ {0, 1, 2}`: 8 820 payments and 6 300 couplings (nested and non-nested pairs). Theorem 4.4: 3 468 entries. (D-ii) integrality: 3 468. (D-iii) valuation: 1 911 entries, and 93 entries with `i + o(D) = 0` are `0`. Result: 0 failures. Controls, each of which must fail somewhere, and does: the payment without the factor `½` (8 403); the dancers read with the bit order reversed, `testBit s (rank t)` (1 944); the closed form claimed also on non-nested pairs (228); `c_k` in place of `a_k` in `Mc` (1 911); the valuation plus one (1 911).
