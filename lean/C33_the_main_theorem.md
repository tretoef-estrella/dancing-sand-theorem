# C33 — Proof of the Main Theorem (the Dancing Sand Theorem)

Piece C33 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §1.2 the Main Theorem, §8 its proof). Folder `RequestProject/MainTheorem/`, namespace `MainTheorem`.

The piece assembles two certified halves: Theorem 3.8 (C32 `Families.T3`: `ℤ_2 ⊕ Syl_2 K(Q_n)` is the product of the groups of the families, with multiplicity) and the group of one family (C16 `FamilyGroup.T1`, `T2`, `T2_empty`: Theorem D + Theorem 7.10 + the raw clocks of §1.2). What is left is bookkeeping: the uniform form of the group of a family, the identification of `k`, `I`, `λ` of §1.2 with the digit list `ds λ` of C32, and the shift-zero convention.

## Setting (reused, not redefined)

- C3 (`Rulers`): `lam`, `oE`, `clock` (`u_i(D) = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`, `ξ_D = lam k I + 1 − 2 o_D`).
- C7 (`TheoremF`): `dancer`, `lemma_0a`, `lemma_0b` (o-order), `lemma_0c_existsUnique`.
- C14 (`Windows`): `Ids`, `card_Ids`.
- C13 (`Dance`): `mCount`.
- C16 (`FamilyGroup`): `X`, `SC`, `Q`, `yPool`, `yPool0`, `T1`, `T2`, `T2_empty`.
- C17 (`CubeLaplacian`): `K`, `Syl2`.
- C31 (`FamDec`): `L`, `m`, `M3`, `M4`, `L1`, `L2`.
- C32 (`Families`): `ds`, `ds_zero`, `ds_odd`, `ds_even`, `B0b`, `T2`, `T3`.

`ℤ_[2]` is `PadicInt 2`. «`X ≅ Y`» is `Nonempty (… ≃ₗ[ℤ_[2]] …)` or `Nonempty (… ≃+ …)`; an explicit equivalence is also fine. Write `k λ := (ds λ).length`, `I λ := Ids (ds λ)`, `N λ := 2 ^ mCount (ds λ)`.

## Part S — the shape of a family

**(S1)** For every `λ`: `Rulers.lam (k λ) (I λ) = λ` (so `ξ_D = λ + 1 − 2 o_D`, the `ξ_D` of §1.2). Also `Rulers.oE (I λ) = Σ_{t ∈ I λ} 2^t` and `λ + 1 = 2^{k λ} + Rulers.oE (I λ)`.

**(S2)** `ds λ = [] ↔ λ = 0`; hence `1 ≤ k λ` for `λ ≥ 1`.

**(S3)** `I λ ⊆ Finset.range (k λ)` and `(I λ).card = mCount (ds λ)` (so `N λ = 2^{|I|}`, the number of dancers).

**(S4)** (small clocks, explicitly) For every `ds`:
  `FamilyGroup.SC ds ≃ₗ[ℤ_[2]] ((a : Fin ds.length) → Fin (2 ^ (ds.length + mCount ds − 1 − a)) → FamilyGroup.Q a)`,
and `FamilyGroup.Q 0` is a subsingleton. (So `SC` is `⊕_{a=1}^{k−1} (ℤ/2^a)^{2^{|I|+k−1−a}}` of §1.2; the factor `a = 0` is zero.)

**(S5)** (o-order) For `p < q < N λ`: `oE (dancer (I λ) p) < oE (dancer (I λ) q)`; `dancer (I λ) 0 = ∅`; and every `D ⊆ I λ` is `dancer (I λ) p` for exactly one `p < N λ`.

## Part G — the group of a family, in one form

**(G0)** Define `XFam : ℕ → ℕ → Type` by
- `XFam λ 0 := SC (ds λ) × (ℤ_[2] × ((q : Fin (N λ − 1)) → Q (yPool0 (ds λ) q).toNat))`,
- `XFam λ (i + 1) := SC (ds λ) × ((p : Fin (N λ)) → Q (yPool (ds λ) (i + 1) p).toNat)`.

(At shift `0` the dancer `∅` carries the free summand `ℤ_2 = ℤ/2^∞` and is not pooled; the others are pooled in o-order: the convention of §1.2.)

**(G1)** For `p < N λ` and `i ≥ 1`: `0 ≤ yPool (ds λ) i p`, provided `λ ≥ 1`. For `q < N λ − 1`: `0 ≤ yPool0 (ds λ) q`, provided `λ ≥ 1` and `I λ ≠ ∅`.

**(G2)** For every `λ ≥ 1` and every `i`: `FamilyGroup.X (ds λ) 1 i ≃ₗ[ℤ_[2]] XFam λ i`.

*Sketch.* `i ≥ 1`: C16 `T1` (with (S2) for `1 ≤ k`) gives `E` with `(E p : ℤ) = yPool … p`, so `E p = (yPool … p).toNat` for `p < N`; reindex the product. `i = 0`, `I ≠ ∅`: C16 `T2`, likewise. `i = 0`, `I = ∅`: `N = 1`, the product over `Fin 0` is a singleton, and C16 `T2_empty` gives `SC × ℤ_2`.

## Part M — the Main Theorem

**(M1)** (the Dancing Sand Theorem, multiplicity form) For every `n ≥ 1`:
  `ℤ_[2] × Syl2 (K n) ≃+ ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) → XFam q.1 ((n − q.1) / 2))`.

*Sketch.* C32 `T3`; on each factor, `m λ n ≥ 1` forces `λ ∈ L n` (count), hence `λ ≥ 1` by C31 (M3), and (G2).

**(M2)** (list form) For every `n ≥ 1`:
  `ℤ_[2] × Syl2 (K n) ≃+ ((j : Fin (FamDec.L n).length) → XFam ((FamDec.L n).get j) ((n − (FamDec.L n).get j) / 2))`.

**(M3)** (the families that occur, and the free summand) For `n ≥ 1` and every `λ`:
- `FamDec.m λ n ≠ 0 → 1 ≤ λ ∧ λ ≤ n ∧ λ % 2 = n % 2`;
- for such `λ`, `(n − λ) / 2 = 0 ↔ λ = n`;
- `FamDec.m n n = 1` and `FamDec.m 0 n = 0`.

(So exactly one factor of (M1) has shift `0`, the family `λ = n`, and it carries the one free summand `ℤ_2`.)

## Notes

- Nothing is cited. Every step is a certified piece (C16, C31, C32) plus reindexing.
- `toNat` is harmless on the support by (G1).
- Brute force (`chkC33.py`), independent of every earlier script: the raw clocks `u_i(D)` of §1.2 computed from the binary expansion of `λ + 1` (dancers in o-order, `h_t = next(t) − t`, `φ`, `κ` by carries), the integer antitonic fit by pool-adjacent-violators with the rounding of §1.2, the small clocks; the right-hand side of (M1) as a multiset of exponents compared with the 2-adic Smith form of the Laplacian of `Q_n` (one infinite exponent), `1 ≤ n ≤ 9`; the worked example `n = 6` of §1.2; (S1), (S3), (S5) for `λ ≤ 300`; (M3) for `n ≤ 40`. Controls: unpooled clocks; `κ(i + o_D, ξ_D)`; the dancer `∅` pooled at shift `0`; the small clocks with the factor `a = 0` counted as `ℤ/2`.
