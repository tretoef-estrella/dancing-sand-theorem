# The group of a family over ℤ_2 (§8, per family: Theorem D + Theorem 7.10)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §1.2 (raw clocks, pooling, the group `X(λ, i)`), §4.3 (Proposition 4.3), §5 (Propositions 5.3 and 5.4), §7.5 (Theorem 7.10) and §8 (the three bullets of the proof of the Main Theorem). This piece takes the cokernel of the tower map `σ^{(α)}_i` over the 2-adic integers, splits it with Proposition 4.3 (piece C13), diagonalizes the final matrix with its Smith form at 2 (piece C15), and identifies the exponents with the pooled raw clocks of §1.2. It is the per-family half of §8; the decomposition of `ℤ_2 ⊕ Syl_2 K(Q_n)` into families (Theorem 3.8) is a later piece.

This file reuses, without changing them:
- piece C15 (`RequestProject/DanceSmith/`): `DanceSmith.S3`, `DanceSmith.Z1`, `DanceSmith.Z3`, `DanceSmith.Cst`, `DanceSmith.yHat`, `DanceSmith.yHatS`, `DanceSmith.xClk`;
- piece C14 (`RequestProject/Windows/`): `Windows.Ids`, `Windows.finalMatrix`, `Windows.theorem_D_iv`, `Windows.card_Ids`;
- piece C13 (`RequestProject/Dance/`): `Dance.SysT`, `Dance.sigma`, `Dance.mCount`, `Dance.proposition_4_3`;
- piece C3 (`RequestProject/Rulers/`): `Rulers.clock`, `Rulers.xD`, `Rulers.xSharp`, `Rulers.kappa`, `Rulers.proposition_5_3`, `Rulers.proposition_5_4_c`;
- pieces C1, C4, C6, C7, C9: `AntitonicFit.ifit`, `GoldenMatching.xVal`, `Houses.xH`, `TheoremF.dancer`, `TheoremF.xHseq`, `CellFloor.xSharp`, `CellFloor.yhatSharp`.

## Setting

Let `A := ℤ_[2]` (Mathlib's `PadicInt 2`). Let `ds : List Bool` with `k := length ds`, `I := Windows.Ids ds`, `m := mCount ds = |I|`, `N := 2^m`, `K := 2^k`, and let `α ≥ 1`, `i` be natural numbers. The family is `λ := K + o_I − 1` (so `λ + 1 = 2^k + Σ_{t∈I} 2^t`), and `I ⊆ {0, …, k − 1}`.

**The group of the tower.**
  `X^{(α)}(ds, i) := SysT A ds (Fin 1) ⧸ range (sigma A ds α i)`.

**Small clocks** (as in `Dance.proposition_4_3`):
  `SC(ds) := Π_{a : Fin k} (Fin (2^{k + m − 1 − a}) → A) ⧸ (2^a • ⊤)`.

**Big clocks.** For `e ∈ ℕ` write `Q(e) := A ⧸ Ideal.span {2^e}`.

**The clocks of C15.** For `i ≥ 1`: `C := α K + κ(i − 1, K)` and `ŷ := AntitonicFit.ifit N x` with `x j := GoldenMatching.xVal k I α (i − 1) (TheoremF.dancer I j)` (`DanceSmith.Cst`, `DanceSmith.yHat`). For `i = 0`: `ŷ^♯ := CellFloor.yhatSharp I k (K − 1) α` (`DanceSmith.yHatS`).

**The raw clocks of §1.2** (`α = 1`). `u_i(D) := Rulers.clock k I i D = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`, `ξ_D = λ + 1 − 2 o_D`. The **pooled clocks** are
  `ŷ_i(p) := AntitonicFit.ifit N (j ↦ u_i(dancer I j)) p`  for `i ≥ 1`, `p < N`;
  `ŷ_0(q) := AntitonicFit.ifit (N − 1) (j ↦ u_0(dancer I (j + 1))) q`  for `q < N − 1`
(at shift 0 the dancer `∅` carries `∞` and is not pooled: the convention of §1.2).

## Part L — cokernels of diagonalizable matrices (any commutative ring)

Let `R` be a commutative ring and `B : Matrix (Fin n) (Fin n) R`.

**(L1)** If `P, Q : Matrix (Fin n) (Fin n) R` have unit determinant and `P * B * Q = Matrix.diagonal d`, then
  `(Fin n → R) ⧸ range (Matrix.toLin' B) ≃ₗ[R] Π_{j : Fin n} R ⧸ Ideal.span {d j}`.

**(L2)** For `c : R`, `range (c • Matrix.toLin' B) = range (Matrix.toLin' (c • B))`; so under the hypothesis of (L1), `(Fin n → R) ⧸ range (c • Matrix.toLin' B) ≃ₗ[R] Π_j R ⧸ Ideal.span {c · d j}`.

**(L3)** If `u : R` is a unit, `Ideal.span {u · y} = Ideal.span {y}`. And `R ⧸ Ideal.span {0} ≃ₗ[R] R`.

*Proof.* (L1): `toLin' B = toLin' P⁻¹ ∘ toLin' (diag d) ∘ toLin' Q⁻¹` with `toLin' P⁻¹`, `toLin' Q⁻¹` linear equivalences; the range of `toLin' B` is the image under `toLin' P⁻¹` of `range (diag d)`, so the quotient is isomorphic to `(Fin n → R) ⧸ range (diag d)`, and `range (diag d) = Π_j Ideal.span {d j}` (as a submodule of the product), whose quotient is the product of the quotients. (L2): `(c • toLin' B) v = toLin' (c • B) v`, and `P (c • B) Q = c • diag d = diag (c · d)`. (L3): standard. ∎

## Part U — odd integers in ℤ_2

**(U1)** For an odd integer `z`, `(z : ℤ_[2])` is a unit.

**(U2)** If `P : Matrix (Fin n) (Fin n) ℤ` has odd determinant, then `(P.map (Int.castRingHom ℤ_[2])).det` is a unit; and `(P * B * Q).map φ = P.map φ * B.map φ * Q.map φ` for the ring homomorphism `φ = Int.castRingHom ℤ_[2]`.

*Proof.* (U1): `‖z‖ = 1` in `ℤ_[2]` when `2 ∤ z` (`PadicInt.isUnit_iff`, `padicNorm`). (U2): `det (P.map φ) = φ (det P)` (`RingHom.map_det`) and (U1); `Matrix.map_mul`. ∎

## Part X — the group of a family

**(X1) `i ≥ 1`.** For `k ≥ 1`, `α ≥ 1`, `i ≥ 1` there is `E : ℕ → ℕ` with `(E p : ℤ) = k + C + ŷ p` for every `p < N`, and
  `X^{(α)}(ds, i) ≃ₗ[A] SC(ds) × Π_{p : Fin N} Q(E p)`.

**(X2) `i = 0`, `I ≠ ∅`.** For `k ≥ 1`, `α ≥ 1`, `I ≠ ∅` there is `E : ℕ → ℕ` with `(E q : ℤ) = k + α K + ŷ^♯ q` for every `q < N − 1`, and
  `X^{(α)}(ds, 0) ≃ₗ[A] SC(ds) × (A × Π_{q : Fin (N − 1)} Q(E q))`.

**(X3) `i = 0`, `I = ∅`.** For `α ≥ 1` with `I = ∅` (so `N = 1`):
  `X^{(α)}(ds, 0) ≃ₗ[A] SC(ds) × A`.

*Proof.* `Dance.proposition_4_3` over `A` gives `X^{(α)}(ds, i) ≃ SC(ds) × (Fin N → A) ⧸ range (2^k • toLin' M_A)`, where `M_A` is the final matrix over `A` read on `Fin N`; by `Windows.theorem_D_iv` it is `M.map φ`, `M = Windows.finalMatrix ℤ ds α i`. (X1): `DanceSmith.S3` gives `P M Q = diag(u_j 2^{C + ŷ(N − 1 − j)})` over `ℤ` with `det P`, `det Q` odd and `u_j` odd; map it to `A` (Part U), apply (L2) with `c = 2^k` and (L3) to drop the units `u_j`, and reindex `j ↦ N − 1 − j` (`Fin.revPerm`) to read the exponents by o-position `p`. (X2): the same with `DanceSmith.Z3`, whose diagonal is `u_j 2^{αK + ŷ^♯(N − 2 − j)}` for `j < N − 1` and `0` for `j = N − 1`; the factor of the `0` entry is `A ⧸ span {0} ≅ A` (L3), and `j ↦ N − 2 − j` reindexes the others. (X3): `DanceSmith.Z1` gives `M = 0`, so `(Fin 1 → A) ⧸ range 0 ≅ A`. ∎

## Part R — the raw clocks (α = 1)

**(R0) Pooling commutes with constants.** For every `N`, `x : ℕ → ℤ` and `c : ℤ`, and every `j < N`:
  `AntitonicFit.ifit N (fun j => x j + c) j = AntitonicFit.ifit N x j + c`.

**(R1) `i ≥ 1`.** For `α = 1`, `i ≥ 1` and `p < N`: `k + C + ŷ p = ŷ_i(p)`, i.e.
  `k + K + κ(i − 1, K) + AntitonicFit.ifit N x p = AntitonicFit.ifit N (j ↦ Rulers.clock k I i (dancer I j)) p`.

**(R2) `i = 0`, `I ≠ ∅`.** For `α = 1` and `q < N − 1`: `k + K + ŷ^♯ q = ŷ_0(q)`, i.e.
  `k + K + CellFloor.yhatSharp I k (K − 1) 1 q = AntitonicFit.ifit (N − 1) (j ↦ Rulers.clock k I 0 (dancer I (j + 1))) q`.

*Proof.* (R0): the antitonic least-squares fit commutes with adding a constant (if `z` is a non-increasing minimizer for `x`, then `z + c` is one for `x + c`, by Lemma 7.1 or directly from the definition), and the integer rounding of a block of `p` positions with sum `S` turns into that of the block with sum `S + pc`, which is the old one plus `c`. (R1): `Rulers.proposition_5_3` gives `u_i(D) = k + K + κ(i − 1, K) + Rulers.xD k I (i − 1) D` for `D ⊆ I` (and `dancer I j ⊆ I`, `TheoremF.lemma_0a`); `Rulers.xD k I (i − 1) D = GoldenMatching.xVal k I 1 (i − 1) D` (the same definition with `α = 1`); then (R0). (R2): `Rulers.proposition_5_4_c` gives `u_0(D) = k + K + Rulers.xSharp k I D` for `∅ ≠ D ⊆ I`; `dancer I (j + 1) ≠ ∅` for `j + 1 < N`; `CellFloor.xSharp I k (K − 1) 1 j = Houses.xH I k (K − 1) 1 (dancer I (j + 1))`, and `Houses.xH I k (K − 1) 1 D = Rulers.xSharp k I D` (both are `R^♯(D) − R^♯(I ∖ D)` with `R^♯ = Rulers.ruler k I 1 (K − 1)`); then (R0) on `N − 1` positions. ∎

## Part T — Theorem X: the group of a family is `X(λ, i)` of §1.2

**(T1) `i ≥ 1`.** For `k ≥ 1` and `i ≥ 1` there is `E : ℕ → ℕ` with `(E p : ℤ) = ŷ_i(p)` for every `p < N`, and
  `X^{(1)}(ds, i) ≃ₗ[A] SC(ds) × Π_{p : Fin N} Q(E p)`.

**(T2) `i = 0`.** For `k ≥ 1` and `I ≠ ∅` there is `E : ℕ → ℕ` with `(E q : ℤ) = ŷ_0(q)` for every `q < N − 1`, and
  `X^{(1)}(ds, 0) ≃ₗ[A] SC(ds) × (A × Π_{q : Fin (N − 1)} Q(E q))`.
For `I = ∅`, (X3) with `α = 1`.

*Proof.* (X1), (X2) with `α = 1`, and (R1), (R2). ∎

**Checks.** `chkC16.py` (exact rationals, the dance of C13): on every digit list with `length + #true ≤ 6`, `α ∈ {1, 2, 3}`, `i ≤ 3`, the multiset of exponents `k + (Smith exponents of M at 2)` (`∞` for a zero) equals `{k + C + ŷ p}` (X1), `{∞} ∪ {k + αK + ŷ^♯ q}` (X2), `{∞}` (X3); for `α = 1` the pooled raw clocks `ŷ_i` equal `k + C + ŷ` and `k + K + ŷ^♯` position by position (R1, R2); (R0) on random sequences; (L1)–(L2) on random integer matrices `P⁻¹ diag(d) Q⁻¹` with `det P`, `det Q` odd; the worked example `n = 6` of §1.2 (`λ = 6, 4, 2`: big clocks `∞, 6, 6, 3`; `6, 6`; `5, 2`). Controls: unpooled raw clocks, `κ(i + o_D, ξ)` instead of `κ(i + o_D − 1, ξ)`, the `i = 0` big clocks computed with the shift-1 clocks, and a matrix of even determinant in (L1).
