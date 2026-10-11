# C39 — the fold on the half-size lattice: Ch, Sh, Ψ, Lemma 10.4(a) and Lemma 10.5(a)

Piece C39 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §10.2, the fold side:
parts (a) of Lemmas 10.4 and 10.5). Folder `RequestProject/FoldHalf/`, namespace `FoldHalf`. The
folders C1–C38b are certified: do not change them. Parts (b) of Lemmas 10.4 and 10.5 (the cube
side) are a later piece.

## Setting (reuse, do not redefine)

- C18 `DPLattice` (`M.ι`, `M.wt`, `M.Fd`, `H M = Hop M.wt`), `DPLattice.bvec`, `DPLattice.wtV`, `DPLattice.tensorV`.
- C20 `Doubling.OddUnits`, `Doubling.dfi` (`dfi s = ⅟(2s − 1)!!`, `dfi 0 = 1`), `Doubling.phi` (basis `Fin 2 × N.ι`, weights `2·wt + wtV e`), and its closed formulas (B3).
- C38 `Fold.signOp`, `Fold.expF`, `Fold.aOp`, `Fold.tauOp`, `Fold.Xbar`.
- C21/C29 `Filt.T` (`T (2l+1) = phi (T l)`, `T (2l+2) = tensorV (phi (T l))`); C24 `Lemma35.Fd_eq_zero_of_bound`; C38b `FoldGroup.XbarFam`.

Throughout: `A` is a commutative ring with `[Doubling.OddUnits A]`, `N : DPLattice A`, and `BN : ℕ` with
**(nil)** `∀ s ≥ BN, N.Fd s = 0`.

## Definitions (new), operators on `N` (a vector of `N` is `N.ι → A`)

- `Ch N BN := Σ_{s < BN} dfi s • N.Fd s` (the paper's `Ch = Σ F^{(s)}/(2s − 1)!!`).
- `Sh N BN := Σ_{s < BN} dfi (s + 1) • N.Fd s` (`Sh = Σ F^{(s)}/(2s + 1)!!`).
- `parOp N d` for `d : ℤ`: multiplies the coordinate `i` by `(−1)^{(d − N.wt i).natAbs}` (on `T(l)` with `d = l + j` this is `(−1)^{D + j}`, i.e. `(−1)^j` on the floor-parity classes; it is the paper's sign).
- `ShInv N BN := Ring.inverse (Sh N BN)` in the ring `Module.End A (N.ι → A)`.
- `Psi N d BN := ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + (Ch N BN − parOp N d) * ShInv N BN` (the paper's `Ψ_j = 2(2D + j) + (Ch − (−1)^j)·Sh^{−1}`, with `2(2D + j) = 2d − 2H` on `T(l)`, `d = l + j`).
- `Zop N d BN := −1 − parOp N d * ShInv N BN` (the paper's `(Ψ_i − Ψ_{i+1})/2`).
- `glueOp X Y Z` for operators `X, Y, Z` on `N`: the operator on `(N.ι → A) × (N.ι → A)`, `(m, m') ↦ (X m, Z m + Y m')` (the paper's `glue(X, Y) = [[X, 0], [(Y − X)/2, Y]]` with the lower-left block given explicitly).

## Part S — the operators

**(S1)** `IsUnit (Sh N BN)`; hence `Sh N BN * ShInv N BN = 1 = ShInv N BN * Sh N BN`.
**(S2)** `parOp N d * parOp N d = 1`, and `parOp N d` commutes with every `N.Fd s`, with `Ch N BN`, `Sh N BN` and `ShInv N BN`; `Ch`, `Sh`, `ShInv` commute pairwise.
**(S3)** `(2 : A) • Zop N d BN = Psi N d BN − Psi N (d + 1) BN` (so `glueOp (Psi N (d+1) BN) (Psi N d BN) (Zop N d BN)` is the paper's `glue(Ψ_{i+1}, Ψ_i)`).
**(S4)** `glueOp X Y Z ∘ₗ glueOp X' Y' Z' = glueOp (X ∘ₗ X') (Y ∘ₗ Y') (Z ∘ₗ X' + Y ∘ₗ Z')`.

## Part E — the antipode on Φ(N) (Proposition 3.1(b) and the proof of Lemma 10.4(a))

Let `M := Doubling.phi N`, `d : ℤ`, `c := 2d + 1`, and `B : ℕ` with `2 * BN ≤ B`.

**(E0)** `∀ r ≥ 2 * BN, M.Fd r = 0`.
**(E1)** `Fold.expF M B (bvec 0 n) = bvec 0 (Ch N BN n) + bvec 1 (Sh N BN n)`.
**(E2)** `Fold.aOp M c B (bvec 0 n) = bvec 0 (parOp N d (Ch N BN n)) − bvec 1 (parOp N d (Sh N BN n))`.
**(E3)** `Fold.aOp M c B * Fold.aOp M c B = 1` and `Fold.aOp M c B * Fold.tauOp M c = Fold.tauOp M c * Fold.aOp M c B`.
**(E4)** (freeness) `β : (N.ι → A) × (N.ι → A) → (M.ι → A)`, `β (x, y) := bvec 0 x + Fold.aOp M c B (bvec 0 y)`, is an `A`-linear equivalence.
**(E5)** (the circulant matrix) with `P := ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + Ch N BN * ShInv N BN` and `Q := −(parOp N d * ShInv N BN)`:
  `Fold.tauOp M c (β (x, y)) = β (P x + Q y, Q x + P y)` and `Fold.aOp M c B (β (x, y)) = β (y, x)`; and `P + Q = Psi N d BN`.

## Part A — Lemma 10.4(a) and Lemma 10.5(a)

**(A1)** (Lemma 10.4(a), general form) For `N`, `BN` with (nil), every `d : ℤ` and every `B ≥ 2 * BN`:
  `Fold.Xbar (Doubling.phi N) (2 * d + 1) B ≃ₗ[A] (N.ι → A) ⧸ LinearMap.range (Psi N d BN)`.

**(A2)** (Lemma 10.5(a), general form) For `N`, `BN` with (nil), every `d : ℤ` and every `B ≥ 2 * BN + 1`:
  `Fold.Xbar (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2) B ≃ₗ[A]`
  `((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN))`.

*Sketch of (A2).* On `V ⊗ M` (`M = Φ(N)`), `aOp` at centre `2d + 2` is `g ⊗ aOp_M` at centre `2d + 1` (`g b_0 = b_0 − b_1`, `g b_1 = −b_1`; the sign of `(e, i)` at `c` is the sign of `i` at `c − 1` times `(−1)^{[e = 1]}`), and `tauOp = (1 − g) ⊗ 1 + 1 ⊗ tauOp_M`. Modulo `a − 1`, `V ⊗ M ≅ M` and `tauOp` becomes `f := 1 + tauOp_M − aOp_M`. In the basis `β` of (E4), `f` has the circulant matrix `[[1 + P, Q − 1], [Q − 1, 1 + P]]`; add column 2 to column 1, subtract row 1 from row 2 and exchange the slots: `coker ≅ coker [[P − Q + 2, 0], [Q − 1, P + Q]]`, and `P − Q + 2 = Psi N (d+1) BN`, `P + Q = Psi N d BN`, `Q − 1 = Zop N d BN`.

**(A3)** (nilpotence on the dance lattices) Over `A` with `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`: every weight of `Filt.T A l` lies in `[−l, l]`, and `∀ s ≥ l + 1, (Filt.T A l).Fd s = 0`.

**(A4)** (the families over `ℤ_[2]`) With `N := Filt.T ℤ_[2] l`, `BN := l + 1`:
  `FoldGroup.XbarFam (2 * l + 1) j ≃ₗ[ℤ_[2]] (N.ι → ℤ_[2]) ⧸ range (Psi N (l + j) (l + 1))` for every `j`, and
  `FoldGroup.XbarFam (2 * l + 2) i ≃ₗ[ℤ_[2]] ((N.ι → ℤ_[2]) × (N.ι → ℤ_[2])) ⧸ range (glueOp (Psi N (l + i + 1) (l + 1)) (Psi N (l + i) (l + 1)) (Zop N (l + i) (l + 1)))` for every `i`.
  (Uses `Filt.T (2l+1) = phi (T l)`, `Filt.T (2l+2) = tensorV (phi (T l))`, (A1)–(A3); the bounds `B = λ + 2j + 1` satisfy `2(l+1) ≤ 2l + 2j + 2` and `2(l+1) + 1 ≤ 2l + 2i + 3`.)

## Checks done before sending

- Brute force (`chkC39.py`, independent lattice model of `T(λ)` from `chkC38b.py`, exact rationals, 2-adic Smith forms), `l ≤ 6`: `F^{(s)} = 0` for `s > l` and weights in `[−l, l]`; `Sh·Sh^{−1} = 1`; `Ch`, `Sh`, `Sh^{−1}`, `Ψ` integral over `ℤ_2`; `parOp` commutes with `Ch`, `Sh` and squares to `1`; `2·Z = Ψ(d) − Ψ(d+1)`; `a² = 1` and `aτ = τa` on `T(λ)` for every centre, `λ ≤ 12`; `β` invertible over `ℤ_2` and `τβ = β·[[P, Q], [Q, P]]`, `P + Q = Ψ`; (A1) `X̄(2l+1, j)` has the 2-adic Smith form of `Ψ(l + j)` on `T(l)` (also with the minimal `B = 2l + 2`), `j ≤ 4`; (A2) `X̄(2l+2, i)` has the 2-adic Smith form of the glued matrix, `l ≤ 5`, `i ≤ 4`. 711 checks, 0 failures; `logs/chkC39.log`.
- Controls (all four fire): `Ψ` with the sign of `d + 1`; `Ψ` without `−2H`; the glue without the lower-left block; the odd family at `d = l + j + 1`.

## Instructions

Encodings are your choice provided they are faithful; say in a docstring how each object is encoded. Keep the statements exactly as in this file (more general statements are fine if noted; say if a hypothesis is unused). Every docstring should name the part of `C39_the_fold_on_the_half_lattice.md` it corresponds to. No `sorry`, no new axiom, no `native_decide`.
