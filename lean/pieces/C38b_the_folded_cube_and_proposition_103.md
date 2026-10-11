# C38b — the folded cube: its cokernel, Corollary 10.2 as groups, and Proposition 10.3

Piece C38b of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §10.1). Folder
`RequestProject/FoldGroup/`, namespace `FoldGroup`. The folders C1–C38 are certified: do not change
them.

## Setting (reuse, do not redefine)

- C17 `CubeLaplacian`: `G n`, `e n i`, `lap A n`, `coker n`, `K n`, `Syl2`, `K_finite`, `cokerEquivK` (`coker n ≃ₗ[ℤ] ℤ × K n`), (D1) `D1` (`T ⊗[ℤ] ℤ_[2] ≃+ Syl2 T` for finite `T`), (D2) `D2`, and the reduction lemmas of `Reduction.lean` (`psi`, `range_tensor_eq`, `cokerTensorEquiv`), as models.
- C38 `Fold`: `aElt`, `transl`, `foldSub`, `Gbar`, `mk`, `lapBar`, `cokerBar`, `KBar`, `push`, `push_surjective`, `push_lap`, `G3`, `G3equiv`, `G3Z`, `Xbar`, `C2`.
- C16 `FamilyGroup.X ds α i`; C31 `FamDec.L`, `FamDec.m`, (M3), (M4); C32 `Families.ds`, (T2) `Families.T2`, (T3); C21 `Filt.T`; C37 `Mirror.cancel_torsion`.

## Definitions (new)

- `XbarFam λ i := Fold.Xbar (Filt.T ℤ_[2] λ) (λ + 2 * i) (λ + 2 * i + 1)` (the paper's `X̄(λ, i)`, a `ℤ_[2]`-module).
- For an additive commutative group `M`: `twoM M : AddSubgroup M`, the subgroup `2·M = {2 • x : x ∈ M}` (the range of `x ↦ 2 • x`).

## Part K — the folded cube over ℤ and over ℤ_2 (every `n`)

**(K1)** For every commutative ring `A`, every `n` and every `u : Gbar n → A`: `Σ_x (lapBar A n u) x = 0`.

**(K2)** For every `n`: `Finite (KBar n)` and `cokerBar n ≃ₗ[ℤ] ℤ × KBar n`.

*Sketch.* The sum map `s : (Gbar n → ℤ) → ℤ` vanishes on `range lapBar` (K1) and `s(δ_x) = 1`, so `cokerBar n ≃ ℤ × (ker s ⧸ range lapBar)`. The quotient `ker s ⧸ range lapBar` is finite: `push` maps the sum-zero functions on `G n` onto the sum-zero functions on `Gbar n` (it preserves the sum; lift a function on `Gbar n` to one supported on representatives), and `push (range lap) = range lapBar` (C38 `push_lap`, `push_surjective`); so it is a quotient of `ker(sum on G n) ⧸ range lap`, which is `K n` by C17 (`cokerEquivK`, `K_finite`). A finite quotient is torsion, and the free part has rank one, so `ker s ⧸ range lapBar = KBar n`. (For `n = 0, 1`, `Gbar n` has one point, `lapBar = 0`, `KBar n = 0`.)

**(K3)** For every `n`: `(Gbar n → ℤ_[2]) ⧸ LinearMap.range (lapBar ℤ_[2] n) ≃+ ℤ_[2] × Syl2 (KBar n)`.

*Sketch.* As C17 (D2): right exactness of `⊗[ℤ] ℤ_[2]` (`(Gbar n → ℤ) ⊗ ℤ_[2] ≃ (Gbar n → ℤ_[2])`, `Gbar n` finite, and the range of `lapBar ℤ n ⊗ 1` is the range of `lapBar ℤ_[2] n`), then (K2) and C17 (D1).

## Part D — Corollary 10.2 as groups

**(D1)** (list form) For every `n`:
`ℤ_[2] × Syl2 (KBar n) ≃+ Π_{j : Fin (FamDec.L n).length} Fold.Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1)`.

*Sketch.* (K3), then C38 `G3` over `ℤ_[2]`, then C38 `C2`.

**(D2)** (shift form) For every `n`:
`ℤ_[2] × Syl2 (KBar n) ≃+ Π_{j : Fin (FamDec.L n).length} XbarFam ((FamDec.L n).get j) ((n − (FamDec.L n).get j) / 2)`.

*Sketch.* On the support `λ + 2 · ((n − λ) / 2) = n` (C31 (M3); `L 0 = [0]`).

**(D3)** (multiplicity form, the paper's `ℤ_2 ⊕ Syl_2 K̄(n) ≅ ⊕_λ X̄(λ, (n − λ)/2)^{m_λ(n)}`) For every `n`:
`ℤ_[2] × Syl2 (KBar n) ≃+ Π_{q : Σ λ : Fin (n + 1), Fin (FamDec.m λ n)} XbarFam q.1 ((n − q.1) / 2)`.

*Sketch.* (D2) and C31 (M4), as C32 (T3).

## Part P — Proposition 10.3

**(P1)** For finite families: `twoM (Π_j M_j) ≃+ Π_j twoM (M_j)`; `twoM (M × N) ≃+ twoM M × twoM N`; an `≃+` `M ≃+ N` induces `twoM M ≃+ twoM N`; and `twoM ℤ_[2] ≃+ ℤ_[2]`.

**(P2)** (Proposition 10.3) Assume `HX : ∀ λ ≥ 1, ∀ i, Nonempty (XbarFam λ i ≃+ twoM (FamilyGroup.X (Families.ds λ) 1 i))`. Then for every `n ≥ 1`:
`Nonempty (Syl2 (KBar n) ≃+ twoM (Syl2 (K n)))` (Theorem DW).

*Sketch.* By (D2), `HX` on each factor (`λ ≥ 1` by C31 (M3) since `n ≥ 1`) and (P1),
`ℤ_[2] × Syl2 (KBar n) ≃+ twoM (Π_j FamilyGroup.X (ds λ_j) 1 i_j) ≃+ twoM (ℤ_[2] × Syl2 (K n)) ≃+ ℤ_[2] × twoM (Syl2 (K n))` (C32 (T2)). Then C37 `Mirror.cancel_torsion`: `ℤ_[2]` has no `2`-power torsion, and `Syl2 (KBar n)`, `twoM (Syl2 (K n))` are `2`-power torsion.

The hypothesis `HX` is the fold law family by family; it is proved in §10.2–§10.7 (later pieces). It is false for `λ = 0` (`XbarFam 0 1 ≅ ℤ/2`, `twoM (X(0, 1)) = 0`), which is why `λ ≥ 1`.

## Checks done before sending

- Brute force (`chkC38b.py`, independent lattice model of `T(λ)`, divided powers `F^r / r!` over `ℚ`, 2-adic Smith forms): (K1) column sums and random `u`, `n ≤ 8`; (K2) rank of `lapBar` over `F_p` is `|Gbar| − 1` and exactly one `ℤ_2` summand, `n ≤ 8`; (D1), (D2), (D3) the 2-adic Smith form of `lapBar` equals the concatenation over the families, `1 ≤ n ≤ 8`; divided powers on `T(λ)` integral over `ℤ_2` (odd denominators such as `F^3/6` are units) and zero above `λ`, `λ ≤ 12`, and `XbarFam` independent of `B ≥ λ + 1`; `HX` for `1 ≤ λ ≤ 12`, `i ≤ 5`; Theorem DW `n ≤ 8`. 254 checks, 0 failures; results in `logs/chkC38b.log`.
- Controls (all four fire): `HX` at `λ = 0`, `i = 1`; `a` without the sign; centre `c = λ` instead of `n` in the list form; Theorem DW without the factor `2`.

## Instructions

Encodings are your choice provided they are faithful; say in a docstring how each object is encoded. Keep the statements exactly as in this file (more general statements are fine if noted; say if a hypothesis is unused). Every docstring should name the part of `C38b_the_folded_cube_and_proposition_103.md` it corresponds to. No `sorry`, no new axiom, no `native_decide`.
