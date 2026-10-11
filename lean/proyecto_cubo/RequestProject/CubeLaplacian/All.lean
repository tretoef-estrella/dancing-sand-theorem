module

public import RequestProject.CubeLaplacian.Basic
public import RequestProject.CubeLaplacian.GroupRing
public import RequestProject.CubeLaplacian.Laplacian
public import RequestProject.CubeLaplacian.Triangular
public import RequestProject.CubeLaplacian.Cokernel
public import RequestProject.CubeLaplacian.TwoAdic
public import RequestProject.CubeLaplacian.Reduction

/-!
# `C17_the_laplacian_in_the_group_ring.md`: the Laplacian of the cube in the group ring

Index of the formalization (namespace `CubeLaplacian`). Nothing of C1–C16 is used.

## Encodings (`Basic.lean`)

* `G n = Fin n → ZMod 2`, `e n i = Pi.single i 1`.
* `R n = AddMonoidAlgebra ℤ (G n)` (as a type, `G n →₀ ℤ`); the identification `R = ℤ^G` is
  `toFun n : R n ≃ₗ[ℤ] (G n → ℤ)`, `f ↦ (g ↦ f g)`.
* `x n i = single (e n i) 1`, `s n i = 1 - x n i`, `sS n S = ∏ i ∈ S, s n i`,
  `sigma n = ∑ i, s n i`, `mulSigma n = (σ · −)` (left multiplication, `ℤ`-linear).
* `lap A n f g = n * f g - ∑ i, f (g + e n i)` (Laplacian with coefficients in a commutative ring
  `A`); `L n = lap ℤ n`; `σ_A = lap ℤ_[2] n`.
* `coker n = (G n → ℤ) ⧸ range (L n)`, `K n = Submodule.torsion ℤ (coker n)` (`K(Q_n)`).
* `Syl2 T = {x : T | ∃ e : ℕ, 2 ^ e • x = 0}` (an `AddSubgroup`).
* `Rplus n = span ℤ {sS n S | S ≠ ∅}` (`R_+`),
  `T n = Rplus n ⧸ (range (mulSigma n)).comap (Rplus n).subtype` (`T(n) = R_+ ⧸ range (σ · −)`).
* Coefficients in the basis `(s_S)` are `(sBasis n).repr f S`.

## Where each statement is

* **Part A** (`GroupRing.lean`): (A1) `A1`; (A2) `A2`; (A3) `A3`; (A4) `A4` (the basis is
  `sBasis n`, with `sBasis_apply`).
* **Part B** (`Laplacian.lean`): (B1) `B1` (pointwise) and `B1'` (`toFun ∘ (σ · −) = L ∘ toFun`);
  (B2) `B2` (the equivalence is `B2equiv`).
* **Part C** (`Triangular.lean`, `Cokernel.lean`): (C1) `C1`, `C1_range`; (C2) `C2_maps`,
  `C2_triangular`, `C2_diagonal`, `C2_injective` (for the restriction `sigmaPlus n : R_+ → R_+`),
  `C2_finiteIndex`; (C3) `C3` (equivalence `C3equiv`, finiteness `T_finite`); (C4) `C4`
  (`C4equiv`, `K_finite`, `cokerEquivK`).
* **Part D** (`TwoAdic.lean`, `Reduction.lean`): (D1) `D1`; (D2) `D2`.

## Remarks

* (C2) "maps `R_+` to `R_+`" is `C2_maps : (Rplus n).map (mulSigma n) ≤ Rplus n`; the triangularity
  statement `C2_triangular` holds for every `S` (not only `S ≠ ∅`), with no extra hypothesis.
* Isomorphisms are stated as `Nonempty (… ≃ₗ[ℤ] …)` (resp. `Nonempty (… ≃+ …)` in Part D), and
  the explicit equivalences are also provided as definitions.
-/
