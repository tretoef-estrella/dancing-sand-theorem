module

public import RequestProject.FoldHalf.Defs
public import RequestProject.FoldHalf.Ops
public import RequestProject.FoldHalf.Quot
public import RequestProject.FoldHalf.PartS
public import RequestProject.FoldHalf.PartE
public import RequestProject.FoldHalf.PartA

/-!
# `C39_the_fold_on_the_half_lattice.md` — the fold on the half-size lattice: `Ch`, `Sh`, `Ψ`,
# Lemma 10.4(a) and Lemma 10.5(a)

Folder `RequestProject/FoldHalf/`, namespace `FoldHalf`. Nothing listed in the Setting is
redefined. Used directly: C18 `DPLattice` (`ι`, `wt`, `Fd`, `H`), `bvec` (and `slice`,
`eq_bvec_slice`), `wtV`, `tensorV` (with its formulas `tensorV_Fd_b0`, `tensorV_Fd_b1`);
C20 `Doubling.OddUnits`, `Doubling.dfi`, `Doubling.phi` and its closed formulas `Doubling.B3`
(and `Doubling.B1` for `F(b₀ n) = b₁ n`); C38 `Fold.signOp`, `Fold.expF`, `Fold.aOp`,
`Fold.tauOp`, `Fold.Xbar` (and C38's `expF_tensorV_bvec0/1`, `signOp_tensorV_bvec0/1`);
C21/C29 `Filt.T` (`T_zero`, `T_odd`, `T_even`); C24 `Lemma35.Fd_eq_zero_of_bound`;
C38b `FoldGroup.XbarFam`.

## Encodings (`Defs.lean`)

* A vector of `N` is `N.ι → A`; operators on `N` are elements of the ring
  `Module.End A (N.ι → A)` (`*` is composition).
* `Ch N BN = Σ_{s ∈ range BN} dfi s • N.Fd s`, `Sh N BN = Σ_{s ∈ range BN} dfi (s+1) • N.Fd s`.
* `parOp N d` multiplies the coordinate `i` by `(−1)^{(d − N.wt i).natAbs}`.
* `ShInv N BN = Ring.inverse (Sh N BN)` in `Module.End A (N.ι → A)`.
* `Psi N d BN = ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + (Ch N BN − parOp N d) * ShInv N BN`,
  `Zop N d BN = −1 − parOp N d * ShInv N BN`, exactly as in the file.
* `glueOp X Y Z (m, m') = (X m, Z m + Y m')`, defined for operators on any module `L` (the file
  uses `L = N.ι → A`).
* The vector space of `Φ(N)` is `(phi N).ι → A`, definitionally `Fin 2 × N.ι → A`; the vector
  with `n` in slot `e` is `bvec e n`. In (E4), `id (bvec 0 x) : (phi N).ι → A` only fixes the
  ambient type of the sum `bvec 0 x + aOp M c B (bvec 0 y)`.
* (E5): `P = PE N BN d`, `Q = QE N BN d`, written as in the file; `β = beta N d B`.
* "`≃ₗ[A]`" statements are given as explicit definitions (`betaEquiv`, `A1equiv`, `A2equiv`) and
  as `Nonempty (… ≃ₗ[A] …)` / existence theorems (`E4`, `A1`, `A2`, `A4_odd`, `A4_even`, `A4`).

## Where each part is

* **Part S** (`PartS.lean`): `S1`, `S2`, `S3`, `S4`.
* **Part E** (`PartE.lean`): `E0`, `E1`, `E2`, `E3` (from the general facts `aOp_mul_self` and
  `aOp_comm_tauOp` of `Ops.lean`: on any DP-lattice with `F^{(r)} = 0` for `r ≥ B`,
  `aOp² = 1` because `signOp · expF · signOp = Σ (−1)^r F^{(r)}` is inverse to `expF`, and
  `aOp` commutes with `tauOp` because `expF F + F expF = expF H − H expF`), `E4` (with the explicit
  inverse `betaInv`), `E5`.
* **Part A** (`PartA.lean`): `A1equiv`/`A1` (the class of `β (x, y)` goes to the class of
  `x + y`), `A2equiv`/`A2` (following the sketch: `ψ (b₀ u₀ + b₁ u₁) = u₀ + (1 − a) u₁` identifies
  `V ⊗ M` modulo `aOp − 1` with `M`, `tauOp` becomes `f = 1 + tauOp_M − aOp_M`; then `β⁻¹` and the
  slot change `(u, v) ↦ (v − u, u)` turn `f` into the glued operator), `A3`, `A4_odd`, `A4_even`,
  `A4`. Both quotient identifications use the general lemma `quotEquivOfIntertwine`
  (`Quot.lean`).

## Hypotheses

* `Doubling.phi` (C20) is only defined over rings with `[IsDomain A] [CharZero A] [OddUnits A]`;
  hence Parts E and (A1), (A2) carry these instances (the file's Setting only lists `OddUnits`,
  but the objects of Parts E and A cannot be formed without the other two).
* (nil) is used in (S1) and in all of Parts E and A. It is not needed for (S2), (S3), (S4), which
  are stated without it (more general).
* (A4) uses (A3) for (nil) of `Filt.T ℤ_[2] l` with `BN = l + 1`.
-/
