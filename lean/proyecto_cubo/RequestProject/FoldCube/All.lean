module

public import RequestProject.FoldCube.Defs
public import RequestProject.FoldCube.Aux
public import RequestProject.FoldCube.PartO1
public import RequestProject.FoldCube.PartO3
public import RequestProject.FoldCube.PartV
public import RequestProject.FoldCube.PartV3
public import RequestProject.FoldCube.PartV5

/-!
# `C39b_the_cube_side_on_the_half_lattice.md` — the cube side on the half-size lattice:
# Lemma 10.4(b) and Lemma 10.5(b)

Folder `RequestProject/FoldCube/`, namespace `FoldCube`. Nothing listed in the Setting is
redefined. Used directly: C18 `DPLattice` (`ι`, `wt`, `Fd`, `H`, axiom (W) `isDP.W_F`, (P1)
`isDP.P1_F`), `bvec`/`slice`, `tensorV` (through C39's `tauOp_t0`, `tauOp_t1`, which come from
`tensorV_Fd_b0`, `tensorV_Fd_b1`); C20 `Doubling.OddUnits`, `Doubling.phi`, `Doubling.B1`
(and `B3` through C39); C38 `Fold.tauOp`, `Fold.aOp`; C38b `FoldGroup.twoM`, `FoldGroup.twoMCongr`;
C39 `FoldHalf.Psi`, `glueOp`, `beta`, `betaInv`, `betaEquiv`, `PE`, `QE`, `E3`, `E5` (E4 through
`betaEquiv`), `A3`, `psi_succ_eq`, `tauOp_phi_b0`, `pi3`; C29 `Filt.T` (`T_zero`, `T_odd`,
`T_even`); C32 `Families.sigL`, `Families.ds`, `Families.sigEquivZ` (the explicit equivalence
behind `B2Z`); C16 `FamilyGroup.X`.

## Encodings

* A vector of a DP-lattice `M` is `M.ι → A`; an operator is an element of the ring
  `Module.End A (M.ι → A)` (`*` = composition, `1` = identity, the numeral `2` is `2 • 1`).
* `Jop`, `Gp`, `SigmaOp`, `thetaOp`, `thX`, `thY` are written exactly as in the file
  (`Defs.lean`). `halfJJ M c` multiplies the coordinate `i` by
  `((((c − M.wt i) * (c − M.wt i + 2)) / 2 : ℤ) : A)` with integer division.
* The vector space of `Φ(N)` is `(phi N).ι → A` (definitionally `Fin 2 × N.ι → A`); `b₀ y₀ + b₁ y₁`
  is `bvec 0 y₀ + bvec 1 y₁`. The same holds for `V ⊗ M` (`tensorV M`).
* `coker T` is `V ⧸ LinearMap.range T`. "`≃ₗ[A]`" and "`≃+`" statements are given as explicit
  definitions (`O1equiv`, `O2equiv`, `O3equiv`, `V1equiv`, `V4equiv`, `V5equiv`) and as
  `Nonempty`/existence theorems.
* In (O3), `e` is written `if Even (d − W) then d else d + 1`. In (O5),
  `c = (j + 1) / 2` is natural-number division and `l + 2 * c` is the integer
  `(l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ)`. In (V6), `d = (l : ℤ) + i`, `BN = l + 1`,
  `B = 2 * l + 2`.

## Where each part is

* **Part O**: (O1) `O1` (`PartO1.lean`); (O2) `O2` and `O2_pi` (`PartO1.lean`); (O3) `O3`, (O4) `O4`,
  (O5) `O5` (first form) and `O5_X` (second form) (`PartO3.lean`).
* **Part V**: (V1) `V1`, (V2) `V2` and `V2_phi`, (V4) `V4` (`PartV.lean`); (V3) `V3a`, `V3b`, `V3c`,
  collected in `V3` (`PartV3.lean`); (V5) `V5`, (V6) `V6` (`PartV5.lean`).

## Hypotheses

* `Doubling.phi` (C20) is only defined over rings with `[IsDomain A] [CharZero A] [OddUnits A]`;
  hence (O1), the second sentence of (V2), (V3), (V5) (and `thX`, `thY`) carry these instances,
  as stated in the file's Setting. (O2), (V1), the first sentence of (V2) and (V4) hold for every
  commutative ring; (O3) only needs `[OddUnits A]`.
* (O2) uses the absence of `2`-torsion; (O3) uses (top) and `OddUnits`; (V3), (V5) use (nil) and
  `B ≥ 2 * BN`. No hypothesis of the file is unused.
-/
