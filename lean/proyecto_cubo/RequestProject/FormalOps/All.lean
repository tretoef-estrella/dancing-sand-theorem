module

public import RequestProject.FormalOps.Bf
public import RequestProject.FormalOps.Defs
public import RequestProject.FormalOps.PartB
public import RequestProject.FormalOps.PartT
public import RequestProject.FormalOps.PartV
public import RequestProject.FormalOps.PartS

/-!
# `C40_the_formal_operators.md` — the formal operators: the algebra `𝔅`, its action, the twist
# map, the `V`-split, the Schur step

Folder `RequestProject/FormalOps/`, namespace `FormalOps`. Nothing listed in the Setting is
redefined. Used directly: C18 `DPLattice` (`ι`, `wt`, `Fd`, the axioms `isDP.W_F`, `isDP.P0_F`,
`isDP.P1_F`), `DPLattice.bvec`, `DPLattice.tensorV` with `tensorV_wt`, `tensorV_Fd_b0`,
`tensorV_Fd_b0_zero`, `tensorV_Fd_b1` (and C18's `choose_natAdd`, `ext_single`, `ext_bvec`);
C20 `Doubling.OddUnits`, `Doubling.dfi`, `Doubling.phi`, `Doubling.B3`; C39 `FoldHalf.E0`.
(`H` and `Doubling.B1` are not needed by any proof: the action only involves the `F^{(m)}`, whose
values on `Φ(N)` are all given by `Doubling.B3`.)

## Encodings

* **`Bf A`** (`Bf.lean`) is a new structure with one field `coef : ℕ → ℤ → A`
  (`x.coef m f` = coefficient of `F^{(m)}` at the target floor `f`), so its multiplication is not
  the pointwise one. Extensionality: `Bf.ext`, `Bf.ext_iff` (`x = y ↔ ∀ m f, x.coef m f = y.coef m f`).
  `0, +, −, n •, a •` are coefficientwise, `1` and the product are exactly as in the file;
  the casts `(n : Bf A)`, `(n : ℤ)` have `coef 0 f = n`, `coef m f = 0` for `m ≥ 1`.
  `Bf.fd m` and `Bf.dg p` are exactly as in the file.
* A vector of a DP-lattice `N` is a function `N.ι → A`; an operator is an element of the ring
  `Module.End A (N.ι → A)` (`*` = composition).
* `flD N W p` is the diagonal operator `(flD N W p v) i = p ((W − N.wt i) / 2) * v i` (integer
  division); `act N W B x := Σ_{m ∈ range B} flD N W (x.coef m) * N.Fd m` (`Defs.lean`).
* `tw00`, `tw11`, `tw10`, `tw01`, `vplus`, `vprime` are elements of `Bf A` with the coefficients of
  the file (`Defs.lean`; `tw01` is defined by cases `0` / `q + 1` on the first index).
* `blockOp P C Bb Dd (u, v) = (P u + C v, Bb u + Dd v)` and `schur P C Bb Dd := Dd − Bb ∘ₗ P.symm ∘ₗ C`
  (`PartS.lean`). The submodule `c K₁` is written `(c • ⊤ : Submodule A K₁)` (Mathlib's pointwise
  scalar multiple of `⊤`).
* (top W) is the hypothesis `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)` and (nil BN) is
  `∀ s ≥ BN, N.Fd s = 0`, written out in each statement.
* Each "`≃ₗ[A]`" statement is given as an explicit equivalence (`S1equiv`, `S2equiv`, `S3equiv`) and
  as a `Nonempty` theorem.

## Where each part is

* **Part B**: (B1) `Bf.instRing`, `Bf.instAlgebra`, `Bf.smul_mul`, `Bf.mul_smul`, simp lemmas
  `Bf.coef_add`, `Bf.coef_mul`, `Bf.coef_one`, `Bf.coef_fd`, `Bf.coef_dg` (`Bf.lean`);
  (B2) `flD_one`, `flD_add`, `flD_mul`, `B2`, `flDHom`; (B3) `B3`; (B4) `act_bound`, `act_one`,
  `act_add`, `act_smul`, `act_mul`, `act_fd`, `act_dg`, collected in `B4` (`PartB.lean`).
* **Part T**: (T0) `T0`; (T1) `T1_b0`, `T1_b1`, collected in `T1` (`PartT.lean`).
* **Part V**: (V0) `V0_top`, `V0_nil`, collected in `V0`; (V1) `V1_b0`, `V1_b1`, collected in `V1`
  (`PartV.lean`).
* **Part S**: (S1) `S1equiv`, `S1`; (S2) `S2equiv`, `S2`; (S3) `S3equiv`, `S3` (`PartS.lean`).

## Hypotheses

* `Doubling.phi` only exists over `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, so Part T
  carries these instances (as in the Setting).
* Because the floor is `(W − wt i) / 2` with integer division, the shift
  `(W − (w − 2a)) / 2 = (W − w) / 2 + a` holds for every integer `w`. Hence **(top W) is not used
  in (B3), (B4) or (V1)**; these are stated without it (more general). In (B4), (nil BN) is not
  needed for `act 1 = 1`, additivity, scalars and `act (dg p) = flD p`, which are also given as
  separate lemmas without it (and, for additivity and scalars, for every `B`).
* (top W) is used in (T0), (T1) and the first half of (V0); (nil BN) in (B4) (bound,
  multiplicativity, `fd`), (T1), the second half of (V0) and (V1).
* Part S holds over any commutative ring and any modules, as in the file.
-/
