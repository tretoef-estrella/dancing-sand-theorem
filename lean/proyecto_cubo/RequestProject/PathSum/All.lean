module

public import RequestProject.PathSum.Defs
public import RequestProject.PathSum.Aux
public import RequestProject.PathSum.PartP
public import RequestProject.PathSum.PartR

/-!
# `C43_path_sum.md` — Lemma 10.10 (the path sum) and the relation of the final inverses
# (paper v8 §10.4)

Folder `RequestProject/PathSum/`, namespace `PathSum`. Nothing listed in the Setting is
redefined. Used directly: C40 `FormalOps.Bf` (with `Bf.coef_mul`, `Bf.coef_one`); C40b
`FormalDance.Agree`, `DanceRel`, `finalM`; C29 `Filt.T`, C32 `Families.ds`, C3 `Rulers.oE`,
C14 `Windows.Dset` (through the statement of C42's `C109`); C42 `InvFloors.gamma`,
`InvFloors.C109`; C20 `Doubling.OddUnits`.

## Encodings
* The field is `ℚ_[2]` with its norm `‖·‖` (`‖2‖ = 1/2`), so `‖x‖ ≤ 2^{−s}` means `v_2(x) ≥ s`;
  the bound of the file is written `(2 : ℝ) ^ (−(α − 1 : ℤ))`.
* Setting: the project had no instance `OddUnits ℚ_[2]`; `instOddUnitsPadicTwo` (`Defs.lean`)
  provides it (an odd natural number is non-zero in a field of characteristic zero).
* Definitions (new), exactly as in the file (`Defs.lean`): `piF α c d = 2^α (d + c)`;
  `XiOp α c η ζ` with `coef 0 f = piF α c f`, `coef 1 f = η`, `coef m f = ζ m f` (`m ≥ 2`);
  `SigOp α c η = XiOp α c η (fun _ _ => 0)`;
  `sL α c η L f = (−1)^L L! η^L / ∏_{i ∈ range (L+1)} piF α c (f − i)`.
* "for all `L` and `f ≥ L`" is `∀ L : ℕ, ∀ f : ℤ, (L : ℤ) ≤ f → …`.

## Where each part is
* (P0) `P0` (`PartP.lean`), over any field (more general).
* (P1) `P1` (`PartP.lean`), via (P0) and the recursion `sL_succ` (`Aux.lean`).
* (P2) `P2` (`PartP.lean`), Lemma 10.10, including `sL α c η L f ≠ 0`; proved by strong
  induction on `L` in `P2_gen`, which needs only `α ≥ 1` (the hypothesis `α ≥ 2` of the file is
  used only through `α ≥ 1`). The term `a ≥ 2` of the path sum is handled by `term_identity` and
  `term_norm_le` (`Aux.lean`, with `v_2(a!) ≤ a − 1` from Legendre's formula in Mathlib).
* (R) `R` (`PartR.lean`), from C42's `C109` for `Ξ` and `Σ`, (P1) and (P2). The bound `B` is
  only needed to apply `C109`.
-/
