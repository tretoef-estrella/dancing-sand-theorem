module

public import RequestProject.FoldGroup.Defs
public import RequestProject.FoldGroup.PartK
public import RequestProject.FoldGroup.PartD
public import RequestProject.FoldGroup.PartP

/-!
# `C38b_the_folded_cube_and_proposition_103.md` — the folded cube: its cokernel, Corollary 10.2
# as groups, and Proposition 10.3

Folder `RequestProject/FoldGroup/`, namespace `FoldGroup`. Nothing listed in the Setting is
redefined. Used directly: C17 `CubeLaplacian.G`, `e`, `lap` (through `L`), `coker`, `K`, `Syl2`,
`K_finite`, `cokerEquivK`, `D1` (and C17's general `torsionEquivOfProd`); C38 `Fold.Gbar`, `mk`,
`lapBar`, `cokerBar`, `KBar`, `push`, `push_surjective`, `push_lap`, `G3equiv` (the explicit
equivalence of `G3`), `Xbar`, `C2`; C16 `FamilyGroup.X`; C31 `FamDec.L`, `FamDec.m`, `FamDec.M3`;
C32 `Families.ds`, `Families.T2` (and the reindexing `famReindex` of `Families.T3`, which is the
counting form of C31 (M4)); C29/C21 `Filt.T`; C37 `Mirror.cancel_torsion`.
Used as models only (their proofs are replayed for `Gbar n`): C17 `D2`, `psi`, `range_tensor_eq`,
`cokerTensorEquiv` (here `psiBar`, `range_tensor_eq_bar`, `cokerBarTensorEquiv`), C32 `T3`.
C38 `aElt`, `transl`, `foldSub` enter only through `G3equiv` and `C2`; C38 `G3`, `G3Z` are not
needed by name (`G3equiv` is used instead).

## Encodings

* `XbarFam lam i := Fold.Xbar (Filt.T ℤ_[2] lam) (lam + 2 * i) (lam + 2 * i + 1)` exactly as in
  the file (centre the integer `(lam : ℤ) + 2 * i`, bound the natural number `lam + 2 * i + 1`).
* `twoM M := (nsmulAddMonoidHom 2).range`, the range of `x ↦ 2 • x`, an `AddSubgroup M`.
* "`≃+`", "`≃ₗ[ℤ]`" statements are `Nonempty (…)` theorems; the explicit equivalences are also
  given where they exist without choice (`cokerBarEquivKBar`, `twoMPi`, `twoMProd`, `twoMCongr`,
  `twoMPadic`).
* Lists and multiplicities are as in C31/C32: `λ_j = (FamDec.L n).get j`,
  `j : Fin (FamDec.L n).length`, and `q : Σ λ : Fin (n + 1), Fin (FamDec.m λ n)`.

## Where each part is

* **Part K** (`PartK.lean`): (K1) `K1`; (K2) `K2` (`KBar_finite`, `cokerBarEquivKBar`); (K3) `K3`.
* **Part D** (`PartD.lean`): (D1) `D1`; (D2) `D2`; (D3) `D3`.
* **Part P** (`PartP.lean`): (P1) `twoMPi`, `twoMProd`, `twoMCongr`, `twoMPadic`, collected in
  `P1`; (P2) `P2` (Proposition 10.3).

## Hypotheses and generality

* (K1) holds for every commutative ring `A`; (K2), (K3), (D1)–(D3) for every `n`.
* (P1): the product statement is proved for every index type, not only finite ones.
* (P2): both `HX` (only for `λ ≥ 1`) and `n ≥ 1` are used (`n ≥ 1` gives `λ ≥ 1` on the support,
  by C31 (M3)).
-/
