module

public import RequestProject.FoldOdd.Defs
public import RequestProject.FoldOdd.PartF
public import RequestProject.FoldOdd.PartF4
public import RequestProject.FoldOdd.PartC

/-!
# `C49_the_fold_law_on_the_odd_families.md`: the fold law on the odd families
# (Corollary 10.17 for `j ≥ 1`, and for `l = 0`)

Folder `RequestProject/FoldOdd/`, namespace `FoldOdd`. Nothing listed in the Setting is
redefined; C40 `FormalOps` (`Bf`, `Bf.dg`, `Bf.fd`, `flD`, `act`, `act_one`, `act_add`,
`act_smul`, `act_mul`, `act_fd`, `act_dg`), C40c `FormalAct.sysAct`, C20 `Doubling.dfi`,
`Doubling.OddUnits`, C39 `FoldHalf` (`Ch`, `Sh`, `parOp`, `ShInv`, `Psi`, (A3), (A4_odd)),
C39b `FoldCube` (`SigmaOp`, (O4), (O5_X)), C46 `Smith2.XiOpZ`, C48b `DanceXi` (R0), (R2),
C38b `FoldGroup.XbarFam`, `FoldGroup.twoM`, C29 `Filt.T`, C32 `Families.ds`, C16
`FamilyGroup.X`, C18 `DPLattice`, `H` are used unchanged.

## Definitions (new) — `Defs.lean`
`cst`, `chC`, `shC`, `shInvC` (with its two defining equations `shInvC_zero`, `shInvC_eq`),
`ChF`, `ShF`, `ShInvF`, `KF`, `kJ`, `PsiF`, `SigF`, written as in the file.

## Where each item is
* **(F1)** `FoldOdd.F1` (`PartF.lean`).
* **(F2)** `FoldOdd.F2` (`PartF.lean`).
* **(F3)** `FoldOdd.F3` (`PartF.lean`).
* **(F4)** `FoldOdd.F4` (`PartF4.lean`).
* **(F5)** `FoldOdd.F5` (`PartF.lean`).
* **(F6)** `FoldOdd.F6` (`PartF.lean`).
* **(C1)** `FoldOdd.C1` (`PartC.lean`).
* **(C2)** `FoldOdd.C2` (`PartC.lean`).
* **(C3)** `FoldOdd.C3` (`PartC.lean`).

The equalities of (F1)–(F5) are equalities (in `Bf A` resp. in `Module.End A (N.ι → A)`).
Conjunctions of the file are `∧`; "`kJ j 1 = 1` if `Even j`" is `Even j → kJ j 1 = 1`.
No statement needed a hypothesis that the file does not give, and none was added.
In (C1) the two quotients are parenthesised, `Nonempty ((… ⧸ range Psi …) ≃ₗ[ℤ_[2]] (… ⧸ range SigmaOp …))`:
without the parentheses Lean's precedence would read the expression differently from the file's
meaning. Helper lemmas (`act_cst`, `coef_KF`, `kJ_one`, `flD_T`, `parOp_T`, `coker_act_XiOpZ`, …)
are proof auxiliaries, not new definitions.
-/
