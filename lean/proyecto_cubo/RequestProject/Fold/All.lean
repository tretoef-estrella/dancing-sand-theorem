module

public import RequestProject.Fold.Defs
public import RequestProject.Fold.PartG
public import RequestProject.Fold.PartL
public import RequestProject.Fold.Transport
public import RequestProject.Fold.Corollary

/-!
# `C38_the_fold_in_the_group_ring.md` — the fold in the group ring: Lemma 10.1 and
# Corollary 10.2 (module form)

Folder `RequestProject/Fold/`, namespace `Fold`. Nothing listed in the Setting is redefined:
C17 `CubeLaplacian.G`, `e`, `lap`; C18 `DPLattice`, `Hop`/`H`, `Hom`, `tensorPow`, `pt`, `wt_pt`
(with `pt_bijective`), `Tn`, `psi`, `psi_comm`, `bvec`, `slice`, `tensorFd` (with `gSplit`,
`slice0_psi_succ`, `slice1_psi_succ`, `ext_slice`, `range_pi_eq`); C20 `Doubling.Iso`; C25
`LemmaW.IsWtPres`, `LemmaW.P1`; C29 `Filt.T`, `Filt.tpow`; C30 `Step36.dsumList`; C31 `FamDec.L`,
`FamDec.D2`; C32 `Families.Q0`, `Families.isoEquiv` are used directly. Listed items not needed by
name: C17 `coker`, `K`, `Syl2` (`cokerBar`, `KBar` are defined in the same way); C20 `Iso.trans`,
`Iso.symm`; C31 `FamDec.m`, `FamDec.Z1_D2` ((C2) is obtained from (C1) with the hypotheses of
C28 `Lift2.Z1` and C21 `Twist.C3_hyp`, exactly as C31 `Z1_D2` is obtained from `D2`); C32 `Q1`
(an existence statement only mentioning `Fd 1` and `H`; its equivalence is rebuilt, by the same
recursion, as the definition `dsumMapEquiv`, which carries every `Fd r` and every diagonal operator
componentwise).

## Encodings (`Defs.lean`)

* `aElt n = fun _ => 1 : G n`; `transl A n f = fun g => f (g + aElt n)`;
  `foldSub A n = range (lap A n) ⊔ range (transl A n − 1)`.
* `Gbar n = G n ⧸ AddSubgroup.zmultiples (aElt n)`, `mk n : G n →+ Gbar n` the quotient map;
  `lapBar A n u x = n·u x − Σ_i u (x + mk n (e n i))`;
  `cokerBar n = (Gbar n → ℤ) ⧸ range (lapBar ℤ n)`, `KBar n = Submodule.torsion ℤ (cokerBar n)`;
  `push A n f x = Σ_{g ∈ univ.filter (mk n g = x)} f g`.
* For `M : DPLattice A`, `c : ℤ`, `B : ℕ`: `signOp M c f i = (−1)^{((c − wt i)/2).natAbs} * f i`
  (`Int.ediv`), `expF M B = Σ_{r ∈ range B} M.Fd r`, `aOp M c B = signOp M c ∘ₗ expF M B`,
  `tauOp M c = M.Fd 1 + (c : A) • 1 − H M`,
  `Xbar M c B = (M.ι → A) ⧸ (range (tauOp M c) ⊔ range (aOp M c B − 1))`.
* "`≃ₗ[A]`" statements are given both as explicit definitions (`G3equiv`, `G3Zequiv`, `L3equiv`,
  `L4equiv`, `foldEquivXbar`) and as `Nonempty (… ≃ₗ[A] …)` theorems; (C1), (C2) are `Nonempty`
  because C31 (D2) is.

## Where each part is

* **Part G** (`PartG.lean`): `G1`; `G2` (= `push_surjective`, `ker_push`, `push_lap`); `G3equiv`,
  `G3equiv_symm_mk` (induced by `push`), `G3`; `G3Zequiv`, `G3Z` (the case `A = ℤ`, `cokerBar`).
* **Part L** (`PartL.lean`, `Transport.lean`): `L0`; `L1` (Lemma 10.1); `L2`; `L3` (and
  `L3equiv`, `L3_charZero` for the last sentence, via C25 `P1`); `L4` (for every list `Ls`) and
  its general form `L4_map` for lists `l.map f` (with `L4equiv`).
* **Part C** (`Corollary.lean`): `foldEquivXbar` (`(G n → A) ⧸ foldSub ≃ Xbar (tensorPow A n) n
  (n + 1)`), `C1` (Corollary 10.2, module form), `C2` (the case `ℤ_[2]`).

## Hypotheses

* (L3): `IsWtPres u.inv.toLin` is kept as in the file but is unused (named `_hinv`); only the
  weight-preservation of `u.hom.toLin` is needed, and only for `signOp` and `aOp`.
* (C1): all hypotheses of C30 (A1) are used, through C31 (D2); `[IsDomain A] [CharZero A]` are
  also used through C25 (P1).
* Parts G, (L0), (L1), (L2), (L4) hold for every commutative ring `A`, with no hypothesis.
-/
