module

public import RequestProject.LiftExt.PartB

/-!
# `C26_lifting_and_extension.md`: index

Lemma 3.3 for one pair, in its lifting and extension forms, namespace `LiftExt`.

Reused, not redefined: from C18 (`DPLattice`) `DPLattice`, `IsDP`, `Hom`, `delta`, `nabla`,
`weylWt`, `deltaF`, `deltaE`; from C19 (`WeylFilt`) `Hom.id`, `Hom.comp`, `Hom.ext'`,
`ShortExact`; from C20 (`Doubling`) `Iso`; from C25 (`LemmaW`) `IsWtPres`, `pr`, `HasWt`, `trM`,
`dual`, `dualHom`, `isoDualDual`, `isoDualDelta`, `isoDualNabla`, `sW`, `sWHom'`, and the results
`P1`, `P2_wtPres`, `P2_F`, `P2_E`, `D5`, `W1`, `E2`, with the auxiliary lemmas `K_vec`,
`sW_single`, `trM_comp`, `trM_trM`, `dualHom_wtPres`, `exists_retraction_of_section`,
`pr_eq_zero_of_noWt`, `prW_delta_single_zero`, `deltaF_single_zero`.

Encodings:
* vectors of a DP-lattice `M` are functions `M.ι → A`; `δ_i = Pi.single i 1`; `δ_0` of `Δ_A(l)` is
  `Pi.single (0 : Fin (l + 1)) 1`;
* a morphism is a C18 `Hom`, its underlying linear map `.toLin`; a short exact sequence is C19's
  `ShortExact f g`; an isomorphism is a C20 `Iso`;
* weight-preserving: C25's `IsWtPres`; "`z` has weight `w`": C25's `HasWt M w z`;
  "`K` has weights in `[a, b]`": `WtIn K a b` (`∀ i, a ≤ K.wt i ∧ K.wt i ≤ b`);
* the duality is C25's `dual` / `dualHom` (transpose `trM`), with the identity isomorphisms
  `isoDualDual`, `isoDualDelta`, `isoDualNabla`;
* the lift of (L1) has underlying map C25's `sW x` (`δ_r ↦ F^{(r)} x`); the extension of (X1)
  has underlying map `k ∘ ρ` with `f ∘ ρ = id − sW x ∘ g`;
* `ℤ_[2]` is Mathlib's `PadicInt 2`.

Contents:
* `Basic.lean`: Setting (`WtIn`), Part L — `L0`, `L1` (and `L1_W4`: C25 (W4) as a special case).
* `PartX.lean`: Part X — `X1_gen` (`K` with weights in `[−l − 1, l + 1]`), `X1`.
* `PartB.lean`: Part B — `B1_le`, `B1_gt`, `B1`, `B2_le`, `B2_gt`, `B2`, `B3_lift`, `B3_ext`,
  `B3`, `B4`, `B5`.
-/
