module

public import RequestProject.FormalAct.Defs
public import RequestProject.FormalAct.PartN
public import RequestProject.FormalAct.PartA
public import RequestProject.FormalAct.PartT
public import RequestProject.FormalAct.PartS

/-!
# `C40c_the_action_of_a_system_and_one_move.md` — the action of a system on a lattice, and one
# move of the dance (paper v8 §10.3, proof of Proposition 10.7, one step)

Folder `RequestProject/FormalAct/`, namespace `FormalAct`. Nothing listed in the Setting is
redefined. Used directly: C18 `DPLattice` (`ι`, `wt`, `Fd`, `isDP.P0_F`), `DPLattice.one`
(with `oneFd`), `DPLattice.bvec`, `DPLattice.slice` (with `eq_bvec_slice`), `DPLattice.tensorV`;
C20 `Doubling.phi`; C29 `Filt.T` with `T_zero`, `T_odd`, `T_even`; C39 `FoldHalf.E0` (which is
(N1)); C40 `FormalOps.Bf`, `flD`, `act`, `blockOp`, `schur` and the theorems `act_one`, `act_add`,
`act_smul`, `act_mul` (parts of `B4`), `T0`, `T1`, `V0`, `V1`, `S3equiv` (the explicit form of
`S3`); C40b `FormalDance.MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep`, `finalM` and
`C4`. (C40's `Doubling.dfi`, `tw00`, …, `vprime` enter through `twP`, …, `vsplit` and C40's
`T1`, `V1`; C40's `S1`, `S2` and C40b's `C1`–`C3` are not needed by any proof.)

## Encodings (`Defs.lean`)
* A system is `G : Matrix n n (Bf A)` with `[Fintype n] [DecidableEq n]`; `G[s, s']` maps the
  source slot `s'` to the coordinate slot `s`. A vector of `N^{⊕n}` is `v : n → N.ι → A`.
* `sysAct N W B G : (n → N.ι → A) →ₗ[A] (n → N.ι → A)`,
  `(sysAct N W B G v) s = Σ_{s'} act N W B (G s s') (v s')`, exactly as in the file.
* `pack : (n → ι → A) × (n → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A)`,
  `pack (u, v) = fun s => bvec 0 (u s) + bvec 1 (v s)`, and
  `vpack : (n × Fin 2 → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A)`,
  `vpack w = fun s => bvec 0 (w (s, 0)) + bvec 1 (w (s, 1))`, exactly as in the file; the inverses
  read the slots with `slice 0`, `slice 1`. For `phi N` and `tensorV M` the basis is
  `Fin 2 × N.ι`, resp. `Fin 2 × M.ι`, so `n → (phi N).ι → A` is `n → Fin 2 × N.ι → A`.
* The cokernel of `f` is `M ⧸ LinearMap.range f`; the submodule `c M` is `(c • ⊤ : Submodule A M)`.
  `(2 : A) ^ h • sysAct …` is the scalar multiple of a linear map.
* (top W) is `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)` and (nil BN) is `∀ s ≥ BN, N.Fd s = 0`.
* Each "`Nonempty (… ≃ₗ[A] …)`" statement is also given by an explicit equivalence (`A3equiv`,
  `A4equiv`, `S1equivQ`, `S2equivQ`).

## Where each part is
* **Part N** (`PartN.lean`): (N1) `N1`; (N2) `N2`.
* **Part A** (`PartA.lean`): (A1) `A1`; (A2) `sysAct_one`, `sysAct_mul`, `sysAct_add`,
  `sysAct_sub`, `sysAct_smul`, collected in `A2`; (A3) `A3_conj` and `A3`; (A4) `A4_apply` and `A4`.
* **Part T** (`PartT.lean`): (T1) `T1`; (T2) `T2`.
* **Part S** (`PartS.lean`): (S1) `S1`; (S2) `S2`.

## Instances and hypotheses
* `Doubling.phi` and `Filt.T` only exist over `[IsDomain A] [CharZero A] [OddUnits A]`, so (N1),
  (N2), (T1), (S1), (S2) carry these instances (as the file says). Everything else is over any
  commutative ring.
* In (A2), `1 ≤ B` is only used for the unit and (nil BN), `BN ≤ B` only for the product; the sum,
  difference and scalar statements are also proved for every `B` without (nil BN) (more general).
* (A3) and (A4) need no hypothesis besides those stated (`1 ≤ B` in (A4) is used).
* (T2) is stated, as in the file, without (top W). All other hypotheses of the file are used.
-/
