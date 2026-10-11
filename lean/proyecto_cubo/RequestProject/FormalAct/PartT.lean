module

public import RequestProject.FormalAct.PartA

/-!
# `C40c_the_action_of_a_system_and_one_move.md`: Part T — the twist map and the V-split on systems

* (T1) `T1` (C40's `T1` entrywise, and linearity of `bvec`), over
  `[IsDomain A] [CharZero A] [Doubling.OddUnits A]` (needed to form `Doubling.phi`);
* (T2) `T2` (C40's `V1` entrywise, `vsplit` read slot by slot), over any commutative ring.

The vectors of `(phi N)^{⊕n}` are functions `n → (phi N).ι → A = n → Fin 2 × N.ι → A`, and those
of `(tensorV M)^{⊕n}` are functions `n → Fin 2 × M.ι → A`; `pack` and `vpack` are those of
`Defs.lean` with `ι = N.ι`, resp. `ι = M.ι`.
-/

@[expose] public section

noncomputable section

namespace FormalAct

open DPLattice Doubling FormalOps FormalDance Finset

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n]

/-- **(T1)** of `C40c_the_action_of_a_system_and_one_move.md`: if `N` satisfies (top W) and
(nil BN), `2 * BN ≤ B` and `BN ≤ B'`, then for all `u v : n → N.ι → A`,
`sysAct (phi N) (2W+1) B G (pack (u, v)) = pack (sysAct N W B' (twB G) u + sysAct N W B' (twD G) v,
sysAct N W B' (twP G) u + sysAct N W B' (twC G) v)`. -/
theorem T1 [IsDomain A] [CharZero A] [OddUnits A] {N : DPLattice A} {W : ℤ} {BN : ℕ}
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    {B B' : ℕ} (hB : 2 * BN ≤ B) (hB' : BN ≤ B') (G : Matrix n n (Bf A))
    (u v : n → N.ι → A) :
    sysAct (phi N) (2 * W + 1) B G (pack (u, v)) =
      pack (sysAct N W B' (twB G) u + sysAct N W B' (twD G) v,
        sysAct N W B' (twP G) u + sysAct N W B' (twC G) v) := by
  funext s
  simp only [sysAct_apply, pack_apply, Pi.add_apply, map_add, map_sum,
    (FormalOps.T1 htop hnil _ _ hB hB').1, (FormalOps.T1 htop hnil _ _ hB hB').2,
    Finset.sum_add_distrib, twB, twD, twP, twC]
  abel

/-- **(T2)** of `C40c_the_action_of_a_system_and_one_move.md`: if `M` satisfies (nil BN),
`BN + 1 ≤ B` and `BN ≤ B'`, then
`sysAct (tensorV M) (W + 1) B G ∘ₗ vpack = vpack ∘ₗ sysAct M W B' (vsplit G)`.
(No (top W) is needed, as in C40's `V1`.) -/
theorem T2 {M : DPLattice A} {W : ℤ} {BN : ℕ} (hnil : ∀ s ≥ BN, M.Fd s = 0) {B B' : ℕ}
    (hB : BN + 1 ≤ B) (hB' : BN ≤ B') (G : Matrix n n (Bf A)) :
    sysAct (tensorV M) (W + 1) B G ∘ₗ (vpack : (n × Fin 2 → M.ι → A) ≃ₗ[A] _).toLinearMap =
      (vpack : (n × Fin 2 → M.ι → A) ≃ₗ[A] _).toLinearMap ∘ₗ sysAct M W B' (vsplit G) := by
  refine LinearMap.ext fun w => funext fun s => ?_
  show ∑ s', act (tensorV M) (W + 1) B (G s s') (vpack w s') =
    vpack (sysAct M W B' (vsplit G) w) s
  simp only [sysAct_apply, vpack_apply, map_add,
    (V1 hnil _ _ hB hB').1, (V1 hnil _ _ hB hB').2, Fintype.sum_prod_type, Fin.sum_univ_two,
    vsplit, map_sum, Finset.sum_add_distrib]
  simp [act_zero']
  abel

end FormalAct
