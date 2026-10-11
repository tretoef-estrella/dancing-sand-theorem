module

public import RequestProject.FormalAct.PartT
public import RequestProject.FormalAct.PartN

/-!
# `C40c_the_action_of_a_system_and_one_move.md`: Part S — one move of the dance

Over `[IsDomain A] [CharZero A] [Doubling.OddUnits A]` (needed to form `Doubling.phi`).

* (S1) `S1` (a twist move), via the explicit equivalence `S1equivQ` (for an explicit witness `Q`
  of `CleanStep G G'`). Proof as in the file: by (T1), `sysAct (phi N) (2W+1) B G` is conjugate,
  by `pack` on the sources and `pack ∘ swap` on the coordinates, to the block operator
  `blockOp P C Bb Dd` of C40 with `P = sysAct (twP G)` (a linear equivalence `pivotEquiv` with
  inverse `sysAct Q`, by (A1), (A2)), `C = sysAct (twC G)`, `Bb = sysAct (twB G)`,
  `Dd = sysAct (twD G)`; its Schur complement is `(2 : A) • sysAct G'` (`schur_eq`); conclude with
  C40's `S3equiv`.
* (S2) `S2` (a split move), via `S2equivQ`: by (T2) and (N1), `sysAct (tensorV (phi N)) (2W+2) B G`
  is conjugate by `vpack` to `sysAct (phi N) (2W+1) (2 * BN) (vsplit G)`, then (S1) on the index
  type `n × Fin 2`.

All hypotheses of the file are used: (top W) through (A1) and (T1), (nil BN) through (A2), (T1),
(N1), `1 ≤ B'` for the unit in (A2), `BN ≤ B'` in (A2), (T1), and `2 * BN ≤ B`,
resp. `2 * BN + 1 ≤ B`, in (T1), resp. (T2).
-/

@[expose] public section

noncomputable section

namespace FormalAct

open DPLattice Doubling FormalOps FormalDance Finset Pointwise

variable {A : Type*} [CommRing A]
  {n : Type*} [Fintype n] [DecidableEq n] {N : DPLattice A} {W : ℤ} {BN : ℕ}

section S1

variable (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
  {B B' : ℕ} (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G G' Q : Matrix n n (Bf A)}
  (hPQ : MAgree (twP G * Q) 1) (hQP : MAgree (Q * twP G) 1)

include htop hnil hB' hB1 hPQ hQP in
/-- (S1), auxiliary: under a clean move with witness `Q`, the pivot `P = sysAct N W B' (twP G)` is
a linear equivalence with inverse `sysAct N W B' Q`. -/
def pivotEquiv : (n → N.ι → A) ≃ₗ[A] (n → N.ι → A) :=
  LinearEquiv.ofLinear (sysAct N W B' (twP G)) (sysAct N W B' Q)
    (by rw [← sysAct_mul hnil hB', A1 htop hPQ, sysAct_one hB1])
    (by rw [← sysAct_mul hnil hB', A1 htop hQP, sysAct_one hB1])

include htop hnil hB' hB1 hPQ hQP in
/-- (S1), auxiliary: the Schur complement of the twist blocks is `(2 : A) • sysAct N W B' G'`. -/
lemma schur_eq (hS : MAgree (twD G - twB G * Q * twC G) ((2 : A) • G')) :
    schur (pivotEquiv htop hnil hB' hB1 hPQ hQP) (sysAct N W B' (twC G)) (sysAct N W B' (twB G))
      (sysAct N W B' (twD G)) = (2 : A) • sysAct N W B' G' := by
  show sysAct N W B' (twD G) - sysAct N W B' (twB G) ∘ₗ sysAct N W B' Q ∘ₗ
    sysAct N W B' (twC G) = _
  rw [← sysAct_mul hnil hB' Q, ← sysAct_mul hnil hB', ← sysAct_sub, ← Matrix.mul_assoc,
    A1 htop hS, sysAct_smul]

end S1

variable [IsDomain A] [CharZero A] [OddUnits A]

section S1'

variable (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
  {B B' : ℕ} (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G G' Q : Matrix n n (Bf A)}
  (hPQ : MAgree (twP G * Q) 1) (hQP : MAgree (Q * twP G) 1)

/-- (S1), the twist move with an explicit witness `Q` of `CleanStep G G'`, as an explicit linear
equivalence of cokernels. -/
def S1equivQ (hB : 2 * BN ≤ B) (hS : MAgree (twD G - twB G * Q * twC G) ((2 : A) • G'))
    (h : ℕ) :
    ((n → (phi N).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (phi N) (2 * W + 1) B G)) ≃ₗ[A]
      (((n → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n → N.ι → A))) ×
        ((n → N.ι → A) ⧸ LinearMap.range ((2 : A) ^ (h + 1) • sysAct N W B' G'))) :=
  (quotEquivConj (pack : _ ≃ₗ[A] (n → (phi N).ι → A))
    ((LinearEquiv.prodComm A _ _).trans (pack : _ ≃ₗ[A] (n → (phi N).ι → A)))
    ((2 : A) ^ h • blockOp (pivotEquiv htop hnil hB' hB1 hPQ hQP) (sysAct N W B' (twC G))
      (sysAct N W B' (twB G)) (sysAct N W B' (twD G)))
    ((2 : A) ^ h • sysAct (phi N) (2 * W + 1) B G) (by
      refine LinearMap.ext fun ⟨u, v⟩ => ?_
      show (2 : A) ^ h • sysAct (phi N) (2 * W + 1) B G (pack (u, v)) =
        pack ((2 : A) ^ h • (sysAct N W B' (twB G) u + sysAct N W B' (twD G) v),
          (2 : A) ^ h • (sysAct N W B' (twP G) u + sysAct N W B' (twC G) v))
      rw [T1 htop hnil hB hB' G u v]
      exact (map_smul pack _ _).symm)).symm.trans
  (S3equiv _ _ _ _ (sysAct N W B' G') (schur_eq htop hnil hB' hB1 hPQ hQP hS) h)

end S1'

/-- **(S1)** of `C40c_the_action_of_a_system_and_one_move.md` (a twist move): if `N` satisfies
(top W) and (nil BN), `2 * BN ≤ B`, `BN ≤ B'`, `1 ≤ B'` and `CleanStep G G'`, then for every
`h : ℕ`, the cokernel of `(2 : A) ^ h • sysAct (phi N) (2W+1) B G` is isomorphic to
`(n → N.ι → A) ⧸ (2 : A) ^ h • ⊤` times the cokernel of `(2 : A) ^ (h + 1) • sysAct N W B' G'`. -/
theorem S1 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    {B B' : ℕ} (hB : 2 * BN ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G G' : Matrix n n (Bf A)}
    (hC : CleanStep G G') (h : ℕ) :
    Nonempty (((n → (phi N).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (phi N) (2 * W + 1) B G)) ≃ₗ[A]
      (((n → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n → N.ι → A))) ×
        ((n → N.ι → A) ⧸ LinearMap.range ((2 : A) ^ (h + 1) • sysAct N W B' G')))) := by
  obtain ⟨Q, hPQ, hQP, hS⟩ := hC
  exact ⟨S1equivQ htop hnil hB' hB1 hPQ hQP hB hS h⟩

/-- (S2), the split move with an explicit witness `Q` of `CleanStep (vsplit G) G''`, as an explicit
linear equivalence of cokernels. -/
def S2equivQ (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    {B B' : ℕ} (hB : 2 * BN + 1 ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G : Matrix n n (Bf A)}
    {G'' Q : Matrix (n × Fin 2) (n × Fin 2) (Bf A)}
    (hPQ : MAgree (twP (vsplit G) * Q) 1) (hQP : MAgree (Q * twP (vsplit G)) 1)
    (hS : MAgree (twD (vsplit G) - twB (vsplit G) * Q * twC (vsplit G)) ((2 : A) • G''))
    (h : ℕ) :
    ((n → (tensorV (phi N)).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (tensorV (phi N)) (2 * W + 2) B G)) ≃ₗ[A]
      (((n × Fin 2 → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n × Fin 2 → N.ι → A))) ×
        ((n × Fin 2 → N.ι → A) ⧸ LinearMap.range ((2 : A) ^ (h + 1) • sysAct N W B' G''))) :=
  (quotEquivConj (vpack : _ ≃ₗ[A] (n → (tensorV (phi N)).ι → A))
    (vpack : _ ≃ₗ[A] (n → (tensorV (phi N)).ι → A))
    ((2 : A) ^ h • sysAct (phi N) (2 * W + 1) (2 * BN) (vsplit G))
    ((2 : A) ^ h • sysAct (tensorV (phi N)) (2 * W + 2) B G) (by
      rw [show (2 : ℤ) * W + 2 = 2 * W + 1 + 1 by ring, LinearMap.smul_comp,
        T2 (N1 hnil) hB (le_refl (2 * BN)) G, LinearMap.comp_smul])).symm.trans
  (S1equivQ htop hnil hB' hB1 hPQ hQP (le_refl (2 * BN)) hS h)

/-- **(S2)** of `C40c_the_action_of_a_system_and_one_move.md` (a split move): if `N` satisfies
(top W) and (nil BN), `2 * BN + 1 ≤ B`, `BN ≤ B'`, `1 ≤ B'` and `CleanStep (vsplit G) G''` with
`G'' : Matrix (n × Fin 2) (n × Fin 2) (Bf A)`, then for every `h : ℕ`, the cokernel of
`(2 : A) ^ h • sysAct (tensorV (phi N)) (2W+2) B G` is isomorphic to
`(n × Fin 2 → N.ι → A) ⧸ (2 : A) ^ h • ⊤` times the cokernel of
`(2 : A) ^ (h + 1) • sysAct N W B' G''`. -/
theorem S2 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    {B B' : ℕ} (hB : 2 * BN + 1 ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G : Matrix n n (Bf A)}
    {G'' : Matrix (n × Fin 2) (n × Fin 2) (Bf A)} (hC : CleanStep (vsplit G) G'') (h : ℕ) :
    Nonempty (((n → (tensorV (phi N)).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (tensorV (phi N)) (2 * W + 2) B G)) ≃ₗ[A]
      (((n × Fin 2 → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n × Fin 2 → N.ι → A))) ×
        ((n × Fin 2 → N.ι → A) ⧸ LinearMap.range ((2 : A) ^ (h + 1) • sysAct N W B' G'')))) := by
  obtain ⟨Q, hPQ, hQP, hS⟩ := hC
  exact ⟨S2equivQ htop hnil hB hB' hB1 hPQ hQP hS h⟩

end FormalAct
