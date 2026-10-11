module

public import RequestProject.InvBlock.Defs

/-!
# `C41_inverse_block.md`: (V1) one twist move, (V2) one split move

* `lift N W B' Q G v = pack (−sysAct N W B' (Q * twC G) v, v)` (the lift of the file).
* (V1) `V1`: C40c (T1), with `u = −sysAct (Q * twC G) v`, then C40c (A1), (A2).
* (V2) `V2`: C40c (T2) (with C40c (N1)) turns the action on `tensorV (phi N)` into the action of
  `vsplit G` on `phi N` through `vpack`; then (V1) on the index type `n × Fin 2`.

Hypotheses: the hypothesis `MAgree (Q * twP G) 1` of the file (the other half of the clean step)
is not needed for (V1) and (V2), and is omitted (more general). All other hypotheses are used.
-/

@[expose] public section

noncomputable section

namespace InvBlock

open DPLattice Doubling Filt FormalOps FormalDance FormalAct

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n]

/-- (V1) of `C41_inverse_block.md`: the lift `lift v := pack (−sysAct N W B' (Q * twC G) v, v)`,
as a linear map. -/
def lift (N : DPLattice A) (W : ℤ) (B' : ℕ) (Q G : Matrix n n (Bf A)) :
    (n → N.ι → A) →ₗ[A] (n → Fin 2 × N.ι → A) :=
  (pack : _ ≃ₗ[A] (n → Fin 2 × N.ι → A)).toLinearMap ∘ₗ
    LinearMap.prod (-sysAct N W B' (Q * twC G)) LinearMap.id

/-- (V1) of `C41_inverse_block.md`: the formula of `lift`. -/
@[simp] lemma lift_apply (N : DPLattice A) (W : ℤ) (B' : ℕ) (Q G : Matrix n n (Bf A))
    (v : n → N.ι → A) : lift N W B' Q G v = pack (-sysAct N W B' (Q * twC G) v, v) := rfl

/-- (V1) of `C41_inverse_block.md`: `out₁ ∘ lift = id`. -/
lemma out1_lift (N : DPLattice A) (W : ℤ) (B' : ℕ) (Q G : Matrix n n (Bf A))
    (v : n → N.ι → A) : out1 (lift N W B' Q G v) = v := by
  simp

variable [DecidableEq n] [IsDomain A] [CharZero A] [OddUnits A]

/-- **(V1)** of `C41_inverse_block.md` (one twist move): if `N` satisfies (top W) and (nil BN),
`2 * BN ≤ B`, `BN ≤ B'`, `1 ≤ B'`, `MAgree (twP G * Q) 1` and
`MAgree (twD G − twB G * Q * twC G) ((2 : A) • G')`, then with
`lift v = pack (−sysAct N W B' (Q * twC G) v, v)`:
`sysAct (phi N) (2 * W + 1) B G (lift v) = pack ((2 : A) • sysAct N W B' G' v, 0)` and
`(pack.symm (lift v)).2 = v`, for every `v`.
(The hypothesis `MAgree (Q * twP G) 1` of the file is not needed and omitted: more general.) -/
theorem V1 {N : DPLattice A} {W : ℤ} {BN B B' : ℕ}
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (hB : 2 * BN ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G G' Q : Matrix n n (Bf A)}
    (hPQ : MAgree (twP G * Q) 1) (hS : MAgree (twD G - twB G * Q * twC G) ((2 : A) • G'))
    (v : n → N.ι → A) :
    sysAct (phi N) (2 * W + 1) B G (lift N W B' Q G v) =
        pack ((2 : A) • sysAct N W B' G' v, 0) ∧
      (pack.symm (lift N W B' Q G v)).2 = v := by
  refine ⟨?_, by simp⟩
  rw [lift_apply, T1 htop hnil hB hB' G]
  have h0 : sysAct N W B' (twD G) - sysAct N W B' (twB G) ∘ₗ sysAct N W B' (Q * twC G) =
      (2 : A) • sysAct N W B' G' := by
    rw [← sysAct_mul hnil hB', ← sysAct_sub, ← Matrix.mul_assoc, A1 htop hS, sysAct_smul]
  have h1 : sysAct N W B' (twP G) ∘ₗ sysAct N W B' (Q * twC G) = sysAct N W B' (twC G) := by
    rw [← sysAct_mul hnil hB', ← Matrix.mul_assoc, sysAct_mul hnil hB', A1 htop hPQ,
      sysAct_one hB1, LinearMap.id_comp]
  have e0 := congrArg (fun f => f v) h0
  have e1 := congrArg (fun f => f v) h1
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply] at e0 e1
  congr 2
  · rw [map_neg, ← e0]; abel
  · rw [map_neg, e1]; abel

/-- **(V2)** of `C41_inverse_block.md` (one split move): if `N` satisfies (top W) and (nil BN),
`2 * BN + 1 ≤ B`, `BN ≤ B'`, `1 ≤ B'`, and `Q` is a witness for `CleanStep (vsplit G) G''` as in
(V1) (`MAgree (twP (vsplit G) * Q) 1` and
`MAgree (twD (vsplit G) − twB (vsplit G) * Q * twC (vsplit G)) ((2 : A) • G'')`), then with the
lift built from `vsplit G` on `phi N`:
`sysAct (tensorV (phi N)) (2 * W + 2) B G (vpack (lift v)) =
vpack (pack ((2 : A) • sysAct N W B' G'' v, 0))` and `(pack.symm (vpack.symm (vpack (lift v)))).2 = v`.
(The hypothesis `MAgree (Q * twP (vsplit G)) 1` is not needed and omitted: more general.) -/
theorem V2 {N : DPLattice A} {W : ℤ} {BN B B' : ℕ}
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (hB : 2 * BN + 1 ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B') {G : Matrix n n (Bf A)}
    {G'' Q : Matrix (n × Fin 2) (n × Fin 2) (Bf A)}
    (hPQ : MAgree (twP (vsplit G) * Q) 1)
    (hS : MAgree (twD (vsplit G) - twB (vsplit G) * Q * twC (vsplit G)) ((2 : A) • G''))
    (v : n × Fin 2 → N.ι → A) :
    sysAct (tensorV (phi N)) (2 * W + 2) B G
        (vpack (lift N W B' Q (vsplit G) v : n × Fin 2 → (phi N).ι → A)) =
        vpack (pack ((2 : A) • sysAct N W B' G'' v, 0) : n × Fin 2 → (phi N).ι → A) ∧
      (pack.symm (vpack.symm
        (vpack (lift N W B' Q (vsplit G) v : n × Fin 2 → (phi N).ι → A)))).2 = v := by
  refine ⟨?_, by simp⟩
  have hT := congrArg (fun f => f (lift N W B' Q (vsplit G) v))
    (T2 (W := 2 * W + 1) (N1 hnil) hB (le_refl (2 * BN)) G)
  rw [show (2 : ℤ) * W + 2 = 2 * W + 1 + 1 by ring]
  exact hT.trans (congrArg vpack (V1 htop hnil (le_refl (2 * BN)) hB' hB1 hPQ hS v).1)

end InvBlock
