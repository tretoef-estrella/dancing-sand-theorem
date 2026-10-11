module

public import RequestProject.GlueEven.Defs

/-!
# `C50f_the_glued_system_on_T.md`: Part S — a glued system of size 2 is `glueOp`

(S1) the size-2 system `glueC h21 x y z` acts, after `pairE`, as `glueOp (act x) (act y) (act z)`;
(S2) hence the two scaled cokernels are isomorphic. Both are stated for every `DPLattice`, every
`W` and every `B`.
-/

@[expose] public section

noncomputable section

namespace GlueEven

open FormalOps FormalAct

/-- Helper for (S1) of `C50f_the_glued_system_on_T.md`: at `r = 1`, `(gE h21).symm j = (j, 0)`. -/
lemma gE_symm_one (h21 : (2 : ℕ) = 2 * 1) (j : Fin 2) : (GlueDance.gE h21).symm j = (j, 0) := by
  rw [GlueDance.gE_symm_apply, finProdFinEquiv_symm_apply]
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [Fin.coe_divNat]

/-- **(S1)** of `C50f_the_glued_system_on_T.md`: for `N : DPLattice ℤ_[2]`, `W : ℤ`, `B : ℕ`,
`x y z : Bf ℤ_[2]` and `v : Fin 2 → N.ι → ℤ_[2]`,
`pairE _ (sysAct N W B (glueC h21 (fun _ _ => x) (fun _ _ => y) (fun _ _ => z)) v) =
glueOp (act N W B x) (act N W B y) (act N W B z) (pairE _ v)`. -/
theorem S1 (h21 : (2 : ℕ) = 2 * 1) (N : DPLattice ℤ_[2]) (W : ℤ) (B : ℕ) (x y z : Bf ℤ_[2])
    (v : Fin 2 → N.ι → ℤ_[2]) :
    pairE _ (FormalAct.sysAct N W B
        (GlueDance.glueC h21 (fun _ _ => x) (fun _ _ => y) (fun _ _ => z)) v) =
      FoldHalf.glueOp (act N W B x) (act N W B y) (act N W B z) (pairE _ v) := by
  simp only [pairE_apply, sysAct_apply, Fin.sum_univ_two, FoldHalf.glueOp_apply,
    GlueDance.glueC, gE_symm_one, GlueDance.glueM_00, GlueDance.glueM_01, GlueDance.glueM_10,
    GlueDance.glueM_11, act_zero', LinearMap.zero_apply, add_zero]

/-- **(S2)** of `C50f_the_glued_system_on_T.md`: for every `h : ℕ`, the quotient of
`Fin 2 → N.ι → ℤ_[2]` by the range of `2 ^ h • sysAct N W B (glueC h21 …)` is linearly equivalent
to the quotient of `(N.ι → ℤ_[2]) × (N.ι → ℤ_[2])` by the range of
`2 ^ h • glueOp (act N W B x) (act N W B y) (act N W B z)`. -/
theorem S2 (h21 : (2 : ℕ) = 2 * 1) (N : DPLattice ℤ_[2]) (W : ℤ) (B : ℕ) (x y z : Bf ℤ_[2])
    (h : ℕ) :
    Nonempty (((Fin 2 → N.ι → ℤ_[2]) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h •
        FormalAct.sysAct N W B
          (GlueDance.glueC h21 (fun _ _ => x) (fun _ _ => y) (fun _ _ => z)))) ≃ₗ[ℤ_[2]]
      (((N.ι → ℤ_[2]) × (N.ι → ℤ_[2])) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h •
        FoldHalf.glueOp (act N W B x) (act N W B y) (act N W B z)))) :=
  ⟨quotEquivConj (pairE _) (pairE _) _ _ (LinearMap.ext fun v => by
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul]
    rw [S1])⟩

end GlueEven
