module

public import RequestProject.DanceXi.PartT
public import RequestProject.Smith2.All
public import RequestProject.FormalProp.All

/-!
# `C48b_the_dance_of_Xi_is_clean.md`: Part R — Theorem 10.16 for `c ≥ 1`

Namespace `DanceXi`. Reused without change: C46 `Smith2.XiOpZ`, `Smith2.R5`; C40c
`FormalAct.sysAct`; C40d `FormalProp.Q2_zero`; C29 `Filt.T`, `Filt.T_zero`; C32 `Families.ds`,
`Families.ds_zero`; C16 `FamilyGroup.X`; C13 `Dance.SysT`, `Dance.sigma`, `Dance.F`, `Dance.pσ`,
`Dance.κσ`; C11 `Payment.G`; C40b `FormalDance.finalM`.

* (R0) `R0`: by `Q2_zero` the left cokernel is that of `finalM (fun _ _ => XiOpZ α c η ζ)`,
  which is multiplication by `2^α c` on `Fin 1 → ℤ_[2]` (`mulVecLin_finalM_XiOpZ`); for `1 ≤ α`,
  `Dance.sigma ℤ_[2] [] α c` is multiplication by `2^α c` on `SysT ℤ_[2] [] (Fin 1)`
  (`sigma_nil`). Both modules are free of rank one (`finOneSysTNil`), and the cokernels of a
  scalar multiplication along a linear equivalence are isomorphic (`quotSmulEquiv`).
* (R1) `R1`: (T3) with `ds := Families.ds l` gives the hypothesis of C46 (R5).
* (R2) `R2`: (R0) for `l = 0`, (R1) for `l ≥ 1`.
-/

@[expose] public section

noncomputable section

namespace DanceXi

open FormalOps FormalDance

/-- (R0) of `C48b_the_dance_of_Xi_is_clean.md`, auxiliary: a linear equivalence `φ : M ≃ M'`
induces an isomorphism of the cokernels of the multiplications by the same scalar `a`. -/
def quotSmulEquiv {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] (φ : M ≃ₗ[R] M') (a : R) :
    (M ⧸ LinearMap.range (a • LinearMap.id : M →ₗ[R] M)) ≃ₗ[R]
      (M' ⧸ LinearMap.range (a • LinearMap.id : M' →ₗ[R] M')) :=
  Submodule.Quotient.equiv _ _ φ (by
    rw [← LinearMap.range_comp]
    have : (φ : M →ₗ[R] M') ∘ₗ (a • LinearMap.id) = (a • LinearMap.id) ∘ₗ (φ : M →ₗ[R] M') := by
      ext x; simp
    rw [this, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ)])

/-- (R0) of `C48b_the_dance_of_Xi_is_clean.md`, auxiliary: the `1 × 1` final matrix of `Ξ` acts
as multiplication by `2^α c`. -/
lemma mulVecLin_finalM_XiOpZ (α c : ℕ) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) :
    Matrix.mulVecLin (finalM (fun _ _ : Fin 1 => Smith2.XiOpZ α c η ζ)) =
      ((2 : ℤ_[2]) ^ α * c) • LinearMap.id := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp [finalM, Smith2.XiOpZ, Matrix.mulVec, dotProduct, Fin.fin_one_eq_zero i]

/-- (R0) of `C48b_the_dance_of_Xi_is_clean.md`, auxiliary: for `1 ≤ α`, `σ` on the tower
`T([])` (where `F = 0`) is multiplication by `2 · 2^{α−1} c = 2^α c`. -/
lemma sigma_nil (α c : ℕ) (hα : 1 ≤ α) :
    Dance.sigma ℤ_[2] [] α c = ((2 : ℤ_[2]) ^ α * c) • LinearMap.id := by
  refine DirectSum.linearMap_ext ℤ_[2] fun q => LinearMap.ext fun x => ?_
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 1 := ⟨α - 1, by omega⟩
  simp [Dance.sigma, Payment.G, Dance.F, Dance.pσ, Dance.κσ, Dance.fl, Payment.slotLof,
    pow_succ]
  congr 1
  ring

/-- (R0) of `C48b_the_dance_of_Xi_is_clean.md`, auxiliary: `Fin 1 → ℤ_[2]` and
`SysT ℤ_[2] [] (Fin 1)` (indexed by `Fin 1 × Idx []`, `Idx [] = Unit`) are isomorphic. -/
def finOneSysTNil : (Fin 1 → ℤ_[2]) ≃ₗ[ℤ_[2]] Dance.SysT ℤ_[2] [] (Fin 1) :=
  letI : Unique (Dance.Idx []) := inferInstanceAs (Unique Unit)
  (LinearEquiv.funCongrLeft ℤ_[2] ℤ_[2] (Equiv.prodUnique (Fin 1) (Dance.Idx []))).trans
    (DirectSum.linearEquivFunOnFintype ℤ_[2] (Fin 1 × Dance.Idx []) (fun _ => ℤ_[2])).symm

/-- **(R0)** of `C48b_the_dance_of_Xi_is_clean.md` (the family `l = 0`, every `c`): for `α c : ℕ`
with `1 ≤ α`, every `η : ℤ_[2]`, every `ζ : ℕ → ℤ → ℤ_[2]` and every `B ≥ 1`, the cokernel of
`sysAct (Filt.T ℤ_[2] 0) 0 B (fun _ _ => XiOpZ α c η ζ)` is isomorphic to
`FamilyGroup.X (Families.ds 0) α c`. -/
theorem R0 (α c : ℕ) (hα : 1 ≤ α) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) (B : ℕ) (hB : 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] 0).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] 0) (0 : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η ζ))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds 0) α c) := by
  obtain ⟨e1⟩ := FormalProp.Q2_zero 1 (fun _ _ => Smith2.XiOpZ α c η ζ) B hB
  rw [mulVecLin_finalM_XiOpZ] at e1
  rw [Families.ds_zero]
  unfold FamilyGroup.X
  rw [sigma_nil α c hα]
  exact ⟨e1.trans (quotSmulEquiv finOneSysTNil _)⟩

/-- **(R1)** of `C48b_the_dance_of_Xi_is_clean.md` (`l ≥ 1`, `c ≥ 1`): for `1 ≤ l`, `2 ≤ α`,
`1 ≤ c`, `IsUnit η`, `z : ℕ → ℤ_[2]` and every `B ≥ l + 1`, the cokernel of
`sysAct (Filt.T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η (fun m _ => z m))` is isomorphic to
`FamilyGroup.X (Families.ds l) α c`. -/
theorem R1 (l α c : ℕ) (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) (η : ℤ_[2]) (hη : IsUnit η)
    (z : ℕ → ℤ_[2]) (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α c) := by
  obtain ⟨GkZ, hG⟩ := T3 (Families.ds l) α c hα η hη z
  exact Smith2.R5 hl hα hc hη (fun m _ => z m) GkZ hG B hB

/-- **(R2)** of `C48b_the_dance_of_Xi_is_clean.md` (Theorem 10.16 for `c ≥ 1`): for every `l`,
`2 ≤ α`, `1 ≤ c`, `IsUnit η`, `z : ℕ → ℤ_[2]` and every `B ≥ l + 1`, the cokernel of
`sysAct (Filt.T ℤ_[2] l) l B (fun _ _ => XiOpZ α c η (fun m _ => z m))` is isomorphic to
`FamilyGroup.X (Families.ds l) α c` (the same isomorphism as in (R1)). -/
theorem R2 (l α c : ℕ) (hα : 2 ≤ α) (hc : 1 ≤ c) (η : ℤ_[2]) (hη : IsUnit η)
    (z : ℕ → ℤ_[2]) (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α c) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rw [Nat.cast_zero]
    exact R0 α c (by omega) η (fun m _ => z m) B hB
  · exact R1 l α c hl hα hc η hη z B hB

end DanceXi
