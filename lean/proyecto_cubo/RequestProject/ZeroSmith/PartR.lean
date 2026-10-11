module

public import RequestProject.ZeroSmith.PartV

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`, Part R — the cokernel at `c = 0`, and
# Theorem 10.16

(R6) `R6`; (R7) `R7`.

`T(l)` is C29's `Filt.T ℤ_[2] l`, the action is C40c's `FormalAct.sysAct`, the cokernel of a
linear map `f` is `M ⧸ LinearMap.range f`, and "isomorphic" is `Nonempty (… ≃ₗ[ℤ_[2]] …)`.
-/

@[expose] public section

noncomputable section

namespace ZeroSmith

open FormalOps FormalDance Windows Matrix
open scoped Pointwise

/-- Proof of (R6) of `C49c_smith_form_and_cokernel_at_zero.md`: if `M.submatrix e e = P * Y * Q`
with `P`, `Q` of unit determinant, then `coker (c • mulVecLin M) ≅ coker (c • toLin' Y)`
(reindexing along `e`; left multiplication by an invertible matrix is an automorphism carrying one
range onto the other, right multiplication by an invertible matrix does not change the range). -/
lemma coker_equiv_of_submatrix {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : n ≃ m) (c : R) (M : Matrix m m R)
    (Y P Q : Matrix n n R) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (h : M.submatrix e e = P * Y * Q) :
    Nonempty (((m → R) ⧸ LinearMap.range (c • Matrix.mulVecLin M)) ≃ₗ[R]
      ((n → R) ⧸ LinearMap.range (c • Matrix.toLin' Y))) := by
  let φ1 : (m → R) ≃ₗ[R] (n → R) := LinearEquiv.funCongrLeft R R e
  let φ2 : (n → R) ≃ₗ[R] (n → R) := LinearEquiv.ofLinear (toLin' P⁻¹) (toLin' P)
    (by rw [← toLin'_mul, nonsing_inv_mul _ hP, toLin'_one])
    (by rw [← toLin'_mul, mul_nonsing_inv _ hP, toLin'_one])
  have hQs : LinearMap.range (toLin' Q ∘ₗ (φ1 : (m → R) →ₗ[R] (n → R))) = ⊤ := by
    rw [LinearMap.range_comp_of_range_eq_top _ φ1.range, LinearMap.range_eq_top]
    intro v
    refine ⟨toLin' Q⁻¹ v, ?_⟩
    rw [← LinearMap.comp_apply, ← toLin'_mul, mul_nonsing_inv _ hQ, toLin'_one, LinearMap.id_apply]
  have hcomm : ((φ1.trans φ2 : (m → R) ≃ₗ[R] (n → R)) : (m → R) →ₗ[R] (n → R)) ∘ₗ
      (c • Matrix.mulVecLin M) = (c • Matrix.toLin' Y) ∘ₗ (toLin' Q ∘ₗ
        (φ1 : (m → R) →ₗ[R] (n → R))) := by
    refine LinearMap.ext fun v => ?_
    have h1 : φ1 (M *ᵥ v) = (M.submatrix e e) *ᵥ (φ1 v) := by
      funext i
      simp only [φ1, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      rw [submatrix_mulVec_equiv]
      have hv : (LinearMap.funLeft R R ⇑e) v ∘ ⇑e.symm = v := by
        funext x; simp [LinearMap.funLeft]
      rw [hv]; rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearMap.smul_apply, Matrix.mulVecLin_apply, map_smul, h1, h]
    simp only [φ2, LinearEquiv.ofLinear_apply, toLin'_apply, mulVec_mulVec, ← Matrix.mul_assoc,
      nonsing_inv_mul _ hP, Matrix.one_mul]
  refine ⟨Submodule.Quotient.equiv _ _ (φ1.trans φ2) ?_⟩
  rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp_of_range_eq_top _ hQs]

/-- **(R6)** of `C49c_smith_form_and_cokernel_at_zero.md` (the cokernel at `c = 0`): for `1 ≤ l`,
`2 ≤ α`, `IsUnit η`, `z : ℕ → ℤ_[2]` and every `B ≥ l + 1`, the cokernel of
`FormalAct.sysAct (Filt.T ℤ_[2] l) l B (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m))` is
isomorphic to `FamilyGroup.X (Families.ds l) α 0`. (No dance is assumed: C48b (T3) gives one.) -/
theorem R6 (l α : ℕ) (hl : 1 ≤ l) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α 0) := by
  set k := (Families.ds l).length
  obtain ⟨GkZ, hG⟩ := DanceXi.T3 (Families.ds l) α 0 hα η hη z
  obtain ⟨e1⟩ := FormalProp.Q1 l 1 _ GkZ hG B hB 0
  rw [pow_zero, one_smul, zero_add] at e1
  have e0 : ((a : Fin k) → (Fin (1 * 2 ^ (k + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]) ⧸
      (2 : ℤ_[2]) ^ (0 + (a : ℕ)) • (⊤ : Submodule ℤ_[2]
        (Fin (1 * 2 ^ (k + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]))) ≃ₗ[ℤ_[2]]
      FamilyGroup.SC (Families.ds l) :=
    LinearEquiv.piCongrRight fun a => Dance.pqCast (A := ℤ_[2]) (one_mul _) (zero_add _)
  obtain ⟨P, Q, hP, hQ, hX⟩ := V7 hl hα hη z GkZ hG
  obtain ⟨e2⟩ := coker_equiv_of_submatrix (finCongr (Smith2.slots_cast (Families.ds l)))
    ((2 : ℤ_[2]) ^ k) (finalM GkZ) _ P Q hP hQ (by exact hX)
  obtain ⟨e3⟩ := FamilyGroup.X_equiv_coker (Families.ds l) α 0 (by omega)
  exact ⟨(e1.trans (LinearEquiv.prodCongr e0 e2)).trans e3.symm⟩

/-- **(R7)** of `C49c_smith_form_and_cokernel_at_zero.md` (Theorem 10.16): for every `l c : ℕ`,
`2 ≤ α`, `IsUnit η`, `z : ℕ → ℤ_[2]` and `B ≥ l + 1`, the cokernel of
`FormalAct.sysAct (Filt.T ℤ_[2] l) l B (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m))` is
isomorphic to `FamilyGroup.X (Families.ds l) α c` (C48b (R2) for `1 ≤ c`, C48b (R0) for
`c = 0`, `l = 0`, and (R6) for `c = 0`, `1 ≤ l`). -/
theorem R7 (l c α : ℕ) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · rw [Nat.cast_zero]
      exact DanceXi.R0 α 0 (by omega) η (fun m _ => z m) B hB
    · exact R6 l α hl hα η hη z B hB
  · exact DanceXi.R2 l α c hα hc η hη z B hB

end ZeroSmith
