module

public import RequestProject.FoldGroup.Defs

/-!
# `C38b_the_folded_cube_and_proposition_103.md`: Part K — the folded cube over ℤ and over ℤ_2

* (K1) `K1`: `Σ_x (lapBar A n u) x = 0`.
* (K2) `K2` (with `KBar_finite` and the explicit `cokerBarEquivKBar`).
* (K3) `K3`.
-/

@[expose] public section

noncomputable section

namespace FoldGroup

open CubeLaplacian Fold Finset

/-! ### (K1) -/

/-- **(K1)** of `C38b_the_folded_cube_and_proposition_103.md`: for every commutative ring `A`,
every `n` and every `u : Gbar n → A`, `Σ_x (lapBar A n u) x = 0`. -/
theorem K1 (A : Type*) [CommRing A] (n : ℕ) (u : Gbar n → A) : ∑ x, lapBar A n u x = 0 := by
  simp only [lapBar_apply, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ i : Fin n, ∑ x, u (x + mk n (e n i)) = ∑ x, u x := fun i =>
    Fintype.sum_equiv (Equiv.addRight (mk n (e n i))) _ _ (fun _ => rfl)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]

/-! ### (K2) -/

variable (n : ℕ)

/-- The sum map on `Gbar n → ℤ` (auxiliary for (K2)). -/
def sumBar : (Gbar n → ℤ) →ₗ[ℤ] ℤ where
  toFun u := ∑ x, u x
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum]

/-- The sum map on `G n → ℤ` (auxiliary for (K2)). -/
def sumG : (G n → ℤ) →ₗ[ℤ] ℤ where
  toFun u := ∑ x, u x
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum]

/-- `push` preserves the sum (auxiliary for (K2)). -/
lemma sumBar_push (f : G n → ℤ) : sumBar n (push ℤ n f) = sumG n f := by
  classical
  show ∑ x, push ℤ n f x = ∑ g, f g
  have : ∀ x, push ℤ n f x = ∑ g ∈ univ.filter (fun g => mk n g = x), f g := fun x => by
    unfold push; simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [this]
  exact Finset.sum_fiberwise _ _ _

lemma sumBar_lapBar (u : Gbar n → ℤ) : sumBar n (lapBar ℤ n u) = 0 := K1 ℤ n u

lemma sumG_lap (h : G n → ℤ) : sumG n (lap ℤ n h) = 0 := by
  rw [← sumBar_push]
  have := LinearMap.congr_fun (push_lap ℤ n) h
  simp only [LinearMap.comp_apply] at this
  rw [this, sumBar_lapBar]

/-- The sum map on `cokerBar n` (auxiliary for (K2)). -/
def sBar : cokerBar n →ₗ[ℤ] ℤ :=
  (LinearMap.range (lapBar ℤ n)).liftQ (sumBar n) (by
    rintro _ ⟨u, rfl⟩; exact sumBar_lapBar n u)

/-- The sum map on `coker n` (auxiliary for (K2)). -/
def sG : coker n →ₗ[ℤ] ℤ :=
  (LinearMap.range (L n)).liftQ (sumG n) (by
    rintro _ ⟨u, rfl⟩; exact sumG_lap n u)

/-- The class of `δ_0` in `cokerBar n` (auxiliary for (K2)). -/
def zBar : cokerBar n := Submodule.Quotient.mk (Pi.single 0 1)

lemma sBar_zBar : sBar n (zBar n) = 1 := by
  classical
  show ∑ x, (Pi.single (0 : Gbar n) (1 : ℤ) : Gbar n → ℤ) x = 1
  simp

lemma sG_single : sG n (Submodule.Quotient.mk (Pi.single 0 1)) = 1 := by
  classical
  show ∑ x, (Pi.single (0 : G n) (1 : ℤ) : G n → ℤ) x = 1
  simp

/-- A `ℤ`-linear functional with a value `1` splits off a copy of `ℤ` (auxiliary for (K2)). -/
def splitEquiv {M : Type*} [AddCommGroup M] (s : M →ₗ[ℤ] ℤ) (z : M) (hz : s z = 1) :
    M ≃ₗ[ℤ] ℤ × LinearMap.ker s where
  toFun x := (s x, ⟨x - s x • z, by simp [hz]⟩)
  invFun p := p.1 • z + p.2
  map_add' x y := by
    ext <;> simp [add_smul]; abel
  map_smul' c x := by
    ext <;> simp [smul_sub, mul_smul]
  left_inv x := by simp
  right_inv p := by
    obtain ⟨a, k, hk⟩ := p
    rw [LinearMap.mem_ker] at hk
    ext <;> simp [hk, hz]

/-- In `M ≃ ℤ × T` with `T` finite, the kernel of a nonzero functional is killed by `|T|`
(auxiliary for (K2)). -/
lemma card_smul_eq_zero_of_ker {M T : Type*} [AddCommGroup M] [AddCommGroup T] [Finite T]
    (E : M ≃ₗ[ℤ] ℤ × T) (f : M →ₗ[ℤ] ℤ) {z : M} (hz : f z ≠ 0) {x : M} (hx : f x = 0) :
    (Nat.card T : ℤ) • x = 0 := by
  set N : ℤ := (Nat.card T : ℤ)
  have hN : N ≠ 0 := by have := Nat.card_pos (α := T); omega
  set y := E.symm (1, 0)
  have key : ∀ w : M, N • w = (N * (E w).1) • y := fun w => by
    apply E.injective
    rw [map_smul, map_smul]
    simp only [y, LinearEquiv.apply_symm_apply, Prod.smul_mk, smul_eq_mul, mul_one, smul_zero]
    refine Prod.ext rfl ?_
    show N • (E w).2 = 0
    rw [show N = ((Nat.card T : ℕ) : ℤ) from rfl, natCast_zsmul, card_nsmul_eq_zero']
  have hfz := congrArg f (key z)
  have hfx := congrArg f (key x)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hfz hfx
  rw [hx, mul_zero] at hfx
  have hy : f y ≠ 0 := fun h => by
    rw [h, mul_zero] at hfz; exact (mul_ne_zero hN hz) hfz
  have ha : (E x).1 = 0 := by
    rcases mul_eq_zero.1 hfx.symm with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h hN
      · exact h
    · exact absurd h hy
  rw [key x, ha, mul_zero, zero_smul]

/-- The kernel of the sum map on `cokerBar n` is torsion (auxiliary for (K2)). -/
lemma ker_sBar_torsion (y : LinearMap.ker (sBar n)) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y = 0 := by
  haveI := K_finite n
  obtain ⟨y, hy⟩ := y
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨f, rfl⟩ := push_surjective ℤ n u
  have hsum : sG n (Submodule.Quotient.mk f) = 0 := by
    rw [LinearMap.mem_ker] at hy
    have : sBar n (Submodule.Quotient.mk (push ℤ n f)) = sumBar n (push ℤ n f) := rfl
    rw [Submodule.mkQ_apply, this, sumBar_push] at hy
    exact hy
  have h1 := card_smul_eq_zero_of_ker (cokerEquivK n) (sG n)
    (z := Submodule.Quotient.mk (Pi.single 0 1)) (by rw [sG_single]; norm_num) hsum
  refine ⟨Nat.card (K n), by have := Nat.card_pos (α := K n); omega, ?_⟩
  apply Subtype.ext
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨h, hh⟩ := h1
  simp only [Submodule.coe_smul, Submodule.coe_zero, Submodule.mkQ_apply]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← map_zsmul, ← hh]
  refine ⟨push ℤ n h, ?_⟩
  rw [← LinearMap.comp_apply, ← push_lap, LinearMap.comp_apply]

instance ker_sBar_finite : Finite (LinearMap.ker (sBar n)) := by
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨m, hm, hy⟩ := ker_sBar_torsion n y
  exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, hy⟩

/-- `cokerBar n ≃ₗ[ℤ] ℤ × ker (sum)` (auxiliary for (K2)). -/
def cokerBarSplit : cokerBar n ≃ₗ[ℤ] ℤ × LinearMap.ker (sBar n) :=
  splitEquiv (sBar n) (zBar n) (sBar_zBar n)

/-- (K2), auxiliary: `KBar n ≃ₗ[ℤ] ker (sum)`. -/
def KBarEquivKer : KBar n ≃ₗ[ℤ] LinearMap.ker (sBar n) :=
  torsionEquivOfProd (cokerBarSplit n)

/-- **(K2)** of `C38b_the_folded_cube_and_proposition_103.md`, first part: `KBar n` is finite. -/
theorem KBar_finite : Finite (KBar n) :=
  Finite.of_equiv _ (KBarEquivKer n).symm.toEquiv

/-- **(K2)** of `C38b_the_folded_cube_and_proposition_103.md`, second part (explicit equivalence):
`cokerBar n ≃ₗ[ℤ] ℤ × KBar n`. -/
def cokerBarEquivKBar : cokerBar n ≃ₗ[ℤ] ℤ × KBar n :=
  (cokerBarSplit n).trans (LinearEquiv.prodCongr (LinearEquiv.refl ℤ ℤ) (KBarEquivKer n).symm)

/-- **(K2)** of `C38b_the_folded_cube_and_proposition_103.md`: for every `n`, `KBar n` is finite
and `cokerBar n ≃ₗ[ℤ] ℤ × KBar n`. -/
theorem K2 : Finite (KBar n) ∧ Nonempty (cokerBar n ≃ₗ[ℤ] ℤ × KBar n) :=
  ⟨KBar_finite n, ⟨cokerBarEquivKBar n⟩⟩

/-! ### (K3) -/

open TensorProduct

/-- `(Gbar n → ℤ) ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (Gbar n → ℤ_[2])`, as C17 `psi` (auxiliary for (K3)). -/
def psiBar : (Gbar n → ℤ) ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (Gbar n → ℤ_[2]) := by
  classical
  exact (TensorProduct.comm ℤ _ _).trans (TensorProduct.piScalarRight ℤ ℤ ℤ_[2] (Gbar n))

lemma psiBar_tmul (f : Gbar n → ℤ) (a : ℤ_[2]) : psiBar n (f ⊗ₜ a) = fun g => f g • a := by
  simp [psiBar]

lemma psiBar_comm :
    (psiBar n).toLinearMap ∘ₗ (lapBar ℤ n).rTensor ℤ_[2] =
      (lapBar ℤ_[2] n).restrictScalars ℤ ∘ₗ (psiBar n).toLinearMap := by
  refine TensorProduct.ext' fun f a => ?_
  funext g
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.rTensor_tmul, psiBar_tmul, LinearMap.coe_restrictScalars, lapBar_apply]
  simp only [zsmul_eq_mul, Finset.sum_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_sum, sub_mul, mul_assoc]

lemma range_tensor_eq_bar :
    (LinearMap.range (TensorProduct.map (LinearMap.range (lapBar ℤ n)).subtype
      (LinearMap.id : ℤ_[2] →ₗ[ℤ] ℤ_[2]))).map (psiBar n).toLinearMap =
      (LinearMap.range (lapBar ℤ_[2] n)).restrictScalars ℤ := by
  have h1 : LinearMap.range (TensorProduct.map (LinearMap.range (lapBar ℤ n)).subtype
      (LinearMap.id : ℤ_[2] →ₗ[ℤ] ℤ_[2])) = LinearMap.range ((lapBar ℤ n).rTensor ℤ_[2]) := by
    have hL : lapBar ℤ n = (LinearMap.range (lapBar ℤ n)).subtype ∘ₗ (lapBar ℤ n).rangeRestrict :=
      LinearMap.ext fun _ => rfl
    conv_rhs => rw [hL, LinearMap.rTensor_comp]
    rw [LinearMap.range_comp_of_range_eq_top]
    · rfl
    · exact LinearMap.range_eq_top.2
        (LinearMap.rTensor_surjective _ (LinearMap.surjective_rangeRestrict _))
  rw [h1, ← LinearMap.range_comp, psiBar_comm, LinearMap.range_comp_of_range_eq_top,
    LinearMap.range_restrictScalars]
  exact LinearMap.range_eq_top.2 (psiBar n).surjective

/-- Right exactness of `⊗_ℤ ℤ_[2]` for the folded cube (auxiliary for (K3)). -/
def cokerBarTensorEquiv :
    cokerBar n ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ]
      (Gbar n → ℤ_[2]) ⧸ (LinearMap.range (lapBar ℤ_[2] n)).restrictScalars ℤ :=
  (TensorProduct.quotientTensorEquiv ℤ_[2] (LinearMap.range (lapBar ℤ n))).trans
    (Submodule.Quotient.equiv _ _ (psiBar n) (range_tensor_eq_bar n))

/-- **(K3)** of `C38b_the_folded_cube_and_proposition_103.md`: for every `n`,
`(Gbar n → ℤ_[2]) ⧸ range (lapBar ℤ_[2] n) ≃+ ℤ_[2] × Syl2 (KBar n)`. -/
theorem K3 :
    Nonempty ((Gbar n → ℤ_[2]) ⧸ LinearMap.range (lapBar ℤ_[2] n) ≃+ ℤ_[2] × Syl2 (KBar n)) := by
  haveI := KBar_finite n
  obtain ⟨d1⟩ := D1 (KBar n)
  let e1 := (Submodule.Quotient.restrictScalarsEquiv ℤ (LinearMap.range (lapBar ℤ_[2] n))).symm
  let e2 := (cokerBarTensorEquiv n).symm
  let e3 : cokerBar n ⊗[ℤ] ℤ_[2] ≃ₗ[ℤ] (ℤ × KBar n) ⊗[ℤ] ℤ_[2] :=
    TensorProduct.congr (cokerBarEquivKBar n) (LinearEquiv.refl ℤ ℤ_[2])
  let e4 := TensorProduct.prodLeft ℤ ℤ ℤ (KBar n) ℤ_[2]
  let e5 : (ℤ ⊗[ℤ] ℤ_[2]) × (KBar n ⊗[ℤ] ℤ_[2]) ≃+ ℤ_[2] × Syl2 (KBar n) :=
    AddEquiv.prodCongr (TensorProduct.lid ℤ ℤ_[2]).toAddEquiv d1
  exact ⟨((((e1.trans e2).trans e3).trans e4).toAddEquiv).trans e5⟩

end FoldGroup
