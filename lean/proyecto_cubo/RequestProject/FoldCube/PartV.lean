module

public import RequestProject.FoldCube.PartO3

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: Part V — the even families (Lemma 10.5(b))

* (V1) `V1equiv`, `V1`: `coker tauOp (tensorV M) (c + 1) ≃ₗ coker (tauOp M c * (tauOp M c + 2))`,
  induced by `bvec 0 y₀ + bvec 1 y₁ ↦ y₀ − tauOp M c y₁`.
* (V2) `V2`, `V2_phi`: `2 • thetaOp M c = tauOp M c * (tauOp M c + 2)` when every `c − wt` is even,
  and this holds for `Doubling.phi N` at `c = 2d + 1`.
* (V3) `V3a`, `V3b`, `V3c` (collected in `V3`): `θ` in the basis `β` of C39 (E4).
* (V4) `V4equiv`, `V4`: the circulant cokernel lemma.
* (V5) `V5`: Lemma 10.5(b), general form.
* (V6) `V6`: Lemma 10.5(b) over `ℤ_[2]`.
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice Doubling Fold FoldHalf

variable {A : Type*} [CommRing A]

lemma two_apply {V : Type*} [AddCommGroup V] [Module A V] (v : V) :
    (2 : Module.End A V) v = (2 : A) • v := by
  rw [show (2 : Module.End A V) = 1 + 1 from (one_add_one_eq_two).symm, LinearMap.add_apply,
    Module.End.one_apply, two_smul]

/-! ### (V1) -/

section V1

variable (M : DPLattice A) (c : ℤ)

/-- the map `bvec 0 y₀ + bvec 1 y₁ ↦ y₀ − tauOp M c y₁` (Part V1). -/
def piV1 : ((tensorV M).ι → A) →ₗ[A] (M.ι → A) := u0 M - tauOp M c ∘ₗ u1 M

lemma piV1_t (y0 y1 : M.ι → A) : piV1 M c (t0 M y0 + t1 M y1) = y0 - tauOp M c y1 := by
  simp [piV1]

lemma piV1_tau (w : (tensorV M).ι → A) :
    piV1 M c (tauOp (tensorV M) (c + 1) w) =
      (tauOp M c * (tauOp M c + 2)) (-u1 M w) := by
  conv_lhs => rw [eq_t_u M w]
  rw [map_add, tauOp_t0, tauOp_t1, add_assoc, ← map_add, piV1_t]
  simp only [Module.End.mul_apply, LinearMap.add_apply, two_apply, map_add, map_neg, map_smul]
  abel

lemma piV1_ker :
    LinearMap.ker (piV1 M c) ≤ LinearMap.range (tauOp (tensorV M) (c + 1)) := by
  intro w hw
  rw [LinearMap.mem_ker] at hw
  refine ⟨t0 M (u1 M w), ?_⟩
  have hw' : u0 M w = tauOp M c (u1 M w) := by
    rw [← sub_eq_zero, ← hw, piV1]; rfl
  rw [tauOp_t0, ← hw', ← eq_t_u M w]

/-- **(V1)** of `C39b_the_cube_side_on_the_half_lattice.md` (modulo `τ`, `g ≡ 1 + τ_M`): for every
DP-lattice `M` and every `c : ℤ`, an explicit `A`-linear equivalence
`((DPLattice.tensorV M).ι → A) ⧸ range (Fold.tauOp (DPLattice.tensorV M) (c + 1)) ≃ₗ[A]
(M.ι → A) ⧸ range (Fold.tauOp M c * (Fold.tauOp M c + 2))`, induced by
`bvec 0 y₀ + bvec 1 y₁ ↦ y₀ − tauOp M c y₁`. -/
def V1equiv :
    (((tensorV M).ι → A) ⧸ LinearMap.range (tauOp (tensorV M) (c + 1))) ≃ₗ[A]
      (M.ι → A) ⧸ LinearMap.range (tauOp M c * (tauOp M c + 2)) :=
  quotEquivOfComap (piV1 M c) (fun y => ⟨t0 M y + t1 M 0, by rw [piV1_t]; simp⟩) _ _
    (comap_eq_of_map _ _ _
      (map_range_eq _ _ _ (-u1 M) (fun y => ⟨t1 M (-y), by simp⟩) (piV1_tau M c))
      (piV1_ker M c))

/-- **(V1)** of `C39b_the_cube_side_on_the_half_lattice.md`: for every DP-lattice `M` and every
`c : ℤ`, `((DPLattice.tensorV M).ι → A) ⧸ range (Fold.tauOp (DPLattice.tensorV M) (c + 1)) ≃ₗ[A]
(M.ι → A) ⧸ range (Fold.tauOp M c * (Fold.tauOp M c + 2))`. -/
theorem V1 :
    Nonempty ((((DPLattice.tensorV M).ι → A) ⧸
        LinearMap.range (Fold.tauOp (DPLattice.tensorV M) (c + 1))) ≃ₗ[A]
      (M.ι → A) ⧸ LinearMap.range (Fold.tauOp M c * (Fold.tauOp M c + 2))) :=
  ⟨V1equiv M c⟩

end V1

/-! ### (V2) -/

section V2

variable (M : DPLattice A) (c : ℤ)

lemma Jop_eq_dg : Jop M c = dg (fun k => ((c - M.wt k : ℤ) : A)) := by
  apply LinearMap.ext; intro f; funext k
  simp [Jop, Hop_apply]; ring

lemma Jop_add_two_eq_dg : Jop M c + 2 = dg (fun k => ((c - M.wt k + 2 : ℤ) : A)) := by
  apply LinearMap.ext; intro f; funext k
  simp only [LinearMap.add_apply, two_apply, Jop_eq_dg, dg_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast; ring

lemma Jop_mul_Fd : Jop M c * M.Fd 1 = M.Fd 1 * (Jop M c + 2) := by
  rw [Jop_add_two_eq_dg, Fd_one_comp_dg M _ (fun k => ((c - M.wt k : ℤ) : A))
    (fun i k hk => by show ((c - M.wt k : ℤ) : A) = _; rw [hk]; push_cast; ring), Jop_eq_dg]

lemma Fd_mul_Fd : M.Fd 1 * M.Fd 1 = (2 : A) • M.Fd 2 := by
  have h := M.isDP.P1_F 1 1
  rw [choose_natAdd] at h
  rw [Module.End.mul_eq_comp, h]
  norm_num

lemma tauOp_eq_F_add_J : tauOp M c = M.Fd 1 + Jop M c := by
  rw [tauOp, Jop, add_sub_assoc]

/-- **(V2)** of `C39b_the_cube_side_on_the_half_lattice.md` (`θ = τ(τ + 2)/2`): if
`∀ i, Even (c − M.wt i)`, then `(2 : A) • thetaOp M c = Fold.tauOp M c * (Fold.tauOp M c + 2)`. -/
theorem V2 (hev : ∀ i, Even (c - M.wt i)) :
    (2 : A) • thetaOp M c = Fold.tauOp M c * (Fold.tauOp M c + 2) := by
  have hJJ : Jop M c * (Jop M c + 2) = (2 : A) • halfJJ M c := by
    rw [Jop_add_two_eq_dg, Jop_eq_dg, dg_mul]
    apply LinearMap.ext; intro f; funext k
    simp only [dg_apply, Pi.mul_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      halfJJ_apply]
    obtain ⟨r, hr⟩ := hev k
    have h2 : (2 : ℤ) ∣ (c - M.wt k) * (c - M.wt k + 2) :=
      Dvd.dvd.mul_right ⟨r, by rw [hr]; ring⟩ _
    set q := (c - M.wt k) * (c - M.wt k + 2) / 2 with hq
    have h3 : (c - M.wt k) * (c - M.wt k + 2) = 2 * q := (Int.mul_ediv_cancel' h2).symm
    have h4 : ((c - M.wt k : ℤ) : A) * ((c - M.wt k + 2 : ℤ) : A) = 2 * (q : A) := by
      have := congrArg (Int.cast : ℤ → A) h3
      rw [Int.cast_mul, Int.cast_mul, Int.cast_two] at this
      exact this
    linear_combination (f k) * h4
  have hexp : tauOp M c * (tauOp M c + 2) = M.Fd 1 * M.Fd 1 + M.Fd 1 * (Jop M c + 2) +
      Jop M c * M.Fd 1 + Jop M c * (Jop M c + 2) := by
    rw [tauOp_eq_F_add_J]; noncomm_ring
  rw [hexp, Jop_mul_Fd, hJJ, Fd_mul_Fd, thetaOp, smul_add, smul_add, two_smul A (M.Fd 1 * _)]
  abel

/-- **(V2)** of `C39b_the_cube_side_on_the_half_lattice.md`, second sentence: for
`M = Doubling.phi N` and `c = 2 * d + 1`, every `c − wt` is even, hence
`(2 : A) • thetaOp M c = Fold.tauOp M c * (Fold.tauOp M c + 2)`. -/
theorem V2_phi [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (d : ℤ) :
    (∀ i, Even (2 * d + 1 - (phi N).wt i)) ∧
    (2 : A) • thetaOp (phi N) (2 * d + 1) =
      Fold.tauOp (phi N) (2 * d + 1) * (Fold.tauOp (phi N) (2 * d + 1) + 2) := by
  have hev : ∀ i, Even (2 * d + 1 - (phi N).wt i) := by
    rintro ⟨e, i⟩
    show Even (2 * d + 1 - (2 * N.wt i + wtV e))
    fin_cases e
    · exact ⟨d - N.wt i, by simp only [Fin.zero_eta, wtV_zero]; ring⟩
    · exact ⟨d - N.wt i + 1, by simp only [Fin.mk_one, wtV_one]; ring⟩
  exact ⟨hev, V2 _ _ hev⟩

end V2

/-! ### (V4) -/

section V4

variable {L M' : Type*} [AddCommGroup L] [Module A L] [AddCommGroup M'] [Module A M']
  (β : (L × L) ≃ₗ[A] M') (w : Module.End A M') (X Y : Module.End A L)
  (hw : ∀ x y, w (β (x, y)) = β (X x + Y y, Y x + X y))

/-- the map `β (x, y) ↦ (y − x, x)` (Part V4). -/
def piV4 : M' →ₗ[A] (L × L) := (pi3 L).toLinearMap ∘ₗ β.symm.toLinearMap

include hw in
lemma piV4_w (m : M') : piV4 β (w m) = glueOp (X - Y) (X + Y) Y (piV4 β m) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := β.surjective m
  simp only [piV4, LinearMap.comp_apply, LinearEquiv.coe_coe, hw, LinearEquiv.symm_apply_apply,
    pi3_apply, glueOp_apply, LinearMap.sub_apply, LinearMap.add_apply, map_sub]
  ext <;> simp <;> abel

lemma piV4_surjective : Function.Surjective (piV4 β) :=
  ((pi3 L).surjective).comp β.symm.surjective

lemma piV4_injective : Function.Injective (piV4 β) :=
  ((pi3 L).injective).comp β.symm.injective

/-- **(V4)** of `C39b_the_cube_side_on_the_half_lattice.md` (circulant cokernels): for `A`-modules
`L`, `M'`, an equivalence `β : (L × L) ≃ₗ[A] M'`, `w : Module.End A M'` and `X, Y` with
`w (β (x, y)) = β (X x + Y y, Y x + X y)`, an explicit `A`-linear equivalence
`M' ⧸ range w ≃ₗ[A] (L × L) ⧸ range (FoldHalf.glueOp (X − Y) (X + Y) Y)` (the class of `β (x, y)`
goes to the class of `(y − x, x)`). -/
def V4equiv : (M' ⧸ LinearMap.range w) ≃ₗ[A]
    (L × L) ⧸ LinearMap.range (FoldHalf.glueOp (X - Y) (X + Y) Y) :=
  quotEquivOfComap (piV4 β) (piV4_surjective β) _ _
    (comap_eq_of_map _ _ _
      (map_range_eq _ _ _ (piV4 β) (piV4_surjective β) (piV4_w β w X Y hw))
      (by rw [LinearMap.ker_eq_bot.2 (piV4_injective β)]; exact bot_le))

include hw in
/-- **(V4)** of `C39b_the_cube_side_on_the_half_lattice.md` (circulant cokernels):
`M' ⧸ range w ≃ₗ[A] (L × L) ⧸ range (FoldHalf.glueOp (X − Y) (X + Y) Y)`. -/
theorem V4 : Nonempty ((M' ⧸ LinearMap.range w) ≃ₗ[A]
    (L × L) ⧸ LinearMap.range (FoldHalf.glueOp (X - Y) (X + Y) Y)) :=
  ⟨V4equiv β w X Y hw⟩

end V4

end FoldCube
