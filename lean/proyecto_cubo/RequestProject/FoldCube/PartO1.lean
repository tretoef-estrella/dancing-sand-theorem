module

public import RequestProject.FoldCube.Aux

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: Part O — (O1) and (O2)

* (O1) `O1equiv`, `O1`: `((phi N).ι → A) ⧸ range (tauOp (phi N) (2d+1)) ≃ₗ[A]
  (N.ι → A) ⧸ range ((2 : A) • Gp N d)`, induced by `(y₀, y₁) ↦ y₀ − 2 Jop N d y₁`
  (`b₀ y₀ + b₁ y₁` is `bvec 0 y₀ + bvec 1 y₁`).
* (O2) `O2equiv`, `O2`: `twoM (L ⧸ range ((2 : A) • G)) ≃+ L ⧸ range G` for `L` without
  `2`-torsion (`O2equiv_symm_mk`: the class of `x` goes to `2 • [x]`), and `O2_pi`: over
  `[IsDomain A] [CharZero A]`, `L = ι → A` has no `2`-torsion.
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice Doubling Fold FoldHalf

variable {A : Type*} [CommRing A]

/-! ### (O2) -/

section O2

variable {L : Type*} [AddCommGroup L] [Module A L]

/-- the map `L ⧸ range G → L ⧸ range (2 G)`, `[x] ↦ [2 x]` (Part O2). -/
def dbl (G : Module.End A L) :
    (L ⧸ LinearMap.range G) →ₗ[A] L ⧸ LinearMap.range ((2 : A) • G) :=
  Submodule.mapQ _ _ ((2 : A) • LinearMap.id) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, by simp⟩)

lemma dbl_mk (G : Module.End A L) (x : L) :
    dbl G (Submodule.Quotient.mk x) = (2 : ℕ) • Submodule.Quotient.mk x := by
  rw [dbl, Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
    ← Submodule.Quotient.mk_smul]
  simp only [two_smul]

lemma dbl_eq (G : Module.End A L) (q : L ⧸ LinearMap.range G) :
    ∃ x : L, q = Submodule.Quotient.mk x ∧ dbl G q = (2 : ℕ) • Submodule.Quotient.mk x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact ⟨x, rfl, dbl_mk G x⟩

lemma dbl_mem (G : Module.End A L) (q : L ⧸ LinearMap.range G) :
    dbl G q ∈ FoldGroup.twoM (L ⧸ LinearMap.range ((2 : A) • G)) := by
  obtain ⟨x, -, hx⟩ := dbl_eq G q
  exact FoldGroup.mem_twoM.2 ⟨_, hx.symm⟩

/-- the corestriction of `dbl` to `twoM` (Part O2). -/
def dblR (G : Module.End A L) :
    (L ⧸ LinearMap.range G) →+ FoldGroup.twoM (L ⧸ LinearMap.range ((2 : A) • G)) :=
  AddMonoidHom.codRestrict (dbl G).toAddMonoidHom _ (dbl_mem G)

lemma dblR_bijective (h2 : ∀ x : L, (2 : ℕ) • x = 0 → x = 0) (G : Module.End A L) :
    Function.Bijective (dblR G) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨x, rfl, hx⟩ := dbl_eq G q
    have h0 : dbl G (Submodule.Quotient.mk x) = 0 := congrArg Subtype.val hq
    rw [dbl_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨y, hy⟩ := h0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨y, ?_⟩
    have : (2 : ℕ) • (x - G y) = 0 := by
      rw [smul_sub, ← hy, LinearMap.smul_apply, ofNat_smul_eq_nsmul (R := A), sub_self]
    exact (sub_eq_zero.1 (h2 _ this)).symm
  · rintro ⟨y, hy⟩
    obtain ⟨q', rfl⟩ := FoldGroup.mem_twoM.1 hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    exact ⟨Submodule.Quotient.mk x, Subtype.ext (dbl_mk G x)⟩

/-- **(O2)** of `C39b_the_cube_side_on_the_half_lattice.md` (halving): for an `A`-module `L` with
`∀ x : L, (2 : ℕ) • x = 0 → x = 0` and every `G : Module.End A L`, an additive equivalence
`FoldGroup.twoM (L ⧸ range ((2 : A) • G)) ≃+ L ⧸ range G` (its inverse sends the class of `x` to
`2 • [x]`, `O2equiv_symm_mk`). -/
def O2equiv (h2 : ∀ x : L, (2 : ℕ) • x = 0 → x = 0) (G : Module.End A L) :
    FoldGroup.twoM (L ⧸ LinearMap.range ((2 : A) • G)) ≃+ L ⧸ LinearMap.range G :=
  (AddEquiv.ofBijective (dblR G) (dblR_bijective h2 G)).symm

/-- (O2) the class of `x` goes to `2 • [x]`. -/
lemma O2equiv_symm_mk (h2 : ∀ x : L, (2 : ℕ) • x = 0 → x = 0) (G : Module.End A L) (x : L) :
    ((O2equiv h2 G).symm (Submodule.Quotient.mk x) : L ⧸ LinearMap.range ((2 : A) • G)) =
      (2 : ℕ) • Submodule.Quotient.mk x := by
  simp only [O2equiv, AddEquiv.symm_symm]
  exact dbl_mk G x

/-- **(O2)** of `C39b_the_cube_side_on_the_half_lattice.md` (halving): for an `A`-module `L` with
`∀ x : L, (2 : ℕ) • x = 0 → x = 0` and every `G : Module.End A L`,
`FoldGroup.twoM (L ⧸ range ((2 : A) • G)) ≃+ L ⧸ range G`, the class of `x` going to `2·[x]`. -/
theorem O2 (h2 : ∀ x : L, (2 : ℕ) • x = 0 → x = 0) (G : Module.End A L) :
    ∃ e : FoldGroup.twoM (L ⧸ LinearMap.range ((2 : A) • G)) ≃+ L ⧸ LinearMap.range G,
      ∀ x : L, ((e.symm (Submodule.Quotient.mk x)) : L ⧸ LinearMap.range ((2 : A) • G)) =
        (2 : ℕ) • Submodule.Quotient.mk x :=
  ⟨O2equiv h2 G, O2equiv_symm_mk h2 G⟩

end O2

/-- **(O2)** of `C39b_the_cube_side_on_the_half_lattice.md`, second sentence: over
`[IsDomain A] [CharZero A]`, `L = ι → A` satisfies `∀ x, (2 : ℕ) • x = 0 → x = 0`. -/
theorem O2_pi [IsDomain A] [CharZero A] (ι : Type*) :
    ∀ x : ι → A, (2 : ℕ) • x = 0 → x = 0 := by
  intro x hx
  funext i
  have := congrFun hx i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

/-! ### (O1) -/

lemma Jop_apply' (M : DPLattice A) (c : ℤ) (x : M.ι → A) : Jop M c x = (c : A) • x - H M x := rfl

section O1

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A)

lemma H_b1 (x : N.ι → A) : H (phi N) (b1 N x) = b1 N ((2 : A) • H N x - x) := by
  funext ⟨e, i⟩
  show ((2 * N.wt i + wtV e : ℤ) : A) * bvec 1 x (e, i) = bvec 1 ((2 : A) • H N x - x) (e, i)
  fin_cases e
  · simp
  · simp [Hop_apply]; ring

lemma tau_b0 (d : ℤ) (x : N.ι → A) :
    tauOp (phi N) (2 * d + 1) (b0 N x) = b0 N ((2 : A) • Jop N d x) + b1 N x := by
  rw [tauOp_phi_b0]
  congr 2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Jop_apply']
  push_cast
  module

lemma tau_b1 (d : ℤ) (x : N.ι → A) :
    tauOp (phi N) (2 * d + 1) (b1 N x) =
      b0 N ((2 : A) • N.Fd 1 x) + b1 N ((2 : A) • (Jop N d x + x)) := by
  rw [tauOp, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    H_b1]
  have hF : (phi N).Fd 1 (b1 N x) = b0 N ((2 : A) • N.Fd 1 x) := by
    rw [map_smul]; exact (B1 N).2.1 x
  rw [hF, Jop_apply', add_sub_assoc]
  congr 1
  rw [← map_smul, ← map_sub]
  congr 1
  push_cast
  module

/-- the map `b₀ y₀ + b₁ y₁ ↦ y₀ − 2 Jop N d y₁` (Part O1). -/
def piO1 (d : ℤ) : ((phi N).ι → A) →ₗ[A] (N.ι → A) :=
  s0 N - ((2 : A) • Jop N d) ∘ₗ s1 N

lemma piO1_b (d : ℤ) (y0 y1 : N.ι → A) :
    piO1 N d (b0 N y0 + b1 N y1) = y0 - (2 : A) • Jop N d y1 := by
  simp [piO1]

lemma piO1_tau (d : ℤ) (w : (phi N).ι → A) :
    piO1 N d (tauOp (phi N) (2 * d + 1) w) = ((2 : A) • Gp N d) (s1 N w) := by
  conv_lhs => rw [eq_b_s N w]
  rw [map_add, tau_b0, tau_b1, show ∀ p q r s : (phi N).ι → A, p + q + (r + s) = (p + r) + (q + s)
    from fun p q r s => by abel, ← map_add, ← map_add, piO1_b]
  simp only [Gp, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    Module.End.one_apply, map_add, map_smul]
  module

lemma piO1_ker (d : ℤ) :
    LinearMap.ker (piO1 N d) ≤ LinearMap.range (tauOp (phi N) (2 * d + 1)) := by
  intro w hw
  rw [LinearMap.mem_ker] at hw
  refine ⟨b0 N (s1 N w), ?_⟩
  have hw' : s0 N w = (2 : A) • Jop N d (s1 N w) := by
    rw [← sub_eq_zero, ← hw, piO1]; rfl
  rw [tau_b0, ← hw', ← eq_b_s N w]

/-- **(O1)** of `C39b_the_cube_side_on_the_half_lattice.md` (elimination of the `b₁` slot): for every
`N` and every `d : ℤ`, an explicit `A`-linear equivalence
`((Doubling.phi N).ι → A) ⧸ range (Fold.tauOp (Doubling.phi N) (2 * d + 1)) ≃ₗ[A]
(N.ι → A) ⧸ range ((2 : A) • Gp N d)`, induced by `bvec 0 y₀ + bvec 1 y₁ ↦ y₀ − 2 Jop N d y₁`. -/
def O1equiv (d : ℤ) :
    (((phi N).ι → A) ⧸ LinearMap.range (tauOp (phi N) (2 * d + 1))) ≃ₗ[A]
      (N.ι → A) ⧸ LinearMap.range ((2 : A) • Gp N d) :=
  quotEquivOfComap (piO1 N d) (fun y => ⟨b0 N y + b1 N 0, by rw [piO1_b]; simp⟩) _ _
    (comap_eq_of_map _ _ _
      (map_range_eq _ _ _ (s1 N) (fun y => ⟨b1 N y, s1_b1 N y⟩) (piO1_tau N d))
      (piO1_ker N d))

/-- **(O1)** of `C39b_the_cube_side_on_the_half_lattice.md`: for every `N`, every `d : ℤ`,
`((Doubling.phi N).ι → A) ⧸ range (Fold.tauOp (Doubling.phi N) (2 * d + 1)) ≃ₗ[A]
(N.ι → A) ⧸ range ((2 : A) • Gp N d)`. -/
theorem O1 (d : ℤ) :
    Nonempty ((((phi N).ι → A) ⧸ LinearMap.range (Fold.tauOp (phi N) (2 * d + 1))) ≃ₗ[A]
      (N.ι → A) ⧸ LinearMap.range ((2 : A) • Gp N d)) :=
  ⟨O1equiv N d⟩

end O1

end FoldCube
