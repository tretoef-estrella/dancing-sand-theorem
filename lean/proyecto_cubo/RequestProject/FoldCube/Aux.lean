module

public import RequestProject.FoldCube.Defs

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: auxiliary lemmas (used in Parts O and V)

* `quotEquivOfComap`: a surjection `π : W → W'` with `comap π S' = S` induces `W ⧸ S ≃ₗ W' ⧸ S'`;
  `comap_eq_of_map`: `comap π (range T') = range T` when `map π (range T) = range T'` and
  `ker π ≤ range T`.
* `dg a`: the diagonal operator `(dg a f) i = a i * f i`; `Fd_one_comp_dg`: `F ∘ dg a = dg b ∘ F`
  when `b k = a i` whenever `wt k = wt i − 2` (C18 (W) for `F = F^{(1)}`).
* `smul_two_cancel`: over `[IsDomain A] [CharZero A]`, `(2 : A) • T = (2 : A) • T'` forces `T = T'`
  for operators on `ι → A`.
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice

variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
  [Module R W']

/-- Auxiliary (Parts O, V): a surjection `π` with `comap π S' = S` induces `W ⧸ S ≃ₗ W' ⧸ S'`
(the class of `w` goes to the class of `π w`). -/
def quotEquivOfComap (π : W →ₗ[R] W') (hπ : Function.Surjective π) (S : Submodule R W)
    (S' : Submodule R W') (h : Submodule.comap π S' = S) : (W ⧸ S) ≃ₗ[R] W' ⧸ S' :=
  (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ, h])).trans
    ((S'.mkQ ∘ₗ π).quotKerEquivOfSurjective ((Submodule.mkQ_surjective _).comp hπ))

lemma comap_eq_of_map (π : W →ₗ[R] W') (T : Module.End R W) (T' : Module.End R W')
    (hmap : Submodule.map π (LinearMap.range T) = LinearMap.range T')
    (hker : LinearMap.ker π ≤ LinearMap.range T) :
    Submodule.comap π (LinearMap.range T') = LinearMap.range T := by
  rw [← hmap, Submodule.comap_map_eq, sup_eq_left.2 hker]

/-- Auxiliary: `map π (range T) = range T'` as soon as `π (T w) = T' (g w)` with `g` surjective. -/
lemma map_range_eq {V : Type*} [AddCommGroup V] [Module R V] (π : W →ₗ[R] W')
    (T : Module.End R W) (T' : V →ₗ[R] W') (g : W →ₗ[R] V) (hg : Function.Surjective g)
    (h : ∀ w, π (T w) = T' (g w)) :
    Submodule.map π (LinearMap.range T) = LinearMap.range T' := by
  ext v
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨g w, (h w).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := hg x
    exact ⟨T w, ⟨w, rfl⟩, h w⟩

variable {A : Type*} [CommRing A]

/-- Auxiliary: the diagonal operator `(dg a f) i = a i * f i`. -/
def dg {ι : Type*} (a : ι → A) : Module.End A (ι → A) where
  toFun f i := a i * f i
  map_add' f g := by funext i; simp [mul_add]
  map_smul' c f := by funext i; simp; ring

@[simp] lemma dg_apply {ι : Type*} (a : ι → A) (f : ι → A) (i : ι) : dg a f i = a i * f i := rfl

lemma dg_mul {ι : Type*} (a b : ι → A) : dg a * dg b = dg (a * b) := by
  apply LinearMap.ext; intro f; funext i; simp [mul_assoc]

lemma dg_one {ι : Type*} : dg (1 : ι → A) = 1 := by
  apply LinearMap.ext; intro f; funext i; simp

lemma dg_single {ι : Type*} [DecidableEq ι] (a : ι → A) (i : ι) :
    dg a (Pi.single i 1) = a i • (Pi.single i 1 : ι → A) := by
  funext k; by_cases h : k = i
  · subst h; simp
  · simp [h]

/-- Auxiliary: `F^{(1)} ∘ dg a = dg b ∘ F^{(1)}` when `b k = a i` whenever `wt k = wt i − 2`
(because `F` sends the coordinate of weight `w` to coordinates of weight `w − 2`). -/
lemma Fd_one_comp_dg (M : DPLattice A) (a b : M.ι → A)
    (h : ∀ i k, M.wt k = M.wt i - 2 → b k = a i) :
    M.Fd 1 * dg a = dg b * M.Fd 1 := by
  refine ext_single fun i => ?_
  funext k
  simp only [Module.End.mul_apply, dg_single, map_smul, dg_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : M.wt k = M.wt i - 2
  · rw [h i k hk]
  · rw [M.isDP.W_F i 1 k (by simpa using hk), mul_zero, mul_zero]

lemma smul_two_cancel [IsDomain A] [CharZero A] {V : Type*} {ι : Type*}
    [AddCommGroup V] [Module A V] {T T' : V →ₗ[A] (ι → A)} (h : (2 : A) • T = (2 : A) • T') :
    T = T' := by
  apply LinearMap.ext; intro f; funext i
  have := congrFun (LinearMap.congr_fun h f) i
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ two_ne_zero this

end FoldCube
