module

public import Mathlib

/-!
# `C39_the_fold_on_the_half_lattice.md`: a quotient lemma (auxiliary, used in Part A)

If `π : W → W'` is surjective, intertwines `T` with `T'`, kills `K`, and its kernel lies in
`range T ⊔ K`, then `W ⧸ (range T ⊔ K) ≃ W' ⧸ range T'` (`quotEquivOfIntertwine`).
-/

@[expose] public section

noncomputable section

namespace FoldHalf

variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W']
  [Module R W']

lemma comap_range_eq (π : W →ₗ[R] W') (hπ : Function.Surjective π) (T : Module.End R W)
    (T' : Module.End R W') (K : Submodule R W) (hT : π ∘ₗ T = T' ∘ₗ π)
    (hK : K ≤ LinearMap.ker π) (hker : LinearMap.ker π ≤ LinearMap.range T ⊔ K) :
    Submodule.comap π (LinearMap.range T') = LinearMap.range T ⊔ K := by
  have hT' : ∀ z, π (T z) = T' (π z) := fun z => LinearMap.congr_fun hT z
  ext w
  simp only [Submodule.mem_comap, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hπ y
    have hmem : w - T z ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, hT', hy, sub_self]
    have := hker hmem
    have h2 : T z ∈ LinearMap.range T ⊔ K := Submodule.mem_sup_left ⟨z, rfl⟩
    simpa using Submodule.add_mem _ this h2
  · intro hw
    obtain ⟨t, ⟨z, rfl⟩, k, hk, rfl⟩ := Submodule.mem_sup.1 hw
    refine ⟨π z, ?_⟩
    rw [map_add, hT', LinearMap.mem_ker.1 (hK hk), add_zero]

/-- Part A (auxiliary): `W ⧸ (range T ⊔ K) ≃ₗ W' ⧸ range T'` for a surjection `π` with
`π ∘ T = T' ∘ π`, `K ≤ ker π ≤ range T ⊔ K`; it sends the class of `w` to the class of `π w`. -/
def quotEquivOfIntertwine (π : W →ₗ[R] W') (hπ : Function.Surjective π) (T : Module.End R W)
    (T' : Module.End R W') (K : Submodule R W) (hT : π ∘ₗ T = T' ∘ₗ π)
    (hK : K ≤ LinearMap.ker π) (hker : LinearMap.ker π ≤ LinearMap.range T ⊔ K) :
    (W ⧸ (LinearMap.range T ⊔ K)) ≃ₗ[R] W' ⧸ LinearMap.range T' :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, comap_range_eq π hπ T T' K hT hK hker])).trans
    (((LinearMap.range T').mkQ ∘ₗ π).quotKerEquivOfSurjective
      ((Submodule.mkQ_surjective _).comp hπ))

end FoldHalf
