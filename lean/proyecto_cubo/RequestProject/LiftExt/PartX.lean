module

public import RequestProject.LiftExt.Basic

/-!
# `C26_lifting_and_extension.md`: Part X — extending along an injection

Encodings (namespace `LiftExt`), as in `Basic.lean`:

* the extension is a short exact sequence `Y —f→ X —g→ Δ_A(l)` (C19's `ShortExact f g`), with
  `f.toLin`, `g.toLin` weight-preserving (C25's `IsWtPres`);
* `x : X.ι → A` is a vector of weight `l` with `g x = δ_0` (C25 (W1)), and `sW x` is C25's linear
  map `δ_r ↦ F^{(r)} x`;
* `ρ : (X.ι → A) →ₗ[A] (Y.ι → A)` is the linear map with `f ∘ ρ = id − sW x ∘ g` (and
  `ρ ∘ f = id`), given by C25's `exists_retraction_of_section`; the extension is
  `k' := k ∘ ρ`.

We prove (X1) in the more general form where `K` has weights in `[−l − 1, l + 1]` (`X1_gen`),
as allowed by the file, and deduce the stated form (`X1`).
-/

@[expose] public section

noncomputable section

namespace LiftExt

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

/-- (X1, auxiliary) a vector of weight `w` (as an `InWt` vector) is an eigenvector of `H`. -/
lemma Hop_of_hasWt {M : DPLattice A} {w : ℤ} {v : M.ι → A} (hv : HasWt M w v) :
    Hop M.wt v = ((w : ℤ) : A) • v := by
  have hv' := (hasWt_iff_inWt M w v).mp hv
  funext i
  rw [Hop_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : M.wt i = w
  · rw [hi]
  · rw [hv' i hi, mul_zero, mul_zero]

/-- (X1) **Lemma W, extension form**, general version with `K` of weights in
`[−l − 1, l + 1]`. Let `f : Hom Y X`, `g : Hom X (delta A l)` be short exact with `f.toLin`,
`g.toLin` weight-preserving, and let `K` have weights in `[−l − 1, l + 1]`. Let
`k : Hom Y K` with `k.toLin` weight-preserving. Then there are `x` of weight `l` with
`g x = δ_0`, a linear map `ρ` with `f ∘ ρ = id − sW x ∘ g` and `ρ ∘ f = id`, and a morphism
`k' : Hom X K` with underlying map `k ∘ ρ` and `Hom.comp k' f = k`. -/
theorem X1_gen (l : ℕ) {Y X K : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hK : WtIn K (-(l : ℤ) - 1) ((l : ℤ) + 1)) (k : Hom Y K) (hk : IsWtPres k.toLin) :
    ∃ x : X.ι → A, HasWt X l x ∧ g.toLin x = Pi.single (0 : Fin (l + 1)) 1 ∧
    ∃ ρ : (X.ι → A) →ₗ[A] (Y.ι → A),
      f.toLin ∘ₗ ρ = LinearMap.id - sW x ∘ₗ g.toLin ∧ ρ ∘ₗ f.toLin = LinearMap.id ∧
    ∃ k' : Hom X K, k'.toLin = k.toLin ∘ₗ ρ ∧ Hom.comp k' f = k := by
  obtain ⟨x, hx, hgx⟩ := W1 hfg hg
  have hxw : InWt X.wt l x := (hasWt_iff_inWt X l x).mp hx
  have hgs : g.toLin ∘ₗ sW x = LinearMap.id := by
    refine ext_single fun r => ?_
    rw [LinearMap.comp_apply, sW_single, ← LinearMap.comp_apply, g.comm_F, LinearMap.comp_apply,
      hgx]
    exact deltaF_single_zero l r
  obtain ⟨ρ, hρf, hfρ⟩ :=
    exists_retraction_of_section f.toLin g.toLin hfg.inj hfg.exact (sW x) hgs
  have hfρ' : ∀ v, f.toLin (ρ v) = v - sW x (g.toLin v) := fun v => by
    have := LinearMap.congr_fun hfρ v
    simpa using this
  have hρf' : ∀ y, ρ (f.toLin y) = y := fun y => LinearMap.congr_fun hρf y
  have hρs : ∀ z : Fin (l + 1) → A, ρ (sW x z) = 0 := by
    intro z
    apply hfg.inj
    rw [hfρ', ← LinearMap.comp_apply g.toLin (sW x), hgs, map_zero]
    exact sub_self _
  -- `g` on `E^{(s)} x` and `F^{(r)} x`
  have hgE : ∀ s, 1 ≤ s → g.toLin (X.Ed s x) = 0 := fun s hs => by
    rw [← LinearMap.comp_apply, g.comm_E, LinearMap.comp_apply, hgx]
    exact deltaE_single_zero_eq l s hs
  have hgF : ∀ r, l < r → g.toLin (X.Fd r x) = 0 := fun r hr => by
    rw [← LinearMap.comp_apply, g.comm_F, LinearMap.comp_apply, hgx]
    exact deltaF_single_zero_eq l r hr
  -- `k ∘ ρ` kills `F^{(r)} x` for `r ≤ l`
  have kill_F : ∀ r : ℕ, r ≤ l → k.toLin (ρ (X.Fd r x)) = 0 := by
    intro r hr
    have h1 := sW_single (l := l) x ⟨r, by omega⟩
    simp only at h1
    rw [← h1, hρs, map_zero]
  -- vectors killed by `g`, of a weight absent from `K`, come from vectors killed by `k`
  have kill_wt : ∀ (w : ℤ) (v : X.ι → A), HasWt X w v → g.toLin v = 0 →
      (∀ i, K.wt i ≠ w) → ∃ y, f.toLin y = v ∧ k.toLin y = 0 := by
    intro w v hv hgv hw
    obtain ⟨y, rfl, hy⟩ := exists_preimage_hasWt hfg hf hv hgv
    exact ⟨y, rfl, eq_zero_of_hasWt (hasWt_map hk hy) hw⟩
  -- two maps agreeing on `range f` and on the `F^{(r)} x` agree
  have ext_split : ∀ L1 L2 : (X.ι → A) →ₗ[A] (K.ι → A), L1 ∘ₗ f.toLin = L2 ∘ₗ f.toLin →
      (∀ r : Fin (l + 1), L1 (X.Fd r x) = L2 (X.Fd r x)) → L1 = L2 := by
    intro L1 L2 h1 h2
    have hs : L1 ∘ₗ sW x = L2 ∘ₗ sW x :=
      ext_single fun r => by simp only [LinearMap.comp_apply, sW_single]; exact h2 r
    refine LinearMap.ext fun v => ?_
    have hv : v = f.toLin (ρ v) + sW x (g.toLin v) := by rw [hfρ']; abel
    rw [hv, map_add, map_add]
    congr 1
    · exact LinearMap.congr_fun h1 (ρ v)
    · exact LinearMap.congr_fun hs (g.toLin v)
  -- the general commutation criterion
  have comm_gen : ∀ (TY : Module.End A (Y.ι → A)) (TX : Module.End A (X.ι → A))
      (TK : Module.End A (K.ι → A)),
      f.toLin ∘ₗ TY = TX ∘ₗ f.toLin → k.toLin ∘ₗ TY = TK ∘ₗ k.toLin →
      (∀ r : ℕ, r ≤ l → k.toLin (ρ (TX (X.Fd r x))) = 0) →
      (k.toLin ∘ₗ ρ) ∘ₗ TX = TK ∘ₗ (k.toLin ∘ₗ ρ) := by
    intro TY TX TK hfT hkT hker
    apply ext_split
    · refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.comp_apply TX, ← hfT, LinearMap.comp_apply, hρf', hρf',
        ← LinearMap.comp_apply k.toLin, hkT, LinearMap.comp_apply]
    · intro r
      have hr := r.isLt
      simp only [LinearMap.comp_apply]
      rw [hker r (by omega), kill_F r (by omega), map_zero]
  -- the three commutations
  have hFcomm : ∀ t, (k.toLin ∘ₗ ρ) ∘ₗ X.Fd t = K.Fd t ∘ₗ (k.toLin ∘ₗ ρ) := by
    intro t
    refine comm_gen _ _ _ (f.comm_F t) (k.comm_F t) fun r hr => ?_
    have hP := LinearMap.congr_fun (X.isDP.P1_F t r) x
    rw [LinearMap.comp_apply] at hP
    rw [hP, LinearMap.smul_apply, map_smul, map_smul]
    by_cases htr : t + r ≤ l
    · rw [kill_F _ htr, smul_zero]
    · obtain ⟨y, hy, hky⟩ := kill_wt _ _ (hasWt_Fd X hx (t + r)) (hgF _ (by omega))
        (fun i => by have := hK i; push_cast; omega)
      rw [← hy, hρf', hky, smul_zero]
  have hEcomm : ∀ s, (k.toLin ∘ₗ ρ) ∘ₗ X.Ed s = K.Ed s ∘ₗ (k.toLin ∘ₗ ρ) := by
    intro s
    refine comm_gen _ _ _ (f.comm_E s) (k.comm_E s) fun r hr => ?_
    rw [K_vec X hxw r s, map_sum, map_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    simp only [mem_range] at hj
    rw [map_smul, map_smul]
    by_cases hjs : s - j = 0
    · rw [hjs, X.isDP.P0_E, Module.End.one_apply, kill_F _ (by omega), smul_zero]
    · obtain ⟨y, hy, hky⟩ := kill_wt _ _ (hasWt_Ed X hx (s - j)) (hgE _ (by omega))
        (fun i => by have := hK i; omega)
      rw [← hy, ← LinearMap.comp_apply (X.Fd (r - j)), ← f.comm_F, LinearMap.comp_apply, hρf',
        ← LinearMap.comp_apply k.toLin, k.comm_F, LinearMap.comp_apply, hky, map_zero,
        smul_zero]
  have hHcomm : (k.toLin ∘ₗ ρ) ∘ₗ H X = H K ∘ₗ (k.toLin ∘ₗ ρ) := by
    refine comm_gen _ _ _ f.comm_H k.comm_H fun r hr => ?_
    rw [Hop_of_hasWt (hasWt_Fd X hx r), map_smul, map_smul, kill_F r hr, smul_zero]
  refine ⟨x, hx, hgx, ρ, hfρ, hρf, ⟨k.toLin ∘ₗ ρ, hFcomm, hEcomm, hHcomm⟩, rfl, Hom.ext' ?_⟩
  change (k.toLin ∘ₗ ρ) ∘ₗ f.toLin = k.toLin
  rw [LinearMap.comp_assoc, hρf, LinearMap.comp_id]

/-- (X1) **Lemma W, extension form.** Let `f : Hom Y X`, `g : Hom X (delta A l)` be short exact
with `f.toLin`, `g.toLin` weight-preserving, and let `K` be a DP-lattice with weights in
`[−l, l]`. Then for every `k : Hom Y K` with `k.toLin` weight-preserving there is
`k' : Hom X K` with `Hom.comp k' f = k`. Moreover `k'` has underlying map `k ∘ ρ`, where
`x` has weight `l`, `g x = δ_0`, and `ρ` is the linear map with `f ∘ ρ = id − sW x ∘ g`.
(Special case of `X1_gen`.) -/
theorem X1 (l : ℕ) {Y X K : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hK : WtIn K (-(l : ℤ)) l) (k : Hom Y K) (hk : IsWtPres k.toLin) :
    ∃ k' : Hom X K, Hom.comp k' f = k ∧
    ∃ x : X.ι → A, HasWt X l x ∧ g.toLin x = Pi.single (0 : Fin (l + 1)) 1 ∧
    ∃ ρ : (X.ι → A) →ₗ[A] (Y.ι → A),
      f.toLin ∘ₗ ρ = LinearMap.id - sW x ∘ₗ g.toLin ∧ k'.toLin = k.toLin ∘ₗ ρ := by
  obtain ⟨x, hx, hgx, ρ, hfρ, -, k', hk', hcomp⟩ :=
    X1_gen l hfg hf hg (hK.mono (by omega) (by omega)) k hk
  exact ⟨k', hcomp, x, hx, hgx, ρ, hfρ, hk'⟩

end LiftExt
