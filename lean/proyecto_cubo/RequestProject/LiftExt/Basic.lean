module

public import RequestProject.LemmaW.All

/-!
# `C26_lifting_and_extension.md`: Setting and Part L — lifting along a surjection

Encodings (namespace `LiftExt`), reusing C18 (`DPLattice`: `DPLattice`, `IsDP`, `Hom`, `delta`,
`nabla`, `weylWt`, `deltaF`, `deltaE`), C19 (`WeylFilt`: `Hom.id`, `Hom.comp`, `Hom.ext'`,
`ShortExact`), C20 (`Doubling.Iso`) and C25 (`LemmaW`: `IsWtPres`, `pr`, `HasWt`, `trM`, `dual`,
`dualHom`, `isoDualDual`, `isoDualDelta`, `isoDualNabla`, `sW`, `sWHom'`, …):

* vectors of a DP-lattice `M` are functions `M.ι → A`; `δ_i = Pi.single i 1`; for `Δ_A(l)`,
  `δ_0 = e_0 = Pi.single (0 : Fin (l + 1)) 1`;
* a morphism is a C18 `Hom M N`, its underlying linear map `f.toLin`; composition `Hom.comp`
  (C19), identity `Hom.id` (C19);
* a short exact sequence `N —f→ X —g→ Z` is C19's `ShortExact f g`;
* "weight-preserving" is C25's `IsWtPres`, "`z` has weight `w`" is C25's `HasWt M w z`
  (`pr M w z = z`);
* "`K` has weights in `[a, b]`" is `WtIn K a b` : `∀ i, a ≤ K.wt i ∧ K.wt i ≤ b` (defined here);
* the lift of (L1) has underlying linear map C25's `sW x : δ_r ↦ F^{(r)} x`.
-/

@[expose] public section

noncomputable section

namespace LiftExt

open DPLattice WeylFilt Doubling LemmaW Finset

variable {A : Type*} [CommRing A]

/-! ### Setting -/

/-- Setting: the DP-lattice `K` *has weights in `[a, b]`*: `a ≤ K.wt i ≤ b` for every `i : K.ι`. -/
def WtIn (K : DPLattice A) (a b : ℤ) : Prop := ∀ i, a ≤ K.wt i ∧ K.wt i ≤ b

/-- Setting (auxiliary): `nabla A m` has weights in `[−m, m]`. -/
lemma wtIn_nabla (m : ℕ) : WtIn (nabla A m) (-(m : ℤ)) m := fun i => by
  change -(m : ℤ) ≤ weylWt m i ∧ weylWt m i ≤ m
  have := (i : Fin (m + 1)).isLt
  simp only [weylWt]; omega

/-- Setting (auxiliary): weights in `[a, b]` are weights in any larger interval. -/
lemma WtIn.mono {K : DPLattice A} {a b a' b' : ℤ} (h : WtIn K a b) (ha : a' ≤ a) (hb : b ≤ b') :
    WtIn K a' b' := fun i => ⟨le_trans ha (h i).1, le_trans (h i).2 hb⟩

/-- Setting (auxiliary): a vector of weight `w` in a lattice with no basis index of weight `w`
vanishes. -/
lemma eq_zero_of_hasWt {M : DPLattice A} {w : ℤ} {v : M.ι → A} (hv : HasWt M w v)
    (hw : ∀ i, M.wt i ≠ w) : v = 0 := by
  rw [← hv, pr_eq_zero_of_noWt M w hw, LinearMap.zero_apply]

/-- Setting (auxiliary): a weight-preserving map sends vectors of weight `w` to vectors of
weight `w`. -/
lemma hasWt_map {M N : DPLattice A} {φ : (M.ι → A) →ₗ[A] (N.ι → A)} (hφ : IsWtPres φ) {w : ℤ}
    {v : M.ι → A} (hv : HasWt M w v) : HasWt N w (φ v) := by
  unfold HasWt
  rw [← LinearMap.comp_apply, ← P2_wtPres hφ, LinearMap.comp_apply, hv]

/-- Setting (auxiliary): `F^{(r)}` sends weight `w` to weight `w − 2r`. -/
lemma hasWt_Fd (M : DPLattice A) {w : ℤ} {v : M.ι → A} (hv : HasWt M w v) (r : ℕ) :
    HasWt M (w - 2 * r) (M.Fd r v) := by
  unfold HasWt
  rw [← LinearMap.comp_apply, ← P2_F, LinearMap.comp_apply, hv]

/-- Setting (auxiliary): `E^{(s)}` sends weight `w` to weight `w + 2s`. -/
lemma hasWt_Ed (M : DPLattice A) {w : ℤ} {v : M.ι → A} (hv : HasWt M w v) (s : ℕ) :
    HasWt M (w + 2 * s) (M.Ed s v) := by
  unfold HasWt
  rw [← LinearMap.comp_apply, ← P2_E, LinearMap.comp_apply, hv]

/-- Setting (auxiliary): the identity morphism is weight-preserving. -/
lemma isWtPres_id (M : DPLattice A) : IsWtPres (Hom.id M).toLin := by
  intro i j hij
  change (Pi.single i (1 : A) : M.ι → A) j = 0
  have : j ≠ i := fun h => hij (h ▸ rfl)
  simp [this]

/-! ### Computations on `Δ_A(l)` at `e_0` -/

/-- (C18, auxiliary) `e_0` has weight `l` in `Δ_A(l)`. -/
lemma hasWt_delta_zero (l : ℕ) :
    HasWt (delta A l) l (Pi.single (0 : Fin (l + 1)) 1) := prW_delta_single_zero l

/-- (C18, auxiliary) `E^{(s)} e_0 = 0` for `s ≥ 1`. -/
lemma deltaE_single_zero_eq (l s : ℕ) (hs : 1 ≤ s) :
    deltaE (A := A) l s (Pi.single (0 : Fin (l + 1)) 1) = 0 := by
  funext m
  rw [deltaE_single_apply, if_neg (by simp; omega)]
  rfl

/-- (C18, auxiliary) `F^{(r)} e_0 = 0` for `r > l`. -/
lemma deltaF_single_zero_eq (l r : ℕ) (hr : l < r) :
    deltaF (A := A) l r (Pi.single (0 : Fin (l + 1)) 1) = 0 := by
  funext m
  have := m.isLt
  rw [deltaF_single_apply, if_neg (by simp; omega)]
  rfl

/-! ### Part L -/

/-- (L0) If `f : Hom N X` is injective with `f.toLin` weight-preserving, and `f.toLin n` has
weight `w`, then `n` has weight `w`. -/
theorem L0 {N X : DPLattice A} (f : Hom N X) (hinj : Function.Injective f.toLin)
    (hf : IsWtPres f.toLin) {w : ℤ} {n : N.ι → A} (hn : HasWt X w (f.toLin n)) :
    HasWt N w n := by
  apply hinj
  unfold HasWt at hn
  rw [← hn, ← LinearMap.comp_apply, P2_wtPres hf, LinearMap.comp_apply]

/-- (L0, consequence; auxiliary) In a short exact sequence `N —f→ X —g→ Z` with `f.toLin`
weight-preserving, a vector `v` of weight `w` with `g v = 0` is `f y` for some `y` of weight
`w`. -/
lemma exists_preimage_hasWt {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) {w : ℤ} {v : X.ι → A} (hv : HasWt X w v)
    (hgv : g.toLin v = 0) : ∃ y, f.toLin y = v ∧ HasWt N w y := by
  have hmem : v ∈ LinearMap.range f.toLin := by rw [hfg.exact]; exact hgv
  obtain ⟨y, rfl⟩ := hmem
  exact ⟨y, rfl, L0 f hfg.inj hf hv⟩

/-- (L1, auxiliary) In a short exact sequence `N —f→ X —g→ Z` with `f.toLin`
weight-preserving, a vector of weight `w` killed by `g` vanishes when `N` has no weight `w`. -/
lemma eq_zero_of_ker {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) {w : ℤ} {v : X.ι → A} (hv : HasWt X w v)
    (hgv : g.toLin v = 0) (hw : ∀ i, N.wt i ≠ w) : v = 0 := by
  obtain ⟨y, rfl, hy⟩ := exists_preimage_hasWt hfg hf hv hgv
  rw [eq_zero_of_hasWt hy hw, map_zero]

/-- (L1) **Lemma W, lifting form.** Let `f : Hom N X`, `g : Hom X Z` be short exact with
`f.toLin`, `g.toLin` weight-preserving, and let `N` have weights in `[−l, l]`. Then for every
`h : Hom (delta A l) Z` with `h.toLin` weight-preserving there is `x : X.ι → A` of weight `l` with
`g.toLin x = h.toLin δ_0`, and a morphism `h' : Hom (delta A l) X` with underlying map `sW x`
and `Hom.comp g h' = h`. -/
theorem L1 (l : ℕ) {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (hfg : ShortExact f g)
    (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) (hN : WtIn N (-(l : ℤ)) l)
    (h : Hom (delta A l) Z) (hh : IsWtPres h.toLin) :
    ∃ x : X.ι → A, HasWt X l x ∧ g.toLin x = h.toLin (Pi.single (0 : Fin (l + 1)) 1) ∧
      ∃ h' : Hom (delta A l) X, h'.toLin = sW x ∧ Hom.comp g h' = h := by
  set z := h.toLin (Pi.single (0 : Fin (l + 1)) 1) with hz
  have hzw : HasWt Z l z := hasWt_map hh (hasWt_delta_zero l)
  obtain ⟨y, hy⟩ := hfg.surj z
  set x := pr X l y with hxdef
  have hx : HasWt X l x := hasWt_pr X l y
  have hgx : g.toLin x = z := by
    rw [hxdef, ← LinearMap.comp_apply, P2_wtPres hg, LinearMap.comp_apply, hy, hzw]
  have hgE : ∀ s, g.toLin (X.Ed s x) = h.toLin (deltaE l s (Pi.single 0 1)) := fun s => by
    rw [← LinearMap.comp_apply, g.comm_E, LinearMap.comp_apply, hgx, hz,
      ← LinearMap.comp_apply, ← h.comm_E]; rfl
  have hgF : ∀ r, g.toLin (X.Fd r x) = h.toLin (deltaF l r (Pi.single 0 1)) := fun r => by
    rw [← LinearMap.comp_apply, g.comm_F, LinearMap.comp_apply, hgx, hz,
      ← LinearMap.comp_apply, ← h.comm_F]; rfl
  have hE : ∀ s : ℕ, 1 ≤ s → X.Ed s x = 0 := fun s hs =>
    eq_zero_of_ker hfg hf (hasWt_Ed X hx s)
      (by rw [hgE, deltaE_single_zero_eq l s hs, map_zero])
      (fun i => by have := hN i; omega)
  have hF : ∀ r : ℕ, l < r → X.Fd r x = 0 := fun r hr =>
    eq_zero_of_ker hfg hf (hasWt_Fd X hx r)
      (by rw [hgF, deltaF_single_zero_eq l r hr, map_zero])
      (fun i => by have := hN i; omega)
  refine ⟨x, hx, hgx, sWHom' x hx hE hF, rfl, Hom.ext' ?_⟩
  refine ext_single fun r => ?_
  change g.toLin (sW x (Pi.single r 1)) = h.toLin (Pi.single r 1)
  rw [sW_single, hgF, deltaF_single_zero]

/-- (L1, remark) C25 (W4) is the case `Z = delta A l`, `h = Hom.id` of (L1). -/
theorem L1_W4 (l : ℕ) {N X : DPLattice A} {f : Hom N X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hN : WtIn N (-(l : ℤ)) l) :
    ∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id (delta A l) := by
  obtain ⟨-, -, -, h', -, hh'⟩ := L1 l hfg hf hg hN (Hom.id _) (isWtPres_id _)
  exact ⟨h', hh'⟩

end LiftExt
