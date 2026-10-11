import RequestProject.LiftExt.All

/-! Auditor's check file for Lean piece C26 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C26_lifting_and_extension.md`, with the weight conditions written out
instead of the names `IsWtPres` and `WtIn`: (L1) with the lift given by `sW x`; (X1) with
`k' = k ∘ ρ`, `f ∘ ρ = id − sW x ∘ g`; (X1) for weights in `[−l−1, l+1]`; (B1) and (B2) for every
`l m`; (B4) over `ℤ_[2]` without weight hypotheses; (B5); then `#print axioms`. -/

open DPLattice WeylFilt Doubling LemmaW LiftExt

section hand
variable {A : Type} [CommRing A]

-- (L1) Lemma W, lifting form.
example (l : ℕ) {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (hfg : ShortExact f g)
    (hf : ∀ i j, N.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ Z.wt j → g.toLin (Pi.single i 1) j = 0)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l)
    (h : Hom (delta A l) Z) (hh : ∀ i j, (delta A l).wt i ≠ Z.wt j → h.toLin (Pi.single i 1) j = 0) :
    ∃ x : X.ι → A, (∀ i, X.wt i ≠ l → x i = 0) ∧
      ∃ h' : Hom (delta A l) X, (∀ r : Fin (l + 1), h'.toLin (Pi.single r 1) = X.Fd r x) ∧
        Hom.comp g h' = h := by
  obtain ⟨x, hx, -, h', hh', hc⟩ := L1 l hfg hf hg hN h hh
  refine ⟨x, fun i hi => ?_, h', fun r => by rw [hh']; exact sW_single x r, hc⟩
  have := congrFun hx i
  simpa [HasWt, pr_apply, hi] using this.symm

-- (X1) Lemma W, extension form, with k' = k ∘ ρ.
example (l : ℕ) {Y X K : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g)
    (hf : ∀ i j, Y.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ (delta A l).wt j → g.toLin (Pi.single i 1) j = 0)
    (hK : ∀ i, -(l : ℤ) ≤ K.wt i ∧ K.wt i ≤ l)
    (k : Hom Y K) (hk : ∀ i j, Y.wt i ≠ K.wt j → k.toLin (Pi.single i 1) j = 0) :
    ∃ k' : Hom X K, Hom.comp k' f = k ∧ ∃ x : X.ι → A, ∃ ρ : (X.ι → A) →ₗ[A] (Y.ι → A),
      f.toLin ∘ₗ ρ = LinearMap.id - sW x ∘ₗ g.toLin ∧ k'.toLin = k.toLin ∘ₗ ρ := by
  obtain ⟨k', hc, x, -, -, ρ, hρ, hk'⟩ := X1 l hfg hf hg hK k hk
  exact ⟨k', hc, x, ρ, hρ, hk'⟩

-- (X1), general form: K with weights in [−l−1, l+1].
example (l : ℕ) {Y X K : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin)
    (hK : ∀ i, -(l : ℤ) - 1 ≤ K.wt i ∧ K.wt i ≤ (l : ℤ) + 1)
    (k : Hom Y K) (hk : IsWtPres k.toLin) :
    ∃ k' : Hom X K, Hom.comp k' f = k := by
  obtain ⟨-, -, -, -, -, -, k', -, hc⟩ := X1_gen l hfg hf hg hK k hk
  exact ⟨k', hc⟩

-- (B1) lifting, every l m.
example (l m : ℕ) {X Z : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X Z}
    (hfg : ShortExact f g)
    (hf : ∀ i j, (nabla A m).wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ Z.wt j → g.toLin (Pi.single i 1) j = 0)
    (h : Hom (delta A l) Z) (hh : ∀ i j, (delta A l).wt i ≠ Z.wt j → h.toLin (Pi.single i 1) j = 0) :
    ∃ h' : Hom (delta A l) X, Hom.comp g h' = h := B1 l m hfg hf hg h hh

-- (B2) extension, every l m.
example (l m : ℕ) {Y X : DPLattice A} {f : Hom Y X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g)
    (hf : ∀ i j, Y.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ (delta A l).wt j → g.toLin (Pi.single i 1) j = 0)
    (k : Hom Y (nabla A m)) (hk : ∀ i j, Y.wt i ≠ (nabla A m).wt j → k.toLin (Pi.single i 1) j = 0) :
    ∃ k' : Hom X (nabla A m), Hom.comp k' f = k := B2 l m hfg hf hg k hk

-- (B5) consistency with C25 (E2).
example (l m : ℕ) {X : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X (delta A l)}
    (hfg : ShortExact f g) (hf : IsWtPres f.toLin) (hg : IsWtPres g.toLin) :
    (∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _) := B5 l m hfg hf hg
end hand

-- (B4) over ℤ_[2], no weight hypotheses.
example (l m : ℕ) {X Z : DPLattice ℤ_[2]} {f : Hom (nabla ℤ_[2] m) X} {g : Hom X Z}
    (hfg : ShortExact f g) (h : Hom (delta ℤ_[2] l) Z) :
    ∃ h' : Hom (delta ℤ_[2] l) X, Hom.comp g h' = h := (B4 l m).1 hfg h
example (l m : ℕ) {Y X : DPLattice ℤ_[2]} {f : Hom Y X} {g : Hom X (delta ℤ_[2] l)}
    (hfg : ShortExact f g) (k : Hom Y (nabla ℤ_[2] m)) :
    ∃ k' : Hom X (nabla ℤ_[2] m), Hom.comp k' f = k := (B4 l m).2 hfg k

#print axioms LiftExt.L0
#print axioms LiftExt.L1
#print axioms LiftExt.X1_gen
#print axioms LiftExt.X1
#print axioms LiftExt.B1
#print axioms LiftExt.B2
#print axioms LiftExt.B3
#print axioms LiftExt.B4
#print axioms LiftExt.B5
