import RequestProject.Cocycle.All

/-! Auditor's check file for Lean piece C27 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C27_cocycles_and_filtrations.md`, with the conditions written out instead
of the names `IsWtPres`, `IsCoboundary`, `CocycleEqs`: (G2) the cocycle equations (W) and (K)
at a basis vector, both directions; (G5) coboundary ⇔ section of `proj`, with the section
`v ↦ (ψ v, v)`; (G7) with `θ x = (ρ x, g x)` and `θ⁻¹ (u, v) = f u + σ v`; (V4) both forms;
(V6) over `ℤ_[2]` with no weight hypotheses; then `#print axioms`. -/

open DPLattice WeylFilt Doubling LemmaW Cocycle Finset

section hand
variable {A : Type} [CommRing A] {M N : DPLattice A}

-- (G2), (W) and (K) from a cocycle.
example (c : Pair M N) (hc : IsCocycle c) :
    (∀ (i : M.ι) (r : ℕ) (j : N.ι), N.wt j ≠ M.wt i - 2 * r → c.1 r (Pi.single i 1) j = 0) ∧
    (∀ (i : M.ι) (r : ℕ) (j : N.ι), N.wt j ≠ M.wt i + 2 * r → c.2 r (Pi.single i 1) j = 0) ∧
    c.1 0 = 0 ∧ c.2 0 = 0 ∧
    (∀ (i : M.ι) (r s : ℕ), N.Ed s (c.1 r (Pi.single i 1)) + c.2 s (M.Fd r (Pi.single i 1)) =
      ∑ j ∈ range (min r s + 1), ((Ring.choose (M.wt i + s - r) j : ℤ) : A) •
        (N.Fd (r - j) (c.2 (s - j) (Pi.single i 1)) +
          c.1 (r - j) (M.Ed (s - j) (Pi.single i 1)))) := by
  have h := (G2 c).mp hc
  exact ⟨h.W_F, h.W_E, h.P0_F, h.P0_E, h.K⟩

-- (G2), converse: the equations written out give a cocycle.
example (c : Pair M N)
    (hWF : ∀ (i : M.ι) (r : ℕ) (j : N.ι), N.wt j ≠ M.wt i - 2 * r → c.1 r (Pi.single i 1) j = 0)
    (hWE : ∀ (i : M.ι) (r : ℕ) (j : N.ι), N.wt j ≠ M.wt i + 2 * r → c.2 r (Pi.single i 1) j = 0)
    (h0F : c.1 0 = 0) (h0E : c.2 0 = 0)
    (h1F : ∀ a b : ℕ, N.Fd a ∘ₗ c.1 b + c.1 a ∘ₗ M.Fd b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • c.1 (a + b))
    (h1E : ∀ a b : ℕ, N.Ed a ∘ₗ c.2 b + c.2 a ∘ₗ M.Ed b =
      ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • c.2 (a + b))
    (hK : ∀ (i : M.ι) (r s : ℕ), N.Ed s (c.1 r (Pi.single i 1)) + c.2 s (M.Fd r (Pi.single i 1)) =
      ∑ j ∈ range (min r s + 1), ((Ring.choose (M.wt i + s - r) j : ℤ) : A) •
        (N.Fd (r - j) (c.2 (s - j) (Pi.single i 1)) +
          c.1 (r - j) (M.Ed (s - j) (Pi.single i 1)))) :
    IsCocycle c :=
  (G2 c).mpr ⟨hWF, hWE, h0F, h0E, h1F, h1E, hK⟩

-- (G4) the coboundary of ψ, written out.
example (ψ : Lin M N) (r : ℕ) :
    (d ψ).1 r = ψ ∘ₗ M.Fd r - N.Fd r ∘ₗ ψ ∧ (d ψ).2 r = ψ ∘ₗ M.Ed r - N.Ed r ∘ₗ ψ := ⟨rfl, rfl⟩

-- (G5) (i) ⇒ (ii) with the explicit section v ↦ (ψ v, v); (ii) ⇒ (i) with a weight-preserving ψ.
example (c : Pair M N) (hc : IsCocycle c)
    (ψ : Lin M N) (hψ : ∀ i j, M.wt i ≠ N.wt j → ψ (Pi.single i 1) j = 0) (hd : d ψ = c) :
    ∃ s : Hom M (glue M N c hc), Hom.comp (proj M N c hc) s = Hom.id M := by
  exact ((G5 c hc).1).mp ⟨ψ, hψ, hd⟩
example (c : Pair M N) (hc : IsCocycle c)
    (s : Hom M (glue M N c hc)) (hs : Hom.comp (proj M N c hc) s = Hom.id M) :
    ∃ ψ : Lin M N, (∀ i j, M.wt i ≠ N.wt j → ψ (Pi.single i 1) j = 0) ∧ d ψ = c :=
  ((G5 c hc).1).mpr ⟨s, hs⟩
example (c : Pair M N) (hc : IsCocycle c) :
    (∃ s : Hom M (glue M N c hc), Hom.comp (proj M N c hc) s = Hom.id M) ↔
      ∃ r : Hom (glue M N c hc) N, Hom.comp r (incl M N c hc) = Hom.id N :=
  (G5 c hc).2

-- (G7) every extension is glued, with θ explicit.
example {X : DPLattice A} {f : Hom N X} {g : Hom X M} (h : ShortExact f g)
    (hf : ∀ i j, N.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ M.wt j → g.toLin (Pi.single i 1) j = 0) :
    ∃ (σ : Lin M X) (ρ : Lin X N), g.toLin ∘ₗ σ = LinearMap.id ∧
      ρ ∘ₗ f.toLin = LinearMap.id ∧ f.toLin ∘ₗ ρ = LinearMap.id - σ ∘ₗ g.toLin ∧
      ∃ (hc : IsCocycle ((fun r => ρ ∘ₗ X.Fd r ∘ₗ σ, fun r => ρ ∘ₗ X.Ed r ∘ₗ σ) : Pair M N))
        (θ : Iso X (glue M N _ hc)),
        (∀ x, θ.hom.toLin x = Sum.elim (ρ x) (g.toLin x)) ∧
        (∀ u v, θ.inv.toLin (Sum.elim u v) = f.toLin u + σ v) ∧
        Hom.comp θ.hom f = incl M N _ hc ∧ Hom.comp (proj M N _ hc) θ.hom = g := by
  obtain ⟨σ, ρ, -, -, h1, h2, h3, hc, θ, h4, h5, h6, h7⟩ := G7 h hf hg
  exact ⟨σ, ρ, h1, h2, h3, hc, θ, h4, h5, h6, h7⟩

-- (V4) both forms.
example (hM : HasDeltaFilt M) (hN : HasNablaFilt N) (c : Pair M N) (hc : IsCocycle c) :
    ∃ ψ : Lin M N, (∀ i j, M.wt i ≠ N.wt j → ψ (Pi.single i 1) j = 0) ∧ d ψ = c :=
  (V4 hM hN).1 c hc
example (hM : HasDeltaFilt M) (hN : HasNablaFilt N) {X : DPLattice A} {f : Hom N X}
    {g : Hom X M} (h : ShortExact f g)
    (hf : ∀ i j, N.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ M.wt j → g.toLin (Pi.single i 1) j = 0) :
    (∃ s : Hom M X, Hom.comp g s = Hom.id M) ∧ (∃ r : Hom X N, Hom.comp r f = Hom.id N) :=
  (V4 hM hN).2 h hf hg

-- (F2) the filtrations of Δ(l) and ∇(m).
example (l m : ℕ) : HasDeltaFilt (delta A l) ∧ HasNablaFilt (nabla A m) := F2 l m
end hand

-- (V6) over ℤ_[2], no weight hypotheses.
example {M N : DPLattice ℤ_[2]} (hM : HasDeltaFilt M) (hN : HasNablaFilt N)
    {X : DPLattice ℤ_[2]} {f : Hom N X} {g : Hom X M} (h : ShortExact f g) :
    (∃ s : Hom M X, Hom.comp g s = Hom.id M) ∧ (∃ r : Hom X N, Hom.comp r f = Hom.id N) :=
  (V6 hM hN).2 h

#print axioms Cocycle.G2
#print axioms Cocycle.G3
#print axioms Cocycle.G4
#print axioms Cocycle.G5
#print axioms Cocycle.G6a
#print axioms Cocycle.G6b
#print axioms Cocycle.G6c
#print axioms Cocycle.G7
#print axioms Cocycle.G7_split
#print axioms Cocycle.F2
#print axioms Cocycle.V1
#print axioms Cocycle.V2
#print axioms Cocycle.V3
#print axioms Cocycle.V4
#print axioms Cocycle.V5
#print axioms Cocycle.V6
