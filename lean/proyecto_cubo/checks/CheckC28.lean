import RequestProject.Lift2.All

/-! Auditor's check file for Lean piece C28 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C28_lifting_mod_2_and_corollary_34.md`, with the hypotheses (H1), (H2),
(H3), the hypothesis of (C1), «weight-preserving» and «reduces to» written out entrywise instead
of the names `H1`, `H2`, `H3`, `OneAddTwoUnit`, `IsWtPres`, `bc`: (D1), (D2), (L2) with the lift
written out, (C1), (C3) with both maps and both compositions, (Z1); then `#print axioms`. -/

open DPLattice WeylFilt Doubling Twist LemmaW Cocycle Lift2

section hand
variable {A B : Type} [CommRing A] [CommRing B] {φ : A →+* B}

-- (D1): kernel 2A and no 2-torsion; unique half, weight-preserving if T is.
example (h2 : ∀ a, φ a = 0 ↔ ∃ b, a = 2 * b) (h3 : ∀ a : A, 2 * a = 0 → a = 0)
    {M N : DPLattice A} (T : Lin M N) (hT : bc φ T = 0) :
    (∃! U : Lin M N, T = (2 : A) • U) ∧
    ((∀ i j, M.wt i ≠ N.wt j → T (Pi.single i 1) j = 0) →
      ∀ U : Lin M N, T = (2 : A) • U → ∀ i j, M.wt i ≠ N.wt j → U (Pi.single i 1) j = 0) :=
  D1 h2 h3 T hT

-- (D2): no 2-torsion; 2 • c cocycle ⇒ c cocycle.
example (h3 : ∀ a : A, 2 * a = 0 → a = 0) {M N : DPLattice A} (c : Pair M N)
    (hc : IsCocycle ((2 : A) • c)) : IsCocycle c :=
  D2 h3 c hc

-- (L2) with the lift written out entrywise.
example (h1 : Function.Surjective φ) (h2 : ∀ a, φ a = 0 ↔ ∃ b, a = 2 * b)
    (h3 : ∀ a : A, 2 * a = 0 → a = 0) {M N : DPLattice A} (hM : HasDeltaFilt M)
    (hN : HasNablaFilt N) (hb : Hom (baseChange φ M) (baseChange φ N))
    (hhb : ∀ i j, M.wt i ≠ N.wt j → hb.toLin (Pi.single i 1) j = 0) :
    ∃ h : Hom M N, (∀ i j, M.wt i ≠ N.wt j → h.toLin (Pi.single i 1) j = 0) ∧
      (∀ i j, φ (h.toLin (Pi.single i 1) j) = hb.toLin (Pi.single i 1) j) ∧
      bcHom φ h = hb := by
  obtain ⟨h, hw, hbc, hH⟩ := L2 h1 h2 h3 hM hN hb hhb
  refine ⟨h, hw, fun i j => ?_, hH⟩
  rw [← bc_single_apply, hbc]; rfl

-- (C1): every 1 + 2a a unit ⇒ 1 + 2 • w bijective.
example (hU : ∀ a : A, IsUnit (1 + 2 * a)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u w : Module.End A (ι → A)) (huw : u = 1 + (2 : A) • w) : Function.Bijective u :=
  (C1 hU u w huw).2

-- (C3) Corollary 3.4, both maps and both compositions.
example (h1 : Function.Surjective φ) (h2 : ∀ a, φ a = 0 ↔ ∃ b, a = 2 * b)
    (h3 : ∀ a : A, 2 * a = 0 → a = 0) (hU : ∀ a : A, IsUnit (1 + 2 * a)) {X Y : DPLattice A}
    (hXD : HasDeltaFilt X) (hXN : HasNablaFilt X) (hYD : HasDeltaFilt Y)
    (hYN : HasNablaFilt Y) (eb : Iso (baseChange φ X) (baseChange φ Y))
    (hhom : ∀ i j, X.wt i ≠ Y.wt j → eb.hom.toLin (Pi.single i 1) j = 0)
    (hinv : ∀ i j, Y.wt i ≠ X.wt j → eb.inv.toLin (Pi.single i 1) j = 0) :
    ∃ f : Hom X Y, ∃ g : Hom Y X,
      g.toLin ∘ₗ f.toLin = LinearMap.id ∧ f.toLin ∘ₗ g.toLin = LinearMap.id ∧
      (∀ i j, X.wt i ≠ Y.wt j → f.toLin (Pi.single i 1) j = 0) ∧
      (∀ i j, Y.wt i ≠ X.wt j → g.toLin (Pi.single i 1) j = 0) ∧
      (∀ i j, φ (f.toLin (Pi.single i 1) j) = eb.hom.toLin (Pi.single i 1) j) ∧
      (∀ i j, φ (g.toLin (Pi.single i 1) j) = eb.inv.toLin (Pi.single i 1) j) := by
  obtain ⟨e, hw1, hw2, hb1, hb2⟩ := C3 h1 h2 h3 hU hXD hXN hYD hYN eb hhom hinv
  refine ⟨e.hom, e.inv, congrArg Hom.toLin e.hom_inv, congrArg Hom.toLin e.inv_hom, hw1, hw2,
    fun i j => ?_, fun i j => ?_⟩
  · rw [← bc_single_apply, hb1]; rfl
  · rw [← bc_single_apply, hb2]; rfl
end hand

-- (Z1) written out.
example : Function.Surjective (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) ∧
    (∀ a : ℤ_[2], PadicInt.toZMod a = 0 ↔ ∃ b, a = 2 * b) ∧
    (∀ a : ℤ_[2], 2 * a = 0 → a = 0) ∧ (∀ a : ℤ_[2], IsUnit (1 + 2 * a)) :=
  Z1

#print axioms Lift2.D1
#print axioms Lift2.D2
#print axioms Lift2.D3
#print axioms Lift2.L0
#print axioms Lift2.L1
#print axioms Lift2.L2
#print axioms Lift2.C1
#print axioms Lift2.C2
#print axioms Lift2.C3
#print axioms Lift2.Z1
#print axioms Lift2.Z2_L2
#print axioms Lift2.Z2_C3
