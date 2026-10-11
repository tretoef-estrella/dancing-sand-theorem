import RequestProject.LemmaW.All

/-! Auditor's check file for Lean piece C25 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C25_lemma_W_and_ext.md`, with the weight condition written out instead of
the name `IsWtPres`: (P1) over a domain of characteristic zero; (P3); (D1) the dual on basis
vectors (`F^{(r)}` of the dual is the transpose of `E^{(r)}`, and conversely); (D3), (D4) with the
identity maps; (D4) equal operators; (D5); (W3) the explicit section `δ_r ↦ F^{(r)} x`; (W4)
Lemma 3.2; (E1); (E2) both forms for all `l m`; (E3); (E4) over `ℤ_[2]`; then `#print axioms`. -/

open DPLattice WeylFilt Doubling LemmaW

section hand
variable {A : Type} [CommRing A]

-- (P1): every morphism over a domain of characteristic zero kills off-weight entries.
example [IsDomain A] [CharZero A] {M N : DPLattice A} (f : Hom M N) :
    ∀ i j, M.wt i ≠ N.wt j → f.toLin (Pi.single i 1) j = 0 := P1 f

-- (P3): the weights of an extension.
example {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (h : ShortExact f g)
    (hf : ∀ i j, N.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ Z.wt j → g.toLin (Pi.single i 1) j = 0)
    (w : ℤ) (hN : ∀ i, N.wt i ≠ w) (hZ : ∀ k, Z.wt k ≠ w) (y : X.ι → A) (j : X.ι)
    (hj : X.wt j = w) : y j = 0 := by
  have := congrArg (fun z => z j) (LinearMap.congr_fun (P3 h hf hg w hN hZ) y)
  simpa [pr_apply, hj] using this

-- (D1): same basis and weights; the dual operators are the transposes, on basis vectors.
example (M : DPLattice A) (r : ℕ) (i j : M.ι) :
    (dual M).wt i = M.wt i ∧
    (dual M).Fd r (Pi.single i 1) j = M.Ed r (Pi.single j 1) i ∧
    (dual M).Ed r (Pi.single i 1) j = M.Fd r (Pi.single j 1) i :=
  ⟨rfl, (D1 M).2.2.2.2.2.1 r i j, (D1 M).2.2.2.2.2.2 r i j⟩

-- (D2): the dual of a morphism has the transposed matrix.
example {M N : DPLattice A} (f : Hom M N) (i : M.ι) (j : N.ι) :
    (dualHom f).toLin (Pi.single j 1) i = f.toLin (Pi.single i 1) j := by
  rw [(D2 (A := A)).1 f]; exact trM_single_apply _ _ _

-- (D3): dual (dual M) ≅ M by the identity.
example (M : DPLattice A) :
    (isoDualDual M).hom.toLin = LinearMap.id ∧ (isoDualDual M).inv.toLin = LinearMap.id :=
  ⟨rfl, rfl⟩

-- (D4): equal operators, and isomorphisms by the identity.
example (l r : ℕ) : (dual (delta A l)).Fd r = (nabla A l).Fd r ∧
    (dual (delta A l)).Ed r = (nabla A l).Ed r ∧
    (dual (nabla A l)).Fd r = (delta A l).Fd r ∧
    (dual (nabla A l)).Ed r = (delta A l).Ed r :=
  ⟨(D4_delta l).2.2.2.1 r, (D4_delta l).2.2.2.2 r, (D4_nabla l).2.2.2.1 r, (D4_nabla l).2.2.2.2 r⟩
example (l : ℕ) : (isoDualDelta (A := A) l).hom.toLin = LinearMap.id ∧
    (isoDualNabla (A := A) l).hom.toLin = LinearMap.id := ⟨rfl, rfl⟩

-- (D5): the dual of a short exact sequence is short exact.
example {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (h : ShortExact f g) :
    ShortExact (dualHom g) (dualHom f) := D5 h

-- (W3): the section sends δ_r to F^{(r)} x.
example {X : DPLattice A} {l : ℕ} (x : X.ι → A) (r : Fin (l + 1)) :
    sW (l := l) x (Pi.single r 1) = X.Fd r x := sW_single x r

-- (W4) Lemma 3.2.
example {l : ℕ} {N X : DPLattice A} {f : Hom N X} {g : Hom X (delta A l)} (h : ShortExact f g)
    (hf : ∀ i j, N.wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ (delta A l).wt j → g.toLin (Pi.single i 1) j = 0)
    (hN : ∀ i, -(l : ℤ) ≤ N.wt i ∧ N.wt i ≤ l) :
    ∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id (delta A l) := W4 h hf hg hN

-- (E1).
example {N X Z : DPLattice A} {f : Hom N X} {g : Hom X Z} (h : ShortExact f g) :
    (∃ s : Hom Z X, Hom.comp g s = Hom.id Z) ↔ (∃ r : Hom X N, Hom.comp r f = Hom.id N) := E1 h

-- (E2) Lemma 3.3 first sentence, every l m.
example (l m : ℕ) {X : DPLattice A} {f : Hom (nabla A m) X} {g : Hom X (delta A l)}
    (h : ShortExact f g)
    (hf : ∀ i j, (nabla A m).wt i ≠ X.wt j → f.toLin (Pi.single i 1) j = 0)
    (hg : ∀ i j, X.wt i ≠ (delta A l).wt j → g.toLin (Pi.single i 1) j = 0) :
    (∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _) := E2 l m h hf hg

-- (E3).
example [IsDomain A] [CharZero A] (l m : ℕ) {X : DPLattice A} {f : Hom (nabla A m) X}
    {g : Hom X (delta A l)} (h : ShortExact f g) :
    (∃ s : Hom (delta A l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla A m), Hom.comp r f = Hom.id _) := E3 l m h
end hand

-- (E4) over ℤ_[2].
example (l m : ℕ) {X : DPLattice ℤ_[2]} {f : Hom (nabla ℤ_[2] m) X}
    {g : Hom X (delta ℤ_[2] l)} (h : ShortExact f g) :
    (∃ s : Hom (delta ℤ_[2] l) X, Hom.comp g s = Hom.id _) ∧
    (∃ r : Hom X (nabla ℤ_[2] m), Hom.comp r f = Hom.id _) := E4 l m h

#print axioms LemmaW.P1
#print axioms LemmaW.P2
#print axioms LemmaW.P3
#print axioms LemmaW.D1
#print axioms LemmaW.D2
#print axioms LemmaW.D3
#print axioms LemmaW.D4
#print axioms LemmaW.D4_delta
#print axioms LemmaW.D4_nabla
#print axioms LemmaW.D5
#print axioms LemmaW.W1
#print axioms LemmaW.W2
#print axioms LemmaW.W3
#print axioms LemmaW.W4
#print axioms LemmaW.W5
#print axioms LemmaW.E1
#print axioms LemmaW.E2
#print axioms LemmaW.E3
#print axioms LemmaW.E4
