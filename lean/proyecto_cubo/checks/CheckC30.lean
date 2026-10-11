import RequestProject.Step36.All

/-! Auditor's check file for Lean piece C30 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C30_the_step_of_theorem_36.md`, with «weight-preserving» written out
entrywise instead of `IsWtPres`: (W1) on the lattices and on one explicit basis index (the weight
`wV a + wV b + 2 N.wt i + wV c` of the source written out); (W2); (A1) with both maps, the weight
conditions and both reductions written out; (K1); (K2) on basis vectors; (K3); (K4) the defining
equations and (a)–(e); (Z1); then `#print axioms`. -/

open DPLattice WeylFilt Doubling Twist Lemma35 Tensor2 Lemma35b LemmaW Cocycle Lift2 Step36

section hand
variable {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [CharZero A] [OddUnits A]
  (φ : A →+* B) (N : DPLattice A) (h2 : (2 : B) = 0)

-- (W1) entrywise.
example : ∀ i j, (baseChange φ (tensorV (tensorV (phi N)))).wt i ≠
      (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).wt j →
      (lemma35Iso φ h2 N).hom.toLin (Pi.single i 1) j = 0 :=
  W1 φ N h2

-- (W1) on one source index, the weight written out as in the file.
example (a b c : Fin 2) (i : N.ι)
    (j : (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).ι)
    (hj : wtV a + wtV b + 2 * N.wt i + wtV c ≠
      (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).wt j) :
    (lemma35Iso φ h2 N).hom.toLin (Pi.single (a, (b, (c, i))) 1) j = 0 := by
  apply W1 φ N h2
  have : (baseChange φ (tensorV (tensorV (phi N)))).wt (a, (b, (c, i))) =
      wtV a + wtV b + 2 * N.wt i + wtV c := by
    show wtV a + (wtV b + (2 * N.wt i + wtV c)) = _
    ring
  rw [this]; exact hj

-- (W2) entrywise.
example : ∀ i j, (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).wt i ≠
      (baseChange φ (tensorV (tensorV (phi N)))).wt j →
      (lemma35Iso φ h2 N).inv.toLin (Pi.single i 1) j = 0 :=
  W2 φ N h2

-- (A1) with both maps and both reductions, weights written out.
example (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) {N : DPLattice A}
    (hΔ : HasDeltaFilt N) (hN : HasNablaFilt N) :
    ∃ f : Hom (tensorV (tensorV (phi N))) (dsum (dsum (phi N) (phi N)) (phi (tensorV N))),
    ∃ g : Hom (dsum (dsum (phi N) (phi N)) (phi (tensorV N))) (tensorV (tensorV (phi N))),
      g.toLin ∘ₗ f.toLin = LinearMap.id ∧ f.toLin ∘ₗ g.toLin = LinearMap.id ∧
      (∀ i j, (tensorV (tensorV (phi N))).wt i ≠
        (dsum (dsum (phi N) (phi N)) (phi (tensorV N))).wt j → f.toLin (Pi.single i 1) j = 0) ∧
      (∀ i j, (dsum (dsum (phi N) (phi N)) (phi (tensorV N))).wt i ≠
        (tensorV (tensorV (phi N))).wt j → g.toLin (Pi.single i 1) j = 0) ∧
      bc φ f.toLin = (lemma35Iso φ h2 N).hom.toLin ∧
      bc φ g.toLin = (lemma35Iso φ h2 N).inv.toLin := by
  obtain ⟨e, hw1, hw2, hb1, hb2⟩ := A1 h1 hk h3 hU h2 hΔ hN
  exact ⟨e.hom, e.inv, congrArg Hom.toLin e.hom_inv, congrArg Hom.toLin e.inv_hom, hw1, hw2,
    hb1, hb2⟩

-- (K1).
example : Nonempty (Doubling.Iso (tensorV (one A)) (V A)) ∧
    Nonempty (Doubling.Iso (phi (one A)) (V A)) ∧
    Nonempty (Doubling.Iso (tensorV (one A)) (phi (one A))) := K1

-- (K2) on basis vectors, both directions.
example (M N : DPLattice A) (e : Fin 2) (i : M.ι) (j : N.ι) :
    (phiDsumIso M N).hom.toLin (Pi.single (e, Sum.inl i) 1) = Pi.single (Sum.inl (e, i)) 1 ∧
    (phiDsumIso M N).hom.toLin (Pi.single (e, Sum.inr j) 1) = Pi.single (Sum.inr (e, j)) 1 ∧
    (phiDsumIso M N).inv.toLin (Pi.single (Sum.inl (e, i)) 1) = Pi.single (e, Sum.inl i) 1 ∧
    (phiDsumIso M N).inv.toLin (Pi.single (Sum.inr (e, j)) 1) = Pi.single (e, Sum.inr j) 1 :=
  ⟨(K2 M N).2.2.1 e i, (K2 M N).2.2.2.1 e j, (K2 M N).2.2.2.2.1 e i, (K2 M N).2.2.2.2.2 e j⟩

-- (K3).
example (M : DPLattice A) : Nonempty (Doubling.Iso (dsum M (zeroL A)) M) ∧
    Nonempty (Doubling.Iso (dsum (zeroL A) M) M) ∧
    Nonempty (Doubling.Iso (tensorV (zeroL A)) (zeroL A)) ∧
    Nonempty (Doubling.Iso (phi (zeroL A)) (zeroL A)) := K3 M

-- (K4) the defining equations and (a)–(e).
example (X : DPLattice A) (L : List (DPLattice A)) :
    dsumList ([] : List (DPLattice A)) = zeroL A ∧ dsumList (X :: L) = dsum X (dsumList L) :=
  ⟨rfl, rfl⟩
example (L₁ L₂ L : List (DPLattice A)) (X : DPLattice A) :
    Nonempty (Doubling.Iso (dsumList (L₁ ++ L₂)) (dsum (dsumList L₁) (dsumList L₂))) ∧
    Nonempty (Doubling.Iso (tensorV (dsumList L)) (dsumList (L.map tensorV))) ∧
    Nonempty (Doubling.Iso (phi (dsumList L)) (dsumList (L.map phi))) ∧
    Nonempty (Doubling.Iso (dsumList [X]) X) :=
  ⟨K4a L₁ L₂, K4c L, K4d L, K4e X⟩
example {L L' : List (DPLattice A)} (hlen : L.length = L'.length)
    (h : ∀ k : Fin L.length, Nonempty (Doubling.Iso (L.get k) (L'.get (k.cast hlen)))) :
    Nonempty (Doubling.Iso (dsumList L) (dsumList L')) := K4b_get hlen h
end hand

-- (Z1) for ℤ_[2] → ZMod 2.
example (N : DPLattice ℤ_[2]) (hΔ : HasDeltaFilt N) (hN : HasNablaFilt N) :
    ∃ e : Doubling.Iso (tensorV (tensorV (phi N))) (dsum (dsum (phi N) (phi N)) (phi (tensorV N))),
      IsWtPres e.hom.toLin ∧ IsWtPres e.inv.toLin ∧
      bc PadicInt.toZMod e.hom.toLin =
        (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).hom.toLin ∧
      bc PadicInt.toZMod e.inv.toLin =
        (lemma35Iso PadicInt.toZMod Twist.C3_hyp.2.2.2.2.1 N).inv.toLin :=
  (Step36.Z1 N).2.2 hΔ hN

#print axioms Step36.himg_wt
#print axioms Step36.W1
#print axioms Step36.W2
#print axioms Step36.A1
#print axioms Step36.K1
#print axioms Step36.K2
#print axioms Step36.K3
#print axioms Step36.K4a
#print axioms Step36.K4b
#print axioms Step36.K4b_get
#print axioms Step36.K4c
#print axioms Step36.K4d
#print axioms Step36.K4e
#print axioms Step36.Z1
