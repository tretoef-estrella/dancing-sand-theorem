import RequestProject.Lemma35b.PartL

/-! Auditor's check file for Lean piece C24 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C24_lemma_35_second_sentence.md`: (I1)–(I3) with their maps on basis
vectors; (B1), (B2), (F1), (F2) with both underlying maps the identity; (B3), (F3); (L4) with the
image of `δ_{inl r}`, `δ_{inr (inl e)}`, `δ_{inr (inr e)}` written out by hand and `uL(e_r)` read
from C22; (L5) as a `Nonempty Iso` between the types written by hand (order
`Φ(N)^2 ⊕ Φ(V ⊗ N)`), and the explicit formula of `lemma35Iso` with the images written out by
hand; (L6) with `PadicInt.toZMod`; then `#print axioms`. -/

open Finset DPLattice WeylFilt Doubling Lemma35 Tensor2 Twist Lemma35b

section I
variable {A : Type} [CommRing A]

-- (I1)
example (M : DPLattice A) : (Lemma35b.Iso.refl M).hom.toLin = LinearMap.id ∧
    (Lemma35b.Iso.refl M).inv.toLin = LinearMap.id := ⟨rfl, rfl⟩
example {M N P : DPLattice A} (u : Doubling.Iso M N) (v : Doubling.Iso N P) :
    (u.trans v).hom.toLin = v.hom.toLin ∘ₗ u.hom.toLin ∧
    (u.trans v).inv.toLin = u.inv.toLin ∘ₗ v.inv.toLin := ⟨rfl, rfl⟩
example {M N : DPLattice A} (u : Doubling.Iso M N) :
    u.symm.hom.toLin = u.inv.toLin ∧ u.symm.inv.toLin = u.hom.toLin := ⟨rfl, rfl⟩

-- (I2) on basis vectors, both ways
example (M N : DPLattice A) (i : M.ι) :
    (dsumComm M N).hom.toLin (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inr i) 1 :=
  (I2 M N).2.2.1 i
example (M N : DPLattice A) (j : N.ι) :
    (dsumComm M N).hom.toLin (Pi.single (Sum.inr j) 1) = Pi.single (Sum.inl j) 1 :=
  (I2 M N).2.2.2.1 j
example (M N : DPLattice A) (i : M.ι) :
    (dsumComm M N).inv.toLin (Pi.single (Sum.inr i) 1) = Pi.single (Sum.inl i) 1 :=
  (I2 M N).2.2.2.2.1 i

-- (I3) on basis vectors
example (M N P : DPLattice A) (i : M.ι) :
    (dsumAssoc M N P).hom.toLin (Pi.single (Sum.inl (Sum.inl i)) 1) = Pi.single (Sum.inl i) 1 :=
  (I3 M N P).2.2.1 i
example (M N P : DPLattice A) (j : N.ι) :
    (dsumAssoc M N P).hom.toLin (Pi.single (Sum.inl (Sum.inr j)) 1) =
      Pi.single (Sum.inr (Sum.inl j)) 1 := (I3 M N P).2.2.2.1 j
example (M N P : DPLattice A) (k : P.ι) :
    (dsumAssoc M N P).hom.toLin (Pi.single (Sum.inr k) 1) = Pi.single (Sum.inr (Sum.inr k)) 1 :=
  (I3 M N P).2.2.2.2.1 k
end I

section BF
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)

-- (B1): same operators, identity both ways
example (M N : DPLattice A) (r : ℕ) :
    (baseChange φ (tensor M N)).Fd r = (tensor (baseChange φ M) (baseChange φ N)).Fd r :=
  (B1 φ M N).2.2.2.1 r
example (M N : DPLattice A) :
    (bcTensorIso φ M N).hom.toLin = (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] _) ∧
    (bcTensorIso φ M N).inv.toLin = (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] _) := ⟨rfl, rfl⟩
-- (B2)
example (M N : DPLattice A) :
    (bcDsumIso φ M N).hom.toLin = (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] _) ∧
    (bcDsumIso φ M N).inv.toLin = (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] _) := ⟨rfl, rfl⟩
-- (B3)
example {M N : DPLattice A} (u : Doubling.Iso M N) :
    (bcIso φ u).hom = bcHom φ u.hom ∧ (bcIso φ u).inv = bcHom φ u.inv := ⟨rfl, rfl⟩

variable (h2 : (2 : B) = 0)
-- (F1)
example (M N : DPLattice B) (r : ℕ) :
    (frob h2 (tensor M N)).Fd r = (tensor (frob h2 M) (frob h2 N)).Fd r := (F1 h2 M N).2.1 r
example (M N : DPLattice B) :
    (frobTensorIso h2 M N).hom.toLin = (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] _) ∧
    (frobTensorIso h2 M N).inv.toLin = (LinearMap.id : (M.ι × N.ι → B) →ₗ[B] _) := ⟨rfl, rfl⟩
-- (F2)
example (M N : DPLattice B) (r : ℕ) :
    (frob h2 (dsum M N)).Ed r = (dsum (frob h2 M) (frob h2 N)).Ed r := (F2 h2 M N).2.2.1 r
example (M N : DPLattice B) :
    (frobDsumIso h2 M N).hom.toLin = (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] _) ∧
    (frobDsumIso h2 M N).inv.toLin = (LinearMap.id : (M.ι ⊕ N.ι → B) →ₗ[B] _) := ⟨rfl, rfl⟩
-- (F3)
example {M N : DPLattice B} (u : Doubling.Iso M N) :
    (frobIso h2 u).hom.toLin = u.hom.toLin ∧ (frobIso h2 u).inv.toLin = u.inv.toLin :=
  ⟨rfl, rfl⟩
end BF

section L
variable {B : Type} [CommRing B] (h2 : (2 : B) = 0)

-- C22's uL on e_r, read entry by entry: e_0 ↦ b_0b'_0, e_1 ↦ b_1b'_0, e_2 ↦ b_0b'_1, e_3 ↦ b_1b'_1
example : uL (Pi.single (0 : Fin 4) 1 : Fin 4 → B) = Pi.single ((0, 0) : Fin 2 × Fin 2) 1 :=
  uL_single 0
example : uL (Pi.single (1 : Fin 4) 1 : Fin 4 → B) = Pi.single ((1, 0) : Fin 2 × Fin 2) 1 :=
  uL_single 1
example : uL (Pi.single (2 : Fin 4) 1 : Fin 4 → B) = Pi.single ((0, 1) : Fin 2 × Fin 2) 1 :=
  uL_single 2
example : uL (Pi.single (3 : Fin 4) 1 : Fin 4 → B) = Pi.single ((1, 1) : Fin 2 × Fin 2) 1 :=
  uL_single 3

-- (L4): the isomorphism, between the types of the file
example (X : DPLattice B) : Doubling.Iso (tensorV (tensorV (tensorV X)))
    (dsum (tensor (tensorV (frob h2 (V B))) X) (dsum (tensorV X) (tensorV X))) := isoL4 h2 X
-- (L4): the images of δ_q with x attached, written out by hand
example (X : DPLattice B) (x : X.ι) (r : Fin 4) :
    L4img h2 X x (Sum.inl r) = Pi.single (Sum.inl (uIdx r, x)) 1 := rfl
example (X : DPLattice B) (x : X.ι) (e : Fin 2) :
    L4img h2 X x (Sum.inr (Sum.inl e)) = Pi.single (Sum.inr (Sum.inl (e, x))) 1 := rfl
example (X : DPLattice B) (x : X.ι) (e : Fin 2) :
    L4img h2 X x (Sum.inr (Sum.inr e)) = Pi.single (Sum.inr (Sum.inr (e, x))) 1 := rfl
-- (L4): the formula on basis vectors
example (X : DPLattice B) (a b c : Fin 2) (x : X.ι) :
    (isoL4 h2 X).hom.toLin (Pi.single (a, (b, (c, x))) 1) =
      ∑ q : Fin 4 ⊕ (Fin 2 ⊕ Fin 2), hL (Pi.single (a, (b, c)) 1 : Fin 2 × (Fin 2 × Fin 2) → B) q •
        L4img h2 X x q := L4 h2 X a b c x
end L

section L5
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (h2 : (2 : B) = 0)
  [IsDomain A] [CharZero A] [OddUnits A]

-- (L5): Lemma 3.5, second sentence; the target in the order Φ(N)^2 ⊕ Φ(V ⊗ N)
example (N : DPLattice A) : Nonempty (Doubling.Iso (baseChange φ (tensorV (tensorV (phi N))))
    (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N))))) := L5 φ h2 N
-- (L5): the images, written out by hand
example (N : DPLattice A) (i : N.ι) (r : Fin 4) :
    L5img φ N i (Sum.inl r) = Pi.single (Sum.inr ((uIdx r).1, ((uIdx r).2, i))) 1 := rfl
example (N : DPLattice A) (i : N.ι) (e : Fin 2) :
    L5img φ N i (Sum.inr (Sum.inl e)) = Pi.single (Sum.inl (Sum.inl (e, i))) 1 := rfl
example (N : DPLattice A) (i : N.ι) (e : Fin 2) :
    L5img φ N i (Sum.inr (Sum.inr e)) = Pi.single (Sum.inl (Sum.inr (e, i))) 1 := rfl
-- (L5): the explicit isomorphism on basis vectors
example (N : DPLattice A) (a b c : Fin 2) (i : N.ι) :
    (lemma35Iso φ h2 N).hom.toLin (Pi.single (a, (b, (c, i))) 1) =
      ∑ q : Fin 4 ⊕ (Fin 2 ⊕ Fin 2), hL (Pi.single (a, (b, c)) 1 : Fin 2 × (Fin 2 × Fin 2) → B) q •
        L5img φ N i q := lemma35Iso_single φ h2 N a b c i
end L5

-- (L6)
example (N : DPLattice ℤ_[2]) :
    Nonempty (Doubling.Iso (baseChange PadicInt.toZMod (tensorV (tensorV (phi N))))
      (baseChange PadicInt.toZMod (dsum (dsum (phi N) (phi N)) (phi (tensorV N))))) := L6 N

#print axioms Lemma35b.I1
#print axioms Lemma35b.I2
#print axioms Lemma35b.I3
#print axioms Lemma35b.B1
#print axioms Lemma35b.B2
#print axioms Lemma35b.B3
#print axioms Lemma35b.F1
#print axioms Lemma35b.F2
#print axioms Lemma35b.F3
#print axioms Lemma35b.uL_single
#print axioms Lemma35b.isoL4
#print axioms Lemma35b.L4
#print axioms Lemma35b.lemma35Iso
#print axioms Lemma35b.lemma35Iso_single
#print axioms Lemma35b.L5
#print axioms Lemma35b.L6
