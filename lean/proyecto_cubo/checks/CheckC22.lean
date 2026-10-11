import RequestProject.Lemma35.All

/-! Auditor's check file for Lean piece C22 (Grepy Escribano, 7 Oct 2026).
Restated by hand from `C22_lemma_35_over_F2.md`: the direct sum (basis, weights, blockwise
operators), (S1), (S2) with the stated maps; the encodings of `V^{⊗3}`, `D`, `V ⊗ V^{[1]}` as
`Pi.single`; the tables of `g`, `h`, `u`, `u⁻¹` written with `Pi.single`; (L1), (L2) with the
objects written out; the cross-check `F^{(1)}(000) = 100 + 010 + 001`; (L3) over `ZMod 2`; the
remark over `ℤ`; then `#print axioms`. -/

open Finset DPLattice WeylFilt Doubling Twist Lemma35

section S
variable {A : Type} [CommRing A]

-- the direct sum: basis M.ι ⊕ N.ι, weights Sum.elim, blockwise operators
example (M N : DPLattice A) : (dsum M N).ι = (M.ι ⊕ N.ι) := rfl
example (M N : DPLattice A) : (dsum M N).wt = Sum.elim M.wt N.wt := rfl
example (M N : DPLattice A) (r : ℕ) (x : M.ι ⊕ N.ι → A) (i : M.ι) :
    (dsum M N).Fd r x (Sum.inl i) = M.Fd r (x ∘ Sum.inl) i := rfl
example (M N : DPLattice A) (r : ℕ) (x : M.ι ⊕ N.ι → A) (j : N.ι) :
    (dsum M N).Fd r x (Sum.inr j) = N.Fd r (x ∘ Sum.inr) j := rfl
example (M N : DPLattice A) (r : ℕ) (x : M.ι ⊕ N.ι → A) (i : M.ι) :
    (dsum M N).Ed r x (Sum.inl i) = M.Ed r (x ∘ Sum.inl) i := rfl
example (M N : DPLattice A) (r : ℕ) (x : M.ι ⊕ N.ι → A) (j : N.ι) :
    (dsum M N).Ed r x (Sum.inr j) = N.Ed r (x ∘ Sum.inr) j := rfl
-- (S1)
example (M N : DPLattice A) : IsDP (Sum.elim M.wt N.wt) (fun r => blk (M.Fd r) (N.Fd r))
    (fun r => blk (M.Ed r) (N.Ed r)) := S1 M N
-- (S2) inclusions and projections
example (M N : DPLattice A) :
    ∃ i : Hom M (dsum M N), ∀ x, i.toLin x = Sum.elim x (0 : N.ι → A) := (S2 M N).1
example (M N : DPLattice A) :
    ∃ i : Hom N (dsum M N), ∀ y, i.toLin y = Sum.elim (0 : M.ι → A) y := (S2 M N).2.1
example (M N : DPLattice A) :
    ∃ p : Hom (dsum M N) M, ∀ z, p.toLin z = z ∘ Sum.inl := (S2 M N).2.2.1
example (M N : DPLattice A) :
    ∃ p : Hom (dsum M N) N, ∀ z, p.toLin z = z ∘ Sum.inr := (S2 M N).2.2.2.1
-- (S2) f ⊕ g acts blockwise; identities and composites
example {M N M' N' : DPLattice A} (f : Hom M M') (g : Hom N N') (z : M.ι ⊕ N.ι → A) (i : M'.ι) :
    (dsumHom f g).toLin z (Sum.inl i) = f.toLin (z ∘ Sum.inl) i :=
  congrFun ((S2 M N).2.2.2.2.1 f g z).1 i
example {M N M' N' : DPLattice A} (f : Hom M M') (g : Hom N N') (z : M.ι ⊕ N.ι → A) (j : N'.ι) :
    (dsumHom f g).toLin z (Sum.inr j) = g.toLin (z ∘ Sum.inr) j :=
  congrFun ((S2 M N).2.2.2.2.1 f g z).2 j
example (M N : DPLattice A) : dsumHom (Hom.id M) (Hom.id N) = Hom.id (dsum M N) :=
  (S2 M N).2.2.2.2.2.1
example {M N M' N' M'' N'' : DPLattice A} (f : Hom M' M'') (g : Hom N' N'') (f' : Hom M M')
    (g' : Hom N N') :
    dsumHom (Hom.comp f f') (Hom.comp g g') = Hom.comp (dsumHom f g) (dsumHom f' g') :=
  (S2 M N).2.2.2.2.2.2 f g f' g'
end S

section L
variable {B : Type} [CommRing B] (h2 : (2 : B) = 0)

-- the encodings
example : T3 B = tensorV (tensorV (V B)) := rfl
example : D3 B = dsum (delta B 3) (dsum (V B) (V B)) := rfl
example (a b c : Fin 2) : (w a b c : Fin 2 × (Fin 2 × Fin 2) → B) = Pi.single (a, (b, c)) 1 := rfl
example (r : Fin 4) : (eD r : Fin 4 ⊕ (Fin 2 ⊕ Fin 2) → B) = Pi.single (Sum.inl r) 1 := rfl
example (e : Fin 2) :
    (bD e : Fin 4 ⊕ (Fin 2 ⊕ Fin 2) → B) = Pi.single (Sum.inr (Sum.inl e)) 1 := rfl
example (e : Fin 2) :
    (Lemma35.cD e : Fin 4 ⊕ (Fin 2 ⊕ Fin 2) → B) = Pi.single (Sum.inr (Sum.inr e)) 1 := rfl
example : VV1 h2 = tensorV (Twist.frob h2 (V B)) := rfl
example (e e' : Fin 2) : (bb e e' : Fin 2 × Fin 2 → B) = Pi.single (e, e') 1 := rfl

-- the table of g, written with Pi.single
example : gL (B := B) (Pi.single (Sum.inl 1) 1) =
    Pi.single (1, (0, 0)) 1 + Pi.single (0, (1, 0)) 1 + Pi.single (0, (0, 1)) 1 :=
  (g_basis (B := B)).2.1
example : gL (B := B) (Pi.single (Sum.inl 2) 1) =
    Pi.single (1, (1, 0)) 1 + Pi.single (1, (0, 1)) 1 + Pi.single (0, (1, 1)) 1 :=
  (g_basis (B := B)).2.2.1
example : gL (B := B) (Pi.single (Sum.inr (Sum.inl 1)) 1) =
    Pi.single (1, (0, 1)) 1 + Pi.single (0, (1, 1)) 1 := (g_basis (B := B)).2.2.2.2.2.1
example : gL (B := B) (Pi.single (Sum.inr (Sum.inr 0)) 1) =
    Pi.single (0, (1, 0)) 1 + Pi.single (0, (0, 1)) 1 := (g_basis (B := B)).2.2.2.2.2.2.1
-- the table of h, written with Pi.single
example : hL (B := B) (Pi.single (0, (1, 0)) 1) =
    Pi.single (Sum.inl 1) 1 + Pi.single (Sum.inr (Sum.inl 0)) 1 +
      Pi.single (Sum.inr (Sum.inr 0)) 1 := (h_basis (B := B)).2.2.1
example : hL (B := B) (Pi.single (1, (0, 1)) 1) =
    Pi.single (Sum.inl 2) 1 + Pi.single (Sum.inr (Sum.inl 1)) 1 +
      Pi.single (Sum.inr (Sum.inr 1)) 1 := (h_basis (B := B)).2.2.2.2.2.1
example : hL (B := B) (Pi.single (1, (1, 1)) 1) = Pi.single (Sum.inl 3) 1 :=
  (h_basis (B := B)).2.2.2.2.2.2.2
-- cross-check of the indexing: F^{(1)}(000) = 100 + 010 + 001 in V^{⊗3}
example : (tensorV (tensorV (V B))).Fd 1 (Pi.single ((0 : Fin 2), ((0 : Fin 2), (0 : Fin 2))) 1) =
    Pi.single ((1 : Fin 2), ((0 : Fin 2), (0 : Fin 2))) 1 + Pi.single ((0 : Fin 2), ((1 : Fin 2), (0 : Fin 2))) 1 + Pi.single ((0 : Fin 2), ((0 : Fin 2), (1 : Fin 2))) 1 :=
  (g_eD_eq_Fd (B := B) 1).symm.trans (g_basis (B := B)).2.1

-- (L1)
example : ∃ (g : Hom (dsum (delta B 3) (dsum (V B) (V B))) (tensorV (tensorV (V B))))
    (h : Hom (tensorV (tensorV (V B))) (dsum (delta B 3) (dsum (V B) (V B)))),
      g.toLin = gL ∧ h.toLin = hL ∧
      Hom.comp h g = Hom.id (dsum (delta B 3) (dsum (V B) (V B))) ∧
      Hom.comp g h = Hom.id (tensorV (tensorV (V B))) ∧
      ∀ r : Fin 4, g.toLin (Pi.single (Sum.inl r) 1) =
        (tensorV (tensorV (V B))).Fd r (Pi.single ((0 : Fin 2), ((0 : Fin 2), (0 : Fin 2))) 1) := by
  obtain ⟨g, h, a, b, c, d, -, e⟩ := L1 h2
  exact ⟨g, h, a, b, c, d, e⟩
example : Nonempty (Iso (tensorV (tensorV (V B))) (dsum (delta B 3) (dsum (V B) (V B)))) :=
  (L1 h2).choose_spec.choose_spec.2.2.2.2.1

-- the table of u and u⁻¹
example : uL (B := B) (Pi.single 1 1) = Pi.single (1, 0) 1 := (u_basis (B := B)).2.1
example : uL (B := B) (Pi.single 2 1) = Pi.single (0, 1) 1 := (u_basis (B := B)).2.2.1
example : uinvL (B := B) (Pi.single (1, 1) 1) = Pi.single 3 1 := (uinv_basis (B := B)).2.2.2
-- (L2)
example : ∃ (u : Hom (delta B 3) (tensorV (Twist.frob h2 (V B))))
    (u' : Hom (tensorV (Twist.frob h2 (V B))) (delta B 3)),
      u.toLin = uL ∧ u'.toLin = uinvL ∧
      Hom.comp u' u = Hom.id (delta B 3) ∧ Hom.comp u u' = Hom.id (tensorV (Twist.frob h2 (V B))) ∧
      ∀ r : Fin 4, u.toLin (Pi.single r 1) =
        (tensorV (Twist.frob h2 (V B))).Fd r (Pi.single ((0 : Fin 2), (0 : Fin 2)) 1) := by
  obtain ⟨u, u', a, b, c, d, -, e⟩ := L2 h2
  exact ⟨u, u', a, b, c, d, e⟩
end L

-- (L3)
example : Nonempty (Iso (tensorV (tensorV (V (ZMod 2))))
    (dsum (delta (ZMod 2) 3) (dsum (V (ZMod 2)) (V (ZMod 2))))) := L3.1
example : Nonempty (Iso (delta (ZMod 2) 3)
    (tensorV (Twist.frob (show (2 : ZMod 2) = 0 from rfl) (V (ZMod 2))))) := L3.2
-- the remark over ℤ: g is not a Hom
example : ¬ ∃ φ : Hom (dsum (delta ℤ 3) (dsum (V ℤ) (V ℤ))) (tensorV (tensorV (V ℤ))),
    φ.toLin = gL := g_not_hom_int

#print axioms Lemma35.dsum
#print axioms Lemma35.S1
#print axioms Lemma35.S2
#print axioms Lemma35.g_basis
#print axioms Lemma35.h_basis
#print axioms Lemma35.g_eD_eq_Fd
#print axioms Lemma35.isoL1
#print axioms Lemma35.L1
#print axioms Lemma35.u_basis
#print axioms Lemma35.uinv_basis
#print axioms Lemma35.u_eW_eq_Fd
#print axioms Lemma35.isoL2
#print axioms Lemma35.L2
#print axioms Lemma35.L3
#print axioms Lemma35.g_not_hom_int
