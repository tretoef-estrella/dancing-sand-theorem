import RequestProject.Fold.All

/-! Auditor's check file for Lean piece C38, the fold in the group ring (Grepy Escribano,
8 Oct 2026). Restated by hand from `C38_the_fold_in_the_group_ring.md` (§10.1: Part G, Lemma 10.1
(L0)–(L4), Corollary 10.2 in module form (C1), (C2)), with every hypothesis of the file kept;
the definitions checked by `rfl`; then `#print axioms`. -/

open CubeLaplacian DPLattice Doubling LemmaW Lift2 Filt Step36 FamDec

variable {A : Type} [CommRing A]

-- Definitions, by `rfl`.
example (n : ℕ) (g : G n) (f : G n → A) :
    Fold.aElt n = (fun _ => 1) ∧ Fold.transl A n f g = f (g + Fold.aElt n) := ⟨rfl, rfl⟩
example (n : ℕ) : Fold.foldSub A n =
    LinearMap.range (lap A n) ⊔ LinearMap.range (Fold.transl A n - 1) := rfl
example (n : ℕ) (u : Fold.Gbar n → A) (x : Fold.Gbar n) :
    Fold.lapBar A n u x = (n : A) * u x - ∑ i, u (x + Fold.mk n (e n i)) := rfl
example (M : DPLattice A) (c : ℤ) (f : M.ι → A) (i : M.ι) :
    Fold.signOp M c f i = (-1) ^ ((c - M.wt i) / 2).natAbs * f i := rfl
example (M : DPLattice A) (c : ℤ) (B : ℕ) :
    Fold.expF M B = ∑ r ∈ Finset.range B, M.Fd r ∧
      Fold.aOp M c B = Fold.signOp M c ∘ₗ Fold.expF M B ∧
      Fold.tauOp M c = M.Fd 1 + (c : A) • 1 - H M := ⟨rfl, rfl, rfl⟩

-- (G1).
example (n : ℕ) : Fold.transl A n ∘ₗ Fold.transl A n = 1 ∧
    Fold.transl A n ∘ₗ lap A n = lap A n ∘ₗ Fold.transl A n := Fold.G1 A n

-- (G2).
example (n : ℕ) : Function.Surjective (Fold.push A n) := Fold.push_surjective A n
example (n : ℕ) : LinearMap.ker (Fold.push A n) = LinearMap.range (Fold.transl A n - 1) :=
  Fold.ker_push A n
example (n : ℕ) : Fold.push A n ∘ₗ lap A n = Fold.lapBar A n ∘ₗ Fold.push A n := Fold.push_lap A n

-- (G3), induced by `push`, and the case ℤ.
example (n : ℕ) : Nonempty (((Fold.Gbar n → A) ⧸ LinearMap.range (Fold.lapBar A n)) ≃ₗ[A]
    ((G n → A) ⧸ Fold.foldSub A n)) := Fold.G3 A n
example (n : ℕ) (f : G n → A) :
    (Fold.G3equiv A n).symm (Submodule.Quotient.mk f) = Submodule.Quotient.mk (Fold.push A n f) :=
  Fold.G3equiv_symm_mk A n f
example (n : ℕ) : Nonempty (Fold.cokerBar n ≃ₗ[ℤ] ((G n → ℤ) ⧸ Fold.foldSub ℤ n)) := Fold.G3Z n

-- (L0), (L1) Lemma 10.1, (L2).
example (n r : ℕ) (hr : n < r) : (tensorPow A n).Fd r = 0 := Fold.L0 n r hr
example (n : ℕ) : (psi A n).toLinearMap ∘ₗ Fold.transl A n =
    Fold.aOp (tensorPow A n) n (n + 1) ∘ₗ (psi A n).toLinearMap := Fold.L1 n
example (n B : ℕ) (hB : n + 1 ≤ B) :
    Fold.expF (tensorPow A n) B = Fold.expF (tensorPow A n) (n + 1) := Fold.L2 n B hB

-- (L3) transport.
example {M N : DPLattice A} (u : Doubling.Iso M N) (hhom : IsWtPres u.hom.toLin)
    (hinv : IsWtPres u.inv.toLin) (c : ℤ) (B : ℕ) :
    u.hom.toLin ∘ₗ Fold.expF M B = Fold.expF N B ∘ₗ u.hom.toLin ∧
    u.hom.toLin ∘ₗ Fold.signOp M c = Fold.signOp N c ∘ₗ u.hom.toLin ∧
    u.hom.toLin ∘ₗ Fold.aOp M c B = Fold.aOp N c B ∘ₗ u.hom.toLin ∧
    u.hom.toLin ∘ₗ Fold.tauOp M c = Fold.tauOp N c ∘ₗ u.hom.toLin ∧
    Nonempty (Fold.Xbar M c B ≃ₗ[A] Fold.Xbar N c B) := Fold.L3 u hhom hinv c B
example [IsDomain A] [CharZero A] {M N : DPLattice A} (u : Doubling.Iso M N) (c : ℤ) (B : ℕ) :
    IsWtPres u.hom.toLin ∧ IsWtPres u.inv.toLin ∧
      Nonempty (Fold.Xbar M c B ≃ₗ[A] Fold.Xbar N c B) := Fold.L3_charZero u c B

-- (L4) direct sums.
example (Ls : List (DPLattice A)) (c : ℤ) (B : ℕ) :
    ∃ Θ : ((dsumList Ls).ι → A) ≃ₗ[A] ((j : Fin Ls.length) → (Ls.get j).ι → A),
      (∀ r x, Θ ((dsumList Ls).Fd r x) = fun j => (Ls.get j).Fd r (Θ x j)) ∧
      (∀ x, Θ (H (dsumList Ls) x) = fun j => H (Ls.get j) (Θ x j)) ∧
      (∀ x, Θ (Fold.signOp (dsumList Ls) c x) = fun j => Fold.signOp (Ls.get j) c (Θ x j)) ∧
      (∀ x, Θ (Fold.expF (dsumList Ls) B x) = fun j => Fold.expF (Ls.get j) B (Θ x j)) ∧
      (∀ x, Θ (Fold.aOp (dsumList Ls) c B x) = fun j => Fold.aOp (Ls.get j) c B (Θ x j)) ∧
      (∀ x, Θ (Fold.tauOp (dsumList Ls) c x) = fun j => Fold.tauOp (Ls.get j) c (Θ x j)) ∧
      Nonempty (Fold.Xbar (dsumList Ls) c B ≃ₗ[A]
        ((j : Fin Ls.length) → Fold.Xbar (Ls.get j) c B)) := Fold.L4 Ls c B

-- The fold quotient is X̄ of V^{⊗n}.
example (n : ℕ) : Nonempty (((G n → A) ⧸ Fold.foldSub A n) ≃ₗ[A]
    Fold.Xbar (tensorPow A n) n (n + 1)) := ⟨Fold.foldEquivXbar n⟩

-- (C1) Corollary 10.2, module form, under the hypotheses of C30 (A1).
example {B : Type} [CommRing B] [IsDomain A] [CharZero A] [OddUnits A] {φ : A →+* B}
    (h1 : Lift2.H1 φ) (hk : Lift2.H2 φ) (h3 : Lift2.H3 A) (hU : Lift2.OneAddTwoUnit A)
    (h2 : (2 : B) = 0) (n : ℕ) :
    Nonempty (((G n → A) ⧸ Fold.foldSub A n) ≃ₗ[A]
      ((j : Fin (FamDec.L n).length) → Fold.Xbar (Filt.T A ((FamDec.L n).get j)) n (n + 1))) :=
  Fold.C1 h1 hk h3 hU h2 n

-- (C2) the case ℤ_[2].
example (n : ℕ) :
    Nonempty (((G n → ℤ_[2]) ⧸ Fold.foldSub ℤ_[2] n) ≃ₗ[ℤ_[2]]
      ((j : Fin (FamDec.L n).length) → Fold.Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1))) :=
  Fold.C2 n

#print axioms Fold.G1
#print axioms Fold.push_surjective
#print axioms Fold.ker_push
#print axioms Fold.push_lap
#print axioms Fold.G2
#print axioms Fold.G3
#print axioms Fold.G3equiv_symm_mk
#print axioms Fold.G3Z
#print axioms Fold.L0
#print axioms Fold.L1
#print axioms Fold.L2
#print axioms Fold.L3
#print axioms Fold.L3_charZero
#print axioms Fold.L4
#print axioms Fold.foldEquivXbar
#print axioms Fold.C1
#print axioms Fold.C2
