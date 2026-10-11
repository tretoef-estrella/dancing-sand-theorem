import RequestProject.FoldGroup.All

/-! Auditor's check file for Lean piece C38b, the folded cube: its cokernel, Corollary 10.2 as
groups, and Proposition 10.3 (Grepy Escribano, 8 Oct 2026). Restated by hand from
`C38b_the_folded_cube_and_proposition_103.md`, with `XbarFam` and `twoM` unfolded where they
appear; the definitions checked by `rfl`; then `#print axioms`. -/

open CubeLaplacian Fold

-- Definitions, by `rfl` (XbarFam and twoM unfolded).
example (lam i : ℕ) : FoldGroup.XbarFam lam i =
    Fold.Xbar (Filt.T ℤ_[2] lam) ((lam : ℤ) + 2 * (i : ℤ)) (lam + 2 * i + 1) := rfl
example (M : Type) [AddCommGroup M] :
    FoldGroup.twoM M = (nsmulAddMonoidHom (α := M) 2).range := rfl
example (M : Type) [AddCommGroup M] (y : M) :
    y ∈ FoldGroup.twoM M ↔ ∃ x : M, (2 : ℕ) • x = y := FoldGroup.mem_twoM

-- (K1).
example (A : Type) [CommRing A] (n : ℕ) (u : Gbar n → A) :
    ∑ x, lapBar A n u x = 0 := FoldGroup.K1 A n u

-- (K2).
example (n : ℕ) : Finite (KBar n) ∧ Nonempty (cokerBar n ≃ₗ[ℤ] ℤ × KBar n) := FoldGroup.K2 n

-- (K3).
example (n : ℕ) :
    Nonempty ((Gbar n → ℤ_[2]) ⧸ LinearMap.range (lapBar ℤ_[2] n) ≃+ ℤ_[2] × Syl2 (KBar n)) :=
  FoldGroup.K3 n

-- (D1) list form.
example (n : ℕ) :
    Nonempty (ℤ_[2] × Syl2 (KBar n) ≃+
      ((j : Fin (FamDec.L n).length) →
        Fold.Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1))) := FoldGroup.D1 n

-- (D2) shift form, XbarFam unfolded.
example (n : ℕ) :
    Nonempty (ℤ_[2] × Syl2 (KBar n) ≃+
      ((j : Fin (FamDec.L n).length) →
        Fold.Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j))
          (((FamDec.L n).get j : ℤ) + 2 * (((n - (FamDec.L n).get j) / 2 : ℕ) : ℤ))
          ((FamDec.L n).get j + 2 * ((n - (FamDec.L n).get j) / 2) + 1))) := FoldGroup.D2 n

-- (D3) multiplicity form, XbarFam unfolded.
example (n : ℕ) :
    Nonempty (ℤ_[2] × Syl2 (KBar n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) →
        Fold.Xbar (Filt.T ℤ_[2] q.1) (((q.1 : ℕ) : ℤ) + 2 * (((n - q.1) / 2 : ℕ) : ℤ))
          (q.1 + 2 * ((n - q.1) / 2) + 1))) := FoldGroup.D3 n

-- (P1), twoM unfolded.
example :
    (∀ (ι : Type) (M : ι → Type) [∀ j, AddCommGroup (M j)],
      Nonempty ((nsmulAddMonoidHom (α := (j : ι) → M j) 2).range ≃+
        ((j : ι) → (nsmulAddMonoidHom (α := M j) 2).range))) ∧
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N],
      Nonempty ((nsmulAddMonoidHom (α := M × N) 2).range ≃+
        (nsmulAddMonoidHom (α := M) 2).range × (nsmulAddMonoidHom (α := N) 2).range)) ∧
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N], (M ≃+ N) →
      Nonempty ((nsmulAddMonoidHom (α := M) 2).range ≃+ (nsmulAddMonoidHom (α := N) 2).range)) ∧
    Nonempty ((nsmulAddMonoidHom (α := ℤ_[2]) 2).range ≃+ ℤ_[2]) := FoldGroup.P1

-- (P2) Proposition 10.3, XbarFam and twoM unfolded.
example (HX : ∀ lam ≥ 1, ∀ i : ℕ,
      Nonempty (Fold.Xbar (Filt.T ℤ_[2] lam) ((lam : ℤ) + 2 * (i : ℤ)) (lam + 2 * i + 1) ≃+
        (nsmulAddMonoidHom (α := FamilyGroup.X (Families.ds lam) 1 i) 2).range))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (Syl2 (KBar n) ≃+ (nsmulAddMonoidHom (α := Syl2 (K n)) 2).range) :=
  FoldGroup.P2 HX n hn

#print axioms FoldGroup.mem_twoM
#print axioms FoldGroup.K1
#print axioms FoldGroup.KBar_finite
#print axioms FoldGroup.cokerBarEquivKBar
#print axioms FoldGroup.K2
#print axioms FoldGroup.K3
#print axioms FoldGroup.D1
#print axioms FoldGroup.D2
#print axioms FoldGroup.D3
#print axioms FoldGroup.twoMPi
#print axioms FoldGroup.twoMProd
#print axioms FoldGroup.twoMCongr
#print axioms FoldGroup.twoMPadic
#print axioms FoldGroup.P1
#print axioms FoldGroup.P2
