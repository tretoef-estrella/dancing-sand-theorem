import RequestProject.FoldHalf.All

/-! Auditor's check file for Lean piece C39, the fold on the half-size lattice (Grepy Escribano,
9 Oct 2026). Restated by hand from `C39_the_fold_on_the_half_lattice.md`: the definitions by
`rfl`; Parts S, E, A with the file's statements; then `#print axioms`. -/

open DPLattice Doubling Fold FoldHalf

section defs
variable {A : Type} [CommRing A] (N : DPLattice A) (BN : ℕ) (d : ℤ)

example : Ch N BN = ∑ s ∈ Finset.range BN, dfi (A := A) s • N.Fd s := rfl
example : Sh N BN = ∑ s ∈ Finset.range BN, dfi (A := A) (s + 1) • N.Fd s := rfl
example (f : N.ι → A) (i : N.ι) : parOp N d f i = (-1) ^ (d - N.wt i).natAbs * f i := rfl
example : ShInv N BN = Ring.inverse (Sh N BN) := rfl
example : Psi N d BN =
    ((2 * d : ℤ) : A) • 1 - (2 : A) • H N + (Ch N BN - parOp N d) * ShInv N BN := rfl
example : Zop N d BN = -1 - parOp N d * ShInv N BN := rfl
example (X Y Z : Module.End A (N.ι → A)) (m m' : N.ι → A) :
    glueOp X Y Z (m, m') = (X m, Z m + Y m') := rfl
end defs

-- Part S.
example {A : Type} [CommRing A] (N : DPLattice A) (BN : ℕ) (hnil : ∀ s ≥ BN, N.Fd s = 0) :
    IsUnit (Sh N BN) ∧ Sh N BN * ShInv N BN = 1 ∧ ShInv N BN * Sh N BN = 1 := S1 N BN hnil
example {A : Type} [CommRing A] (N : DPLattice A) (BN : ℕ) (d : ℤ) :
    parOp N d * parOp N d = 1 ∧
    (∀ s, parOp N d * N.Fd s = N.Fd s * parOp N d) ∧
    parOp N d * Ch N BN = Ch N BN * parOp N d ∧
    parOp N d * Sh N BN = Sh N BN * parOp N d ∧
    parOp N d * ShInv N BN = ShInv N BN * parOp N d ∧
    Ch N BN * Sh N BN = Sh N BN * Ch N BN ∧
    Ch N BN * ShInv N BN = ShInv N BN * Ch N BN ∧
    Sh N BN * ShInv N BN = ShInv N BN * Sh N BN := S2 N BN d
example {A : Type} [CommRing A] (N : DPLattice A) (BN : ℕ) (d : ℤ) :
    (2 : A) • Zop N d BN = Psi N d BN - Psi N (d + 1) BN := S3 N BN d
example {A : Type} [CommRing A] (L : Type) [AddCommGroup L] [Module A L]
    (X Y Z X' Y' Z' : Module.End A L) :
    glueOp X Y Z ∘ₗ glueOp X' Y' Z' = glueOp (X ∘ₗ X') (Y ∘ₗ Y') (Z ∘ₗ X' + Y ∘ₗ Z') :=
  S4 X Y Z X' Y' Z'

section E
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]
  (N : DPLattice A) (BN : ℕ) (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)

example : ∀ r ≥ 2 * BN, (phi N).Fd r = 0 := E0 N BN hnil
example (n : N.ι → A) :
    Fold.expF (phi N) B (bvec 0 n) = bvec 0 (Ch N BN n) + bvec 1 (Sh N BN n) :=
  E1 N BN hnil B hB n
example (n : N.ι → A) :
    Fold.aOp (phi N) (2 * d + 1) B (bvec 0 n) =
      bvec 0 (parOp N d (Ch N BN n)) - bvec 1 (parOp N d (Sh N BN n)) := E2 N BN hnil d B hB n
example :
    Fold.aOp (phi N) (2 * d + 1) B * Fold.aOp (phi N) (2 * d + 1) B = 1 ∧
    Fold.aOp (phi N) (2 * d + 1) B * Fold.tauOp (phi N) (2 * d + 1) =
      Fold.tauOp (phi N) (2 * d + 1) * Fold.aOp (phi N) (2 * d + 1) B := E3 N BN hnil d B hB
example : ∃ β : ((N.ι → A) × (N.ι → A)) ≃ₗ[A] ((phi N).ι → A),
    ∀ x y, β (x, y) = (id (bvec 0 x) : (phi N).ι → A) +
      Fold.aOp (phi N) (2 * d + 1) B (bvec 0 y) := E4 N BN hnil d B hB
-- (E5): P, Q, β unfolded by rfl, then the statement.
example : PE N BN d = ((2 * d : ℤ) : A) • 1 - (2 : A) • H N + Ch N BN * ShInv N BN := rfl
example : QE N BN d = -(parOp N d * ShInv N BN) := rfl
example (x y : N.ι → A) : beta N d B (x, y) =
    (id (bvec 0 x) : (phi N).ι → A) + Fold.aOp (phi N) (2 * d + 1) B (bvec 0 y) := rfl
example :
    (∀ x y, Fold.tauOp (phi N) (2 * d + 1) (beta N d B (x, y)) =
      beta N d B (PE N BN d x + QE N BN d y, QE N BN d x + PE N BN d y)) ∧
    (∀ x y, Fold.aOp (phi N) (2 * d + 1) B (beta N d B (x, y)) = beta N d B (y, x)) ∧
    PE N BN d + QE N BN d = Psi N d BN := E5 N BN hnil d B hB

-- (A1) Lemma 10.4(a).
example : Nonempty (Fold.Xbar (Doubling.phi N) (2 * d + 1) B ≃ₗ[A]
    (N.ι → A) ⧸ LinearMap.range (Psi N d BN)) := A1 N BN hnil d B hB
-- (A2) Lemma 10.5(a).
example (B' : ℕ) (hB' : 2 * BN + 1 ≤ B') :
    Nonempty (Fold.Xbar (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2) B' ≃ₗ[A]
      ((N.ι → A) × (N.ι → A)) ⧸
        LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN))) :=
  A2 N BN hnil d B' hB'
end E

-- (A3).
example (A : Type) [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (l : ℕ) :
    (∀ i : (Filt.T A l).ι, -(l : ℤ) ≤ (Filt.T A l).wt i ∧ (Filt.T A l).wt i ≤ l) ∧
    ∀ s ≥ l + 1, (Filt.T A l).Fd s = 0 := A3 A l

-- (A4), XbarFam unfolded.
example (l j : ℕ) :
    Nonempty (Fold.Xbar (Filt.T ℤ_[2] (2 * l + 1)) (((2 * l + 1 : ℕ) : ℤ) + 2 * (j : ℤ))
        (2 * l + 1 + 2 * j + 1) ≃ₗ[ℤ_[2]]
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range (Psi (Filt.T ℤ_[2] l) (l + j) (l + 1))) :=
  A4_odd l j
example (l i : ℕ) :
    Nonempty (Fold.Xbar (Filt.T ℤ_[2] (2 * l + 2)) (((2 * l + 2 : ℕ) : ℤ) + 2 * (i : ℤ))
        (2 * l + 2 + 2 * i + 1) ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
        LinearMap.range (glueOp (Psi (Filt.T ℤ_[2] l) (l + i + 1) (l + 1))
          (Psi (Filt.T ℤ_[2] l) (l + i) (l + 1)) (Zop (Filt.T ℤ_[2] l) (l + i) (l + 1)))) :=
  A4_even l i

#print axioms FoldHalf.S1
#print axioms FoldHalf.S2
#print axioms FoldHalf.S3
#print axioms FoldHalf.S4
#print axioms FoldHalf.E0
#print axioms FoldHalf.E1
#print axioms FoldHalf.E2
#print axioms FoldHalf.E3
#print axioms FoldHalf.E4
#print axioms FoldHalf.E5
#print axioms FoldHalf.A1
#print axioms FoldHalf.A2
#print axioms FoldHalf.A3
#print axioms FoldHalf.A4_odd
#print axioms FoldHalf.A4_even
#print axioms FoldHalf.A4
