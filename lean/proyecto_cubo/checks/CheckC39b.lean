import RequestProject.FoldCube.All

/-! Auditor's check file for Lean piece C39b, the cube side on the half lattice (Grepy Escribano,
9 Oct 2026). Restated by hand from `C39b_the_cube_side_on_the_half_lattice.md`: the definitions by
`rfl`; Parts O and V with the file's statements; then `#print axioms`. -/

open DPLattice Doubling Fold FoldHalf FoldCube

section defs
variable {A : Type} [CommRing A] (M N : DPLattice A) (c d e : ℤ)

example : Jop M c = (c : A) • 1 - H M := rfl
example : Gp N d = N.Fd 1 - (2 : A) • (Jop N d * (Jop N d + 1)) := rfl
example : SigmaOp N e = N.Fd 1 + ((2 * e : ℤ) : A) • 1 - (2 : A) • H N := rfl
example (f : M.ι → A) (i : M.ι) :
    halfJJ M c f i = ((((c - M.wt i) * (c - M.wt i + 2)) / 2 : ℤ) : A) * f i := rfl
example : thetaOp M c = M.Fd 2 + M.Fd 1 * (Jop M c + 2) + halfJJ M c := rfl
end defs

section phidefs
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]
  (N : DPLattice A) (BN : ℕ) (d : ℤ) (B : ℕ)
example : thX N BN d B = LinearMap.fst A (N.ι → A) (N.ι → A) ∘ₗ FoldHalf.betaInv N BN d ∘ₗ
    thetaOp (phi N) (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl A (N.ι → A) (N.ι → A) :=
  rfl
example : thY N BN d B = LinearMap.snd A (N.ι → A) (N.ι → A) ∘ₗ FoldHalf.betaInv N BN d ∘ₗ
    thetaOp (phi N) (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl A (N.ι → A) (N.ι → A) :=
  rfl
end phidefs

-- (O1)
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (d : ℤ) :
    Nonempty ((((phi N).ι → A) ⧸ LinearMap.range (Fold.tauOp (phi N) (2 * d + 1))) ≃ₗ[A]
      (N.ι → A) ⧸ LinearMap.range ((2 : A) • Gp N d)) := O1 N d

-- (O2), with the class of x going to 2·[x]
example {A : Type} [CommRing A] {L : Type} [AddCommGroup L] [Module A L]
    (h2 : ∀ x : L, (2 : ℕ) • x = 0 → x = 0) (G : Module.End A L) :
    ∃ e : FoldGroup.twoM (L ⧸ LinearMap.range ((2 : A) • G)) ≃+ L ⧸ LinearMap.range G,
      ∀ x : L, ((e.symm (Submodule.Quotient.mk x)) : L ⧸ LinearMap.range ((2 : A) • G)) =
        (2 : ℕ) • Submodule.Quotient.mk x := O2 h2 G
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] (ι : Type) :
    ∀ x : ι → A, (2 : ℕ) • x = 0 → x = 0 := O2_pi ι

-- (O3)
example {A : Type} [CommRing A] [OddUnits A] (N : DPLattice A) (W : ℤ)
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (d : ℤ) :
    Nonempty (((N.ι → A) ⧸ LinearMap.range (Gp N d)) ≃ₗ[A]
      (N.ι → A) ⧸ LinearMap.range (SigmaOp N (if Even (d - W) then d else d + 1))) :=
  O3 N W htop d

-- (O4)
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (l : ℕ) :
    ∀ i, (Filt.T A l).wt i ≤ l ∧ Even ((l : ℤ) - (Filt.T A l).wt i) := O4 l

-- (O5), both forms; c = (j + 1) / 2 = ⌈j/2⌉
example (l j : ℕ) :
    Nonempty (FoldGroup.twoM (((Filt.T ℤ_[2] (2 * l + 1)).ι → ℤ_[2]) ⧸
        LinearMap.range (Families.sigL ℤ_[2] (2 * l + 1) 1 j)) ≃+
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ)))) :=
  O5 l j
example (l j : ℕ) :
    Nonempty (FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j) ≃+
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ)))) :=
  O5_X l j

-- (V1)
example {A : Type} [CommRing A] (M : DPLattice A) (c : ℤ) :
    Nonempty ((((DPLattice.tensorV M).ι → A) ⧸
        LinearMap.range (Fold.tauOp (DPLattice.tensorV M) (c + 1))) ≃ₗ[A]
      (M.ι → A) ⧸ LinearMap.range (Fold.tauOp M c * (Fold.tauOp M c + 2))) := V1 M c

-- (V2), both sentences
example {A : Type} [CommRing A] (M : DPLattice A) (c : ℤ) (hev : ∀ i, Even (c - M.wt i)) :
    (2 : A) • thetaOp M c = Fold.tauOp M c * (Fold.tauOp M c + 2) := V2 M c hev
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (d : ℤ) :
    (∀ i, Even (2 * d + 1 - (phi N).wt i)) ∧
    (2 : A) • thetaOp (phi N) (2 * d + 1) =
      Fold.tauOp (phi N) (2 * d + 1) * (Fold.tauOp (phi N) (2 * d + 1) + 2) := V2_phi N d

section V3
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (BN : ℕ)
  (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
-- (V3) (a), (b), (c), with P, Q unfolded by rfl
example : PE N BN d = ((2 * d : ℤ) : A) • 1 - (2 : A) • H N + Ch N BN * ShInv N BN := rfl
example : QE N BN d = -(parOp N d * ShInv N BN) := rfl
example :
    (∀ x y, thetaOp (phi N) (2 * d + 1) (beta N d B (x, y)) =
      beta N d B (thX N BN d B x + thY N BN d B y, thY N BN d B x + thX N BN d B y)) ∧
    ((2 : A) • thX N BN d B = PE N BN d * PE N BN d + QE N BN d * QE N BN d + (2 : A) • PE N BN d ∧
      (2 : A) • thY N BN d B =
        PE N BN d * QE N BN d + QE N BN d * PE N BN d + (2 : A) • QE N BN d) ∧
    (PE N BN d - QE N BN d = Psi N (d + 1) BN - 2 ∧
      (2 : A) • (thX N BN d B + thY N BN d B) = Psi N d BN * (Psi N d BN + 2) ∧
      (2 : A) • (thX N BN d B - thY N BN d B) = (Psi N (d + 1) BN - 2) * Psi N (d + 1) BN) :=
  V3 N BN hnil d B hB
-- (V5)
example :
    Nonempty (FoldGroup.twoM (((DPLattice.tensorV (phi N)).ι → A) ⧸
        LinearMap.range (Fold.tauOp (DPLattice.tensorV (phi N)) (2 * d + 2))) ≃+
      ((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (FoldHalf.glueOp (thX N BN d B - thY N BN d B)
        (thX N BN d B + thY N BN d B) (thY N BN d B))) := V5 N BN hnil d B hB
end V3

-- (V4)
example {A : Type} [CommRing A] {L M' : Type} [AddCommGroup L] [Module A L] [AddCommGroup M']
    [Module A M'] (β : (L × L) ≃ₗ[A] M') (w : Module.End A M') (X Y : Module.End A L)
    (hw : ∀ x y, w (β (x, y)) = β (X x + Y y, Y x + X y)) :
    Nonempty ((M' ⧸ LinearMap.range w) ≃ₗ[A]
      (L × L) ⧸ LinearMap.range (FoldHalf.glueOp (X - Y) (X + Y) Y)) := V4 β w X Y hw

-- (V6): N = T(l), d = l + i, BN = l + 1, B = 2l + 2
example (l i : ℕ) :
    Nonempty (FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i) ≃+
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
        LinearMap.range (FoldHalf.glueOp
          (thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) -
            thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2))
          (thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) +
            thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2))
          (thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2)))) := V6 l i

#print axioms FoldCube.O1
#print axioms FoldCube.O2
#print axioms FoldCube.O2_pi
#print axioms FoldCube.O3
#print axioms FoldCube.O4
#print axioms FoldCube.O5
#print axioms FoldCube.O5_X
#print axioms FoldCube.V1
#print axioms FoldCube.V2
#print axioms FoldCube.V2_phi
#print axioms FoldCube.V3
#print axioms FoldCube.V4
#print axioms FoldCube.V5
#print axioms FoldCube.V6
