import RequestProject.Families.All

/-! Auditor's check file for Lean piece C32 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C32_theorem_38_the_groups_of_the_families.md`: (B0) the three equations;
two hand values of `ds` (checked first against the tower model of `chkC32.py`: ds 5 = [false, true],
ds 6 = [true, true]); (B0b) and its instance at λ = 5; (B1) with (a), (b) written out; (B2) with the
operator `sigL` unfolded; (B2Z); (Q0); (Q1); (Q2); (T1) under the hypotheses of C30 (A1), every
hypothesis explicit; (T2) Theorem 3.8 over ℤ_[2]; (T3) the multiplicity form; then
`#print axioms`. -/

open DirectSum DPLattice Doubling Lift2 Filt Step36 FamDec

-- (B0) the three equations.
example (l : ℕ) : Families.ds 0 = [] ∧ Families.ds (2 * l + 1) = false :: Families.ds l ∧
    Families.ds (2 * l + 2) = true :: Families.ds l :=
  ⟨Families.ds_zero, Families.ds_odd l, Families.ds_even l⟩

-- Hand values: 5 = 2·2 + 1, 2 = 2·0 + 2; 6 = 2·2 + 2.
example : Families.ds 5 = [false, true] := by
  rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, Families.ds_odd, show (2 : ℕ) = 2 * 0 + 2 from rfl,
    Families.ds_even, Families.ds_zero]
example : Families.ds 6 = [true, true] := by
  rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, Families.ds_even, show (2 : ℕ) = 2 * 0 + 2 from rfl,
    Families.ds_even, Families.ds_zero]

-- (B0b).
example (lam : ℕ) :
    lam + 1 = 2 ^ (Families.ds lam).length + ∑ t ∈ Windows.Ids (Families.ds lam), 2 ^ t :=
  Families.B0b lam

section B
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

-- (B1) with (a) and (b) written out.
example (lam : ℕ) : ∃ Θ : ((T A lam).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (Families.ds lam), A),
    Θ.toLinearMap ∘ₗ (T A lam).Fd 1 = Dance.F A (Families.ds lam) ∘ₗ Θ.toLinearMap ∧
    ∀ (j : (T A lam).ι) (q : Dance.Idx (Families.ds lam)),
      2 * (Dance.fl (Families.ds lam) q : ℤ) + (T A lam).wt j ≠ lam →
        Θ (Pi.single j 1) q = 0 :=
  Families.B1 lam

-- The operator of Part B2, unfolded.
example (lam α i : ℕ) : Families.sigL A lam α i =
    (T A lam).Fd 1 + (2 ^ (α - 1) : A) • (((lam : A) + 2 * i) • LinearMap.id - H (T A lam)) :=
  rfl

-- (B2).
example (lam α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((((T A lam).ι → A) ⧸ LinearMap.range ((T A lam).Fd 1 + (2 ^ (α - 1) : A) •
        (((lam : A) + 2 * i) • LinearMap.id - H (T A lam)))) ≃ₗ[A]
      (Dance.SysT A (Families.ds lam) (Fin 1) ⧸
        LinearMap.range (Dance.sigma A (Families.ds lam) α i))) :=
  Families.B2 lam α i hα
end B

-- (B2Z).
example (lam α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((((T ℤ_[2] lam).ι → ℤ_[2]) ⧸ LinearMap.range (Families.sigL ℤ_[2] lam α i)) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds lam) α i) :=
  Families.B2Z lam α i hα

section Q
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

-- (Q0).
example (n : ℕ) : tpow A n = DPLattice.tensorPow A n := Families.Q0 n
end Q

section Q'
variable {A : Type} [CommRing A]

-- (Q1).
example (Ls : List (DPLattice A)) :
    ∃ Θ : ((dsumList Ls).ι → A) ≃ₗ[A] ((j : Fin Ls.length) → (Ls.get j).ι → A),
      (∀ x, Θ ((dsumList Ls).Fd 1 x) = fun j => (Ls.get j).Fd 1 (Θ x j)) ∧
      (∀ x, Θ (H (dsumList Ls) x) = fun j => H (Ls.get j) (Θ x j)) :=
  Families.Q1 Ls

-- (Q2).
example {X Y : DPLattice A} (e : Doubling.Iso X Y) :
    ∃ Θ : (X.ι → A) ≃ₗ[A] (Y.ι → A),
      Θ.toLinearMap ∘ₗ X.Fd 1 = Y.Fd 1 ∘ₗ Θ.toLinearMap ∧
      Θ.toLinearMap ∘ₗ H X = H Y ∘ₗ Θ.toLinearMap :=
  Families.Q2 e
end Q'

section T
variable {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [CharZero A] [OddUnits A]

-- (T1) list form, every hypothesis of C30 (A1) explicit.
example (φ : A →+* B) (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A)
    (h2 : (2 : B) = 0) (n : ℕ) :
    Nonempty (((CubeLaplacian.G n → A) ⧸ LinearMap.range (CubeLaplacian.lap A n)) ≃ₗ[A]
      ((j : Fin (FamDec.L n).length) → Dance.SysT A (Families.ds ((FamDec.L n).get j)) (Fin 1) ⧸
        LinearMap.range (Dance.sigma A (Families.ds ((FamDec.L n).get j)) 1
          ((n - (FamDec.L n).get j) / 2)))) :=
  Families.T1 (φ := φ) h1 hk h3 hU h2 n
end T

-- (T2) Theorem 3.8 over ℤ_[2].
example (n : ℕ) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((j : Fin (FamDec.L n).length) →
        FamilyGroup.X (Families.ds ((FamDec.L n).get j)) 1 ((n - (FamDec.L n).get j) / 2))) :=
  Families.T2 n

-- (T3) the multiplicity form.
example (n : ℕ) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) →
        FamilyGroup.X (Families.ds q.1) 1 ((n - q.1) / 2))) :=
  Families.T3 n

#print axioms Families.ds_even
#print axioms Families.B0b
#print axioms Families.B1
#print axioms Families.B1a
#print axioms Families.B1b
#print axioms Families.B2
#print axioms Families.B2Z
#print axioms Families.Q0
#print axioms Families.Q1
#print axioms Families.Q2
#print axioms Families.T1
#print axioms Families.T2
#print axioms Families.T3
