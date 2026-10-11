import RequestProject.FamDec.All

/-! Auditor's check file for Lean piece C31 (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C31_theorem_36_the_family_decomposition.md`: (M1) the three equations;
(M2) by `rfl`; (M3) support and `L 0`; (M4) the permutation; three small values of `L` and `m`
by `decide` (kernel); (P1), (P2); (D1), (D2), (D3) under the hypotheses of C30 (A1); Lemma 3.7;
(Z1) over ℤ_[2]; then `#print axioms`. -/

open DPLattice WeylFilt Doubling Twist Lemma35 Tensor2 Lemma35b Cocycle Lift2 Filt Step36 FamDec

-- (M1) the three equations.
example (l : ℕ) : FamDec.Vdot 0 = [1] ∧ FamDec.Vdot (2 * l + 1) = [2 * l + 2] ∧
    FamDec.Vdot (2 * l + 2) = [2 * l + 1, 2 * l + 1] ++ (FamDec.Vdot l).map (fun ν => 2 * ν + 1) :=
  ⟨Vdot_zero, Vdot_odd l, Vdot_even l⟩

-- (M2) by definition.
example (n lam : ℕ) : FamDec.L 0 = [0] ∧ FamDec.L (n + 1) = (FamDec.L n).flatMap FamDec.Vdot ∧
    FamDec.m lam n = (FamDec.L n).count lam := ⟨rfl, rfl, rfl⟩

-- Hand values: Vdot 2 = [1, 1] ++ [2·1+1] = [1, 1, 3], and L 3 = Vdot 2 = [1, 1, 3].
example : FamDec.Vdot 2 = [1, 1, 3] := by
  rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, Vdot_even, Vdot_zero]; rfl
example : FamDec.L 3 = [1, 1, 3] := by
  have e1 : FamDec.Vdot 1 = [2] := Vdot_odd 0
  have e2 : FamDec.Vdot 2 = [1, 1, 3] := by
    rw [show (2 : ℕ) = 2 * 0 + 2 from rfl, Vdot_even, Vdot_zero]; rfl
  simp [FamDec.L, Vdot_zero, e1, e2]

-- (M3).
example (n : ℕ) (hn : 1 ≤ n) (lam : ℕ) (h : lam ∈ FamDec.L n) :
    1 ≤ lam ∧ lam ≤ n ∧ lam % 2 = n % 2 := M3 n hn lam h
example (lam : ℕ) : lam ∈ FamDec.L 0 ↔ lam = 0 := mem_L_zero lam

-- (M4).
example (n : ℕ) : List.Perm (FamDec.L n)
    ((List.range (n + 1)).flatMap (fun lam => List.replicate (FamDec.m lam n) lam)) := M4 n

-- (P1), (P2) over any commutative ring.
example {A : Type} [CommRing A] {L₁ L₂ : List (DPLattice A)} (h : L₁.Perm L₂) :
    Nonempty (Doubling.Iso (dsumList L₁) (dsumList L₂)) := P1 h
example {A : Type} [CommRing A] (f : ℕ → DPLattice A) (g : ℕ → List (DPLattice A))
    (L : List ℕ) (h : ∀ lam ∈ L, Nonempty (Doubling.Iso (f lam) (dsumList (g lam)))) :
    Nonempty (Doubling.Iso (dsumList (L.map f)) (dsumList (L.flatMap g))) := P2 f g L h

section D
variable {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [CharZero A] [OddUnits A]

-- (D1).
example (φ : A →+* B) (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A)
    (h2 : (2 : B) = 0) (lam : ℕ) :
    Nonempty (Doubling.Iso (tensorV (Filt.T A lam)) (dsumList ((FamDec.Vdot lam).map (Filt.T A)))) :=
  D1 h1 hk h3 hU h2 lam

-- (D2) Theorem 3.6, list form.
example (φ : A →+* B) (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A)
    (h2 : (2 : B) = 0) (n : ℕ) :
    Nonempty (Doubling.Iso (tpow A n) (dsumList ((FamDec.L n).map (Filt.T A)))) :=
  D2 h1 hk h3 hU h2 n

-- (D3) Theorem 3.6, multiplicity form.
example (φ : A →+* B) (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A)
    (h2 : (2 : B) = 0) (n : ℕ) : Nonempty (Doubling.Iso (tpow A n)
    (dsumList ((List.range (n + 1)).flatMap
      (fun lam => List.replicate (FamDec.m lam n) (Filt.T A lam))))) :=
  D3 h1 hk h3 hU h2 n
end D

-- Lemma 3.7.
example (n : ℕ) (hn : 1 ≤ n) : FamDec.m 0 n = 0 ∧ FamDec.m n n = 1 :=
  ⟨L1 n hn, L2 n hn⟩
example (n : ℕ) (hn : 1 ≤ n) (ho : n % 2 = 1) : FamDec.m 1 n = 2 ^ ((n - 1) / 2) := L3 n hn ho
example (n : ℕ) (hn : 1 ≤ n) (he : n % 2 = 0) : FamDec.m 2 n = 2 ^ ((n - 2) / 2) := L4 n hn he

-- (Z1).
example : (∀ lam : ℕ, Nonempty (Doubling.Iso (tensorV (Filt.T ℤ_[2] lam))
      (dsumList ((FamDec.Vdot lam).map (Filt.T ℤ_[2]))))) ∧
    (∀ n : ℕ, Nonempty (Doubling.Iso (tpow ℤ_[2] n) (dsumList ((FamDec.L n).map (Filt.T ℤ_[2]))))) ∧
    (∀ n : ℕ, Nonempty (Doubling.Iso (tpow ℤ_[2] n)
      (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate (FamDec.m lam n) (Filt.T ℤ_[2] lam)))))) := FamDec.Z1

#print axioms FamDec.Vdot_even
#print axioms FamDec.M3
#print axioms FamDec.M4
#print axioms FamDec.P1
#print axioms FamDec.P2
#print axioms FamDec.D1
#print axioms FamDec.D2
#print axioms FamDec.D3
#print axioms FamDec.L1
#print axioms FamDec.L2
#print axioms FamDec.L3
#print axioms FamDec.L4
#print axioms FamDec.Z1
