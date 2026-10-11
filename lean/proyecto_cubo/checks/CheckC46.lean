import RequestProject.Smith2.All

/-! Auditor's check file for Lean piece C46: Theorem 10.12 second half, the Smith form over ℤ_2 and
the cokernel (Grepy Escribano, 9 Oct 2026). Restated by hand from
`C46_smith_form_and_cokernel_over_Z2.md`; then `#print axioms`. -/

open Matrix Finset FormalOps FormalDance Smith2 Windows DanceSmith

-- the definitions, by `rfl`
example {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (x : Bf A) (m : ℕ) (f : ℤ) :
    (Smith2.Bf.map φ x).coef m f = φ (x.coef m f) := rfl
example (α c : ℕ) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) (f : ℤ) :
    (XiOpZ α c η ζ).coef 0 f = 2 ^ α * ((f : ℤ_[2]) + c) ∧ (XiOpZ α c η ζ).coef 1 f = η ∧
    (XiOpZ α c η ζ).coef 5 f = ζ 5 f := ⟨rfl, rfl, rfl⟩
example {n : Type} (N : ℕ) (X : Matrix n n ℤ_[2]) (i j : n) :
    trunc N X i j = ((X i j).appr N : ℤ) := rfl

-- (Z1)
example {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ_[2]) (Y : Matrix (Fin n) (Fin n) ℤ) (N : ℕ)
    (hXY : ∃ R : Matrix (Fin n) (Fin n) ℤ_[2], ∀ i j, X i j - (Y i j : ℤ_[2]) = 2 ^ N * R i j)
    (P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd P.det) (hQ : Odd Q.det) (u : ℕ → ℤ)
    (hu : ∀ j, Odd (u j)) (E : ℕ → ℕ) (hE : ∀ j < n, E j < N)
    (h : P * Y * Q = diagonal (fun j : Fin n => u j * 2 ^ E j)) :
    ∃ P' Q' : Matrix (Fin n) (Fin n) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * X * Q' = diagonal (fun j : Fin n => (2 : ℤ_[2]) ^ E j) :=
  Z1 X Y N hXY P Q hP hQ u hu E hE h

-- (G1)
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ)
    (hM : ∀ s s' : Fin (2 ^ Dance.mCount ds),
      (¬ Dset ds s' ⊆ Dset ds s → M' s s' = 0) ∧
      (Dset ds s' ⊆ Dset ds s → M' s s' ≠ 0 ∧
        ∃ n : ℕ, (n : ℤ) = Cst ds α i +
            GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (Dset ds s) (Dset ds s') ∧
          2 ^ n ∣ M' s s' ∧ ¬ 2 ^ (n + 1) ∣ M' s s')) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds,
            (E j : ℤ) = Cst ds α i + yHat ds α i (2 ^ Dance.mCount ds - 1 - j)) ∧
          P * M' * Q = diagonal (fun j : Fin (2 ^ Dance.mCount ds) => u j * 2 ^ E j) :=
  G1 ds hk α i hα hi M' hM

section R
variable {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℤ_[2]} (hη : IsUnit η)
  (ζ : ℕ → ℤ → ℤ_[2])
  (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
    (Bf ℤ_[2]))
  (hG : DanceRel (Families.ds l) 1 (fun _ _ => XiOpZ α c η ζ) GkZ)
include hl hα hc hη hG

-- (R1)
example (GkS : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hS : DanceRel (Families.ds l) 1 (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ) GkS) :
    ∃ P Q : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2], IsUnit P.det ∧ IsUnit Q.det ∧ finalM GkZ = P * finalM GkS * Q :=
  R1 hl hα hc hη ζ GkZ hG GkS hS

-- (R2)
example : ∃ P Q : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      ℤ_[2], IsUnit P.det ∧ IsUnit Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l),
        (E j : ℤ) = Cst (Families.ds l) α c +
          yHat (Families.ds l) α c (2 ^ Dance.mCount (Families.ds l) - 1 - j)) ∧
      P * finalM GkZ * Q =
        diagonal (fun j : Fin (Dance.slots (Families.ds l) 1) => (2 : ℤ_[2]) ^ E j) :=
  R2 hl hα hc hη ζ GkZ hG

-- (R3)
example (B : ℕ) (hB : l + 1 ≤ B) (h : ℕ) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range ((2 : ℤ_[2]) ^ h • FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => XiOpZ α c η ζ : Matrix (Fin 1) (Fin 1) (Bf ℤ_[2])))) ≃ₗ[ℤ_[2]]
      ((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range ((2 : ℤ_[2]) ^ h • FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ)))) :=
  R3 hl hα hc hη ζ GkZ hG B hB h

-- (R4)
example (B : ℕ) (hB : l + 1 ≤ B) :
    ∃ E : ℕ → ℕ, (∀ p < 2 ^ Dance.mCount (Families.ds l),
        (E p : ℤ) = (Families.ds l).length + Cst (Families.ds l) α c +
          yHat (Families.ds l) α c p) ∧
      Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
          LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
            (fun _ _ => XiOpZ α c η ζ : Matrix (Fin 1) (Fin 1) (Bf ℤ_[2])))) ≃ₗ[ℤ_[2]]
        FamilyGroup.SC (Families.ds l) ×
          ((p : Fin (2 ^ Dance.mCount (Families.ds l))) → FamilyGroup.Q (E p))) :=
  R4 hl hα hc hη ζ GkZ hG B hB

-- (R5): coker(Ξ on T(l)) ≅ X^(α)(l, c)
example (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => XiOpZ α c η ζ : Matrix (Fin 1) (Fin 1) (Bf ℤ_[2])))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α c) :=
  R5 hl hα hc hη ζ GkZ hG B hB
end R

#print axioms Smith2.M1
#print axioms Smith2.M2
#print axioms Smith2.M3
#print axioms Smith2.M4
#print axioms Smith2.M5
#print axioms Smith2.Z0
#print axioms Smith2.Z1
#print axioms Smith2.Z2
#print axioms Smith2.G1
#print axioms Smith2.G2
#print axioms Smith2.V1
#print axioms Smith2.V2
#print axioms Smith2.R1
#print axioms Smith2.R2
#print axioms Smith2.R3
#print axioms Smith2.R4
#print axioms Smith2.R5
