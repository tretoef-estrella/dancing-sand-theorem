import RequestProject.ZeroSmith.All

/-! Auditor's check file for Lean piece C49c: the Smith form and the cokernel of Ξ at c = 0,
Theorem 10.16 for every c, Corollary 10.17 for every l, j (Grepy Escribano, 10 Oct 2026).
Restated by hand from `C49c_smith_form_and_cokernel_at_zero.md`; then `#print axioms`. -/

open FormalOps FormalDance Windows DanceSmith Matrix ZeroSmith

-- the new definition, by `rfl`
example (ds : List Bool) (α : ℕ)
    (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ) :
    Data0 ds α M' = ∀ s s' : Fin (2 ^ Dance.mCount ds),
      (¬ Dset ds s' ⊆ Dset ds s → M' s s' = 0) ∧ (Dset ds s = ∅ → M' s s' = 0) ∧
      (Dset ds s' ⊆ Dset ds s → Dset ds s ≠ ∅ → M' s s' ≠ 0 ∧ ∃ n : ℕ,
        (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
          (α : ℤ) (Dset ds s) (Dset ds s') ∧ 2 ^ n ∣ M' s s' ∧ ¬ 2 ^ (n + 1) ∣ M' s s') := rfl

-- (G1) C15 (Z3) in general form
example (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅)
    (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ)
    (hM : Data0 ds α M') :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
            (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 2 - j)) ∧
          P * M' * Q = diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then u j * 2 ^ E j else 0) :=
  G1 ds hk α hα hne M' hM

-- (G2)
example (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) :
    Data0 ds α (finalMatrix ℤ ds α 0) := G2 ds hk α hα

-- (Z3) truncation with one zero diagonal entry
example (m N : ℕ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2])
    (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hXY : ∃ R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2],
      ∀ i j, X i j - (Y i j : ℤ_[2]) = 2 ^ N * R i j)
    (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hP : Odd P.det) (hQ : Odd Q.det) (u : ℕ → ℤ)
    (hu : ∀ j, Odd (u j)) (E : ℕ → ℕ) (hE : ∀ j < m, E j < N)
    (h : P * Y * Q = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then u j * 2 ^ E j else 0))
    (hdet : X.det = 0) :
    ∃ P' Q' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * X * Q' = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then (2 : ℤ_[2]) ^ E j
        else 0) :=
  Z3 m N X Y hXY P Q hP hQ u hu E hE h hdet

-- (V5) Smith form of the final matrix of Ξ_0 over ℤ_2
example {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ)
    (hne : Ids (Families.ds l) ≠ ∅) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
        (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l) - 1,
          (E j : ℤ) = (α : ℤ) * 2 ^ (Families.ds l).length +
            yHatS (Families.ds l) α (2 ^ Dance.mCount (Families.ds l) - 2 - j)) ∧
        P * (finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
          (Fin.cast (Smith2.slots_cast (Families.ds l))) * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount (Families.ds l)) =>
            if (j : ℕ) < 2 ^ Dance.mCount (Families.ds l) - 1 then (2 : ℤ_[2]) ^ E j else 0) :=
  V5 hl hα hη z GkZ hG hne

-- (V7) equivalence with the integer final matrix
example {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
        (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧
        (finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
          (Fin.cast (Smith2.slots_cast (Families.ds l))) =
          P * (finalMatrix ℤ (Families.ds l) α 0).map (Int.castRingHom ℤ_[2]) * Q :=
  V7 hl hα hη z GkZ hG

-- (R6) the cokernel at c = 0
example (l α : ℕ) (hl : 1 ≤ l) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α 0) :=
  R6 l α hl hα η hη z B hB

-- (R7) Theorem 10.16 for every l and c
example (l c α : ℕ) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α c) :=
  R7 l c α hα η hη z B hB

-- (C4) coker Ψ_j ≅ coker Σ_⌈j/2⌉, every l, j
example (l j : ℕ) :
    Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1))) ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range
        (FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ))))) :=
  C4 l j

-- (C5) Corollary 10.17, every l, j
example (l j : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)) :=
  C5 l j

#print axioms ZeroSmith.G1
#print axioms ZeroSmith.G2
#print axioms ZeroSmith.Z3
#print axioms ZeroSmith.V4
#print axioms ZeroSmith.V5
#print axioms ZeroSmith.V6
#print axioms ZeroSmith.V7
#print axioms ZeroSmith.R6
#print axioms ZeroSmith.R7
#print axioms ZeroSmith.C4
#print axioms ZeroSmith.C5
