import RequestProject.Split.All

/-! Auditor's check file for Lean piece C12 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C12_split_move.md` and closed by `rfl`; the main statements
restated by hand with the systems unfolded and closed by the certified theorems; then
`#print axioms`. -/

open Payment Split DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι] {N : ι → Type*}
  [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] {S : Type*} [Fintype S] [LinearOrder S]

-- Floors of the two models
example (fl : ι → ℕ) (i : ι) (e e' : Fin 2) : flVΦ fl (i, e, e') = 2 * fl i + e.val + e'.val := rfl
example (fl : ι → ℕ) (i : ι) : flΨ fl (i, 0) = 2 * fl i := rfl
example (fl : ι → ℕ) (i : ι) : flΨ fl (i, 1) = 2 * fl i + 1 := rfl
example (fl : ι → ℕ) (i : ι) : flΨ fl (i, 2) = 2 * fl i + 1 := rfl
example (fl : ι → ℕ) (i : ι) : flΨ fl (i, 3) = 2 * fl i + 2 := rfl

-- The split payments
example (p : S → ℕ → A) (s : S) (f : ℕ) :
    pSp p (toLex (s, 0)) f = -(p s (2 * f) * p s (2 * f + 1)) := rfl
example (p : S → ℕ → A) (s : S) (f : ℕ) :
    pSp p (toLex (s, 1)) f = -(p s (2 * f + 1) * p s (2 * f + 2)) := rfl

-- The split couplings, case by case (q = smaller slot, q' = larger slot)
example (p : S → ℕ → A) (κ : S → S → ℕ → A) (s' : S) (f : ℕ) :
    κSp p κ (toLex (s', 1)) (toLex (s', 0)) f = -p s' (2 * f + 1) := by
  simp [κSp]
example (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (h : s' < u) (f : ℕ) :
    κSp p κ (toLex (u, 1)) (toLex (s', 0)) f = -κ u s' (2 * f + 1) := by
  simp [κSp, h, ne_of_gt h]
example (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (h : s' < u) (f : ℕ) :
    κSp p κ (toLex (u, 0)) (toLex (s', 0)) f = -(p s' (2 * f + 1) * κ u s' (2 * f)
      + κ u s' (2 * f + 1) * p u (2 * f)
      + ∑ s ∈ Finset.univ.filter (fun s => s' < s ∧ s < u), κ s s' (2 * f + 1) * κ u s (2 * f)) := by
  simp [κSp, h]
example (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (h : s' < u) (f : ℕ) :
    κSp p κ (toLex (u, 1)) (toLex (s', 1)) f = -(p s' (2 * f + 2) * κ u s' (2 * f + 1)
      + κ u s' (2 * f + 2) * p u (2 * f + 1)
      + ∑ s ∈ Finset.univ.filter (fun s => s' < s ∧ s < u),
          κ s s' (2 * f + 2) * κ u s (2 * f + 1)) := by
  simp [κSp, h]
-- no coupling from a slot C to a slot A
example (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) :
    κSp p κ (toLex (u, 0)) (toLex (s', 1)) f = 0 := by
  simp [κSp]

-- (A2)
example (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) :
    theta ∘ₗ FVΦ F = FΨ F ∘ₗ (theta : (⨁ q, NVΦ N q) →ₗ[A] _) := A2_theta_comp_F F

-- (A3), every c
example (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A)
    (c : A) :
    Nonempty (((⨁ q : S × (ι × Fin 2 × Fin 2), N q.2.1) ⧸
        LinearMap.range (c • G (flVΦ fl) (FVΦ F) p κ)) ≃ₗ[A]
      ((⨁ q : S × (ι × Fin 4), N q.2.1) ⧸ LinearMap.range (c • G (flΨ fl) (FΨ F) p κ))) :=
  A3_coker fl F p κ c

-- Theorem B, every c
example (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A)
    (c : A) :
    Nonempty (((⨁ q : S × (ι × Fin 4), N q.2.1) ⧸ LinearMap.range (c • G (flΨ fl) (FΨ F) p κ))
      ≃ₗ[A] ((⨁ q : S × ι, N q.2) ⧸ c • (⊤ : Submodule A (⨁ q : S × ι, N q.2))) ×
        ((⨁ q : S × ι, N q.2) ⧸ c • (⊤ : Submodule A (⨁ q : S × ι, N q.2))) ×
        ((⨁ q : Lex (S × Fin 2) × ι, N q.2) ⧸
          LinearMap.range (c • (2 : A) • G fl F (pSp p) (κSp p κ)))) :=
  theorem_B fl F p κ c

-- Proposition 4.2 (c = 1), for the tensor model
example (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    Nonempty (((⨁ q : S × (ι × Fin 2 × Fin 2), N q.2.1) ⧸
        LinearMap.range (G (flVΦ fl) (FVΦ F) p κ)) ≃ₗ[A]
      ((⨁ q : Lex (S × Fin 2) × ι, N q.2) ⧸
        LinearMap.range ((2 : A) • G fl F (pSp p) (κSp p κ)))) :=
  corollary_B1_VΦ fl F p κ

#print axioms A1_theta_thetaInv
#print axioms A1_thetaInv_theta
#print axioms A2_theta_comp_F
#print axioms A3_thetaS_comp_G
#print axioms A3_coker
#print axioms theorem_B
#print axioms corollary_B1
#print axioms corollary_B1_VΦ
#print axioms corollary_B2
