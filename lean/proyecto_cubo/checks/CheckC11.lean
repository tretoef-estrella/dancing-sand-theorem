import RequestProject.Payment.All

/-! Auditor's check file for Lean piece C11 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C11_payment_systems_twist.md` and closed by `rfl`; the main
statements restated by hand with the definitions unfolded and closed by the certified theorems;
then `#print axioms`. -/

open Payment DirectSum
open scoped Pointwise

variable {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι] {N : ι → Type*}
  [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] {S : Type*} [Fintype S] [LinearOrder S]

-- The payment system on generators
example (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    G fl F p κ = DirectSum.toModule A (S × ι) (⨁ q : S × ι, N q.2) (fun q =>
      slotEmb A N S q.1 ∘ₗ F ∘ₗ DirectSum.lof A ι N q.2
        + (2 * p q.1 (fl q.2)) • DirectSum.lof A (S × ι) (fun q => N q.2) q
        + ∑ s ∈ Finset.univ.filter (q.1 < ·),
            (2 * κ s q.1 (fl q.2)) • DirectSum.lof A (S × ι) (fun q => N q.2) (s, q.2)) := rfl

-- The double Φ
example (fl : ι → ℕ) (i : ι) (e : Fin 2) : flΦ fl (i, e) = 2 * fl i + e.val := rfl

-- The twisted data
example (p : S → ℕ → A) (s : S) (f : ℕ) : pT p s f = -(p s (2 * f) * p s (2 * f + 1)) := rfl
example (p : S → ℕ → A) (κ : S → S → ℕ → A) (u s' : S) (f : ℕ) :
    κT p κ u s' f = -(p s' (2 * f + 1) * κ u s' (2 * f) + κ u s' (2 * f + 1) * p u (2 * f)
      + ∑ s ∈ Finset.univ.filter (fun s => s' < s ∧ s < u), κ s s' (2 * f + 1) * κ u s (2 * f)) :=
  rfl

-- Theorem A, every c
example (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A)
    (c : A) :
    Nonempty (((⨁ q : S × (ι × Fin 2), N q.2.1) ⧸ LinearMap.range (c • G (flΦ fl) (FΦ F) p κ))
      ≃ₗ[A] ((⨁ q : S × ι, N q.2) ⧸ c • (⊤ : Submodule A (⨁ q : S × ι, N q.2))) ×
        ((⨁ q : S × ι, N q.2) ⧸ LinearMap.range (c • (2 : A) • G fl F (pT p) (κT p κ)))) :=
  theorem_A fl F p κ c

-- Proposition 4.1 (c = 1)
example (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (p : S → ℕ → A) (κ : S → S → ℕ → A) :
    Nonempty (((⨁ q : S × (ι × Fin 2), N q.2.1) ⧸ LinearMap.range (G (flΦ fl) (FΦ F) p κ))
      ≃ₗ[A] ((⨁ q : S × ι, N q.2) ⧸ LinearMap.range ((2 : A) • G fl F (pT p) (κT p κ)))) :=
  corollary_A1 fl F p κ

#print axioms theorem_A
#print axioms corollary_A1
#print axioms corollary_A2
#print axioms blockCokerEquiv
#print axioms map_shear_range
#print axioms projS_comp_G
