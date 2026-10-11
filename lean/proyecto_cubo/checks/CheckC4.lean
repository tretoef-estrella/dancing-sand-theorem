import RequestProject.GoldenMatching.All

/-! Auditor's check file for Lean piece C4 (Grepy Escribano, 6 Oct 2026).
Encodings written out by hand from `C4_golden_matching.md` and closed by `rfl`; statements
restated by hand and closed by the certified theorems; then `#print axioms`. -/

open GoldenMatching Rulers Finset

-- Encodings
example (s p g : ℕ) :
    IsGoldenImage s p g ↔ (g = p ∨ ∃ j < s, p / 2 ^ j = 2 ^ (s - j) - 1 ∧ g = p % 2 ^ j) := Iff.rfl
example (I D : Finset ℕ) : rank I D = (I.powerset.filter (fun D' => oE D' < oE D)).card := rfl
example (I : Finset ℕ) (r : ℕ) : Lr I r = I.powerset.filter (fun D => 2 ^ I.card - r ≤ rank I D) := rfl
example (I : Finset ℕ) (r : ℕ) : Fr I r = I.powerset.filter (fun D => rank I D < r) := rfl
example (k : ℕ) (I a b : Finset ℕ) : IsGoldenArrow k I a b ↔ (b ⊆ a ∧ gamma k I (a \ b) = 0) :=
  Iff.rfl
example (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ : ℕ) (a b : Finset ℕ) :
    cHat k I α μ a b = ruler k I α μ a - ruler k I α (μ + 2 ^ k) b + gamma k I (a \ b) := rfl
example (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ r : ℕ) :
    U k I α μ r = ∑ D ∈ Lr I r, (ruler k I α μ D - ruler k I α (μ + 2 ^ k) (I \ D)) := rfl

-- Theorem A: rows N − r, …, N − 1; columns 0, …, r − 1; exactly one golden bijection
example (s r : ℕ) (hr : r ≤ 2 ^ s) :
    ∃ β : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ) ≃ (range r : Finset ℕ),
      ∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β p) :=
  (theorem_A s r hr).1
example (s r : ℕ) (hr : r ≤ 2 ^ s)
    (β β' : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ) ≃ (range r : Finset ℕ))
    (hβ : ∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β p))
    (hβ' : ∀ p : (Ico (2 ^ s - r) (2 ^ s) : Finset ℕ), IsGoldenImage s p (β' p)) :
    ∀ p, β p = β' p :=
  (theorem_A s r hr).2 β β' hβ hβ'

-- Theorem B: exactly one golden bijection L_r → F_r
example (k : ℕ) (I : Finset ℕ) (hI : ∀ t ∈ I, t < k) (r : ℕ) (hr : r ≤ 2 ^ I.card) :
    (∃ β : Lr I r ≃ Fr I r, ∀ D : Lr I r, ((β D : Finset ℕ) ⊆ D ∧ gamma k I ((D : Finset ℕ) \ β D) = 0))
      ∧ ∀ β β' : Lr I r ≃ Fr I r, (∀ D : Lr I r, IsGoldenArrow k I D (β D)) →
        (∀ D : Lr I r, IsGoldenArrow k I D (β' D)) → ∀ D, β D = β' D :=
  theorem_B k hI r hr

-- Lemma C1
example (I D : Finset ℕ) (hD : D ⊆ I) : oE (I \ D) = oE I - oE D := lemma_C1_oE hD
example (I D : Finset ℕ) (hD : D ⊆ I) : rank I (I \ D) = 2 ^ I.card - 1 - rank I D :=
  lemma_C1_rank hD
example (I : Finset ℕ) (r : ℕ) :
    Set.BijOn (fun D => I \ D) (Lr I r : Set (Finset ℕ)) (Fr I r : Set (Finset ℕ)) :=
  lemma_C1_bijOn I r

-- Lemma C2: any bijection, no support condition
example (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ r : ℕ) (β : Lr I r ≃ Fr I r) :
    ∑ D : Lr I r, cHat k I α μ D (β D) =
      U k I α μ r + ∑ D : Lr I r, (gamma k I ((D : Finset ℕ) \ β D) : ℤ) :=
  lemma_C2 k I α μ r β

-- Corollary D: every orders e, f; exact valuation r·C + U(r)
example (k : ℕ) (I : Finset ℕ) (hI : ∀ t ∈ I, t < k) (α : ℤ) (μ : ℕ) (C : ℤ)
    (M : Finset ℕ → Finset ℕ → ℤ)
    (hS : ∀ a b, a ⊆ I → b ⊆ I → ¬ b ⊆ a → M a b = 0)
    (hH : ∀ a b, b ⊆ a → a ⊆ I →
      ∃ n : ℕ, (n : ℤ) = C + cHat k I α μ a b ∧ 2 ^ n ∣ M a b ∧ ¬ 2 ^ (n + 1) ∣ M a b)
    (r : ℕ) (hr : r ≤ 2 ^ I.card) (e : Fin r ≃ Lr I r) (f : Fin r ≃ Fr I r) :
    ∃ n : ℕ, (n : ℤ) = r * C + U k I α μ r ∧
      2 ^ n ∣ (Matrix.of fun i j => M (e i) (f j)).det ∧
      ¬ 2 ^ (n + 1) ∣ (Matrix.of fun i j => M (e i) (f j)).det :=
  let ⟨n, h1, h2, h3, _⟩ := corollary_D k hI α μ C M hS hH r hr e f
  ⟨n, h1, h2, h3⟩

#print axioms theorem_A
#print axioms theorem_B
#print axioms lemma_C1_oE
#print axioms lemma_C1_lt
#print axioms lemma_C1_rank
#print axioms lemma_C1_bijOn
#print axioms lemma_C2
#print axioms corollary_D
