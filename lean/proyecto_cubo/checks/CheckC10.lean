import RequestProject.Deficit.All

/-! Auditor's check file for Lean piece C10 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C10_deficit_law.md` and closed by `rfl`; the main statements
restated by hand with the definitions unfolded and closed by the certified theorems; then
`#print axioms`. -/

open Deficit Finset

-- Encodings (Setting)
example (f g : Finset ℕ → ℤ) (Δ : Finset ℕ) :
    starMul f g Δ = ∑ Δ₁ ∈ Δ.powerset, f Δ₁ * g (Δ \ Δ₁) := rfl
example (I Δ : Finset ℕ) : a I 0 Δ = -(if Δ = ∅ then 1 else 0) := rfl
example (I Δ : Finset ℕ) (t : ℕ) :
    a I (t + 1) Δ = (∑ Δ₁ ∈ Δ.powerset, a I t Δ₁ * a I t (Δ \ Δ₁)) -
      (if t ∈ I then 1 else 0) * (if t ∈ Δ then 1 else 0) * a I t (Δ \ {t}) := rfl
example (I Δ : Finset ℕ) : c I 0 Δ = if Δ = ∅ then 1 else 0 := rfl
example (I Δ : Finset ℕ) (h : ℕ) :
    c I (h + 1) Δ = -(1 / 2) * (∑ Δ₁ ∈ Δ.powerset, c I h Δ₁ * c I h (Δ \ Δ₁)) -
      (if h ∈ I then 1 else 0) * (if h ∈ Δ then 1 else 0) * c I h (Δ \ {h}) := rfl
example (I : Finset ℕ) (k : ℕ) (α : ℤ) (i : ℕ) (D D' : Finset ℕ) :
    Mc I k α i D D' = -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ k + ((∑ t ∈ D \ D', 2 ^ t : ℕ) : ℤ)) * (a I k (D \ D') : ℚ) *
      ∏ d ∈ (Ico (∑ t ∈ D, 2 ^ t) ((∑ t ∈ D', 2 ^ t) + 2 ^ k) : Finset ℕ),
        (2 : ℚ) ^ α * ((i : ℚ) + (d : ℚ)) := rfl

-- Lemma 4.5, the nonempty case, written with k − |Δ| − min Δ
example {k : ℕ} (hk : 1 ≤ k) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {Δ : Finset ℕ} (hΔ : Δ ⊆ I)
    (h : Δ.Nonempty) : a I k Δ ≠ 0 ∧ (padicValInt 2 (a I k Δ) : ℤ) = (k : ℤ) - Δ.card - Δ.min' h :=
  ⟨(lemma_4_5 hk hI hΔ).1, lemma_4_5_nonempty hk hI hΔ h⟩

-- (A3) general form
example (I : Finset ℕ) (t : ℕ) (Δ : Finset ℕ) (h : Δ.Nonempty) (hΔI : Δ ⊆ I) (ht : Δ.max' h < t) :
    a I t Δ ≠ 0 ∧ padicValInt 2 (a I t Δ) = t - Δ.card - Δ.min' h :=
  ⟨(A3_deficit I t Δ h hΔI ht).2.1, (A3_deficit I t Δ h hΔI ht).2.2⟩

-- (B1)
example (I : Finset ℕ) (h : ℕ) (Δ : Finset ℕ) :
    c I h Δ = -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ h) * 2 ^ (∑ t ∈ Δ, 2 ^ t) * (a I h Δ : ℚ) :=
  B1_rescaling I h Δ

-- (C2) the valuation of the closed form
example {k : ℕ} (hk : 1 ≤ k) {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) {α : ℤ} (hα : 1 ≤ α) (i : ℕ)
    {D D' : Finset ℕ} (hD' : D' ⊆ D) (hD : D ⊆ I) (hi : 0 < i + Rulers.oE D) :
    (∃ z : ℤ, z ≠ 0 ∧ Mc I k α i D D' = z) ∧
      padicValRat 2 (Mc I k α i D D') = 1 - (2 : ℤ) ^ k + Rulers.oE (D \ D') +
        Rulers.delta k (D \ D') +
        ∑ d ∈ Ico (Rulers.oE D) (Rulers.oE D' + 2 ^ k), (α + (padicValNat 2 (i + d) : ℤ)) :=
  C2_integrality_valuation hk hI hα i hD' hD hi

#print axioms A1_support
#print axioms A2_const
#print axioms A3_deficit
#print axioms lemma_4_5
#print axioms lemma_4_5_empty
#print axioms lemma_4_5_nonempty
#print axioms lemma_4_5_indep
#print axioms A4_subadditivity
#print axioms A5_q1
#print axioms A5_q2
#print axioms B1_rescaling
#print axioms C1_window
#print axioms C2_integrality_valuation
