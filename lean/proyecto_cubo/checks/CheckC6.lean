import RequestProject.Houses.All

/-! Auditor's check file for Lean piece C6 (Grepy Escribano, 6 Oct 2026).
Encodings written out by hand from `C6_houses_windows_penalties.md` and closed by `rfl`; the main
statements restated by hand and closed by the certified theorems; then `#print axioms`. -/

open Houses Finset Rulers

-- Encodings (Setting and Part B of the file)
example (u x : ℕ) : bit u x = x / 2 ^ u % 2 := rfl
example (u x : ℕ) : Houses.r u x = v2 (x / 2 ^ u + 1) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (E : Finset ℕ) : RH I k ℓ α E = ruler k I α ℓ E := rfl
example (k ℓ : ℕ) (E : Finset ℕ) : JH k ℓ E = if 2 ^ k ≤ ℓ + oE E then 1 else 0 := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (D : Finset ℕ) :
    xH I k ℓ α D = RH I k ℓ α D - RH I k ℓ α (I \ D) := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (a b : Finset ℕ) :
    cHatH I k ℓ α a b = RH I k ℓ α a - RH I k ℓ α b + gamma k I (a \ b) := rfl
example (I : Finset ℕ) (k ℓ t : ℕ) : kap I k ℓ t =
    if bit t ℓ = 1 then min (Houses.r t ℓ) (h k I t) else 1 + min (Houses.r (t + 1) ℓ) (h k I t - 1) := rfl
example (I : Finset ℕ) (k ℓ t : ℕ) : sat I k ℓ t = if kap I k ℓ t = h k I t then 1 else 0 := rfl
example (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ) (t : ℕ) : tau I k ℓ α t =
    (h k I t : ℤ) - α * 2 ^ t - (if bit t ℓ = 1 then (kap I k ℓ t : ℤ) else 0) := rfl
example (ℓ u : ℕ) (E : Finset ℕ) :
    cin ℓ u E = if 2 ^ u ≤ ℓ % 2 ^ u + oE E % 2 ^ u then 1 else 0 := rfl
example (I : Finset ℕ) (k ℓ t : ℕ) (E : Finset ℕ) :
    car I k ℓ t E = ((Ico t (next k I t)).filter (fun u => cin ℓ (u + 1) E = 1)).card := rfl

-- Lemma A (Lemma 7.5) and its last claim
example {I : Finset ℕ} {k : ℕ} (hI : ∀ t ∈ I, t < k) (α : ℤ) (μ : ℕ) {E : Finset ℕ} (hE : E ⊆ I) :
    ruler k I α μ E = ruler k I α (μ % 2 ^ k) E
      - (v2 (μ / 2 ^ k + 1) : ℤ) * ((if 2 ^ k ≤ μ % 2 ^ k + oE E then 1 else 0 : ℕ) : ℤ) :=
  lemma_A hI α μ hE
example (k m : ℕ) : Xor' (v2 (m / 2 ^ k + 1) = 0) (v2 ((m + 2 ^ k) / 2 ^ k + 1) = 0) :=
  lemma_A_exactly_one_zero k m

-- Lemma A′ (the cell is a penalty cell)
example {I : Finset ℕ} {k : ℕ} (hI : ∀ t ∈ I, t < k) (α : ℤ) (m : ℕ) {a b : Finset ℕ}
    (ha : a ⊆ I) (hb : b ⊆ I) :
    GoldenMatching.cHat k I α m a b = cHatH I k (m % 2 ^ k) α a b
      - (Houses.r k m : ℤ) * JH k (m % 2 ^ k) a + (Houses.r k (m + 2 ^ k) : ℤ) * JH k (m % 2 ^ k) b :=
  lemma_A'_cost hI α m ha hb

-- Lemma B (Lemma 7.6): (B5) and (B6)
example {I : Finset ℕ} {k ℓ : ℕ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ) {E : Finset ℕ}
    (hE : E ⊆ I) :
    ruler k I α ℓ E = ∑ t ∈ E, tau I k ℓ α t
      - ∑ t ∈ I, (kap I k ℓ t : ℤ) * (cin ℓ t E : ℤ) *
          (if (bit t ℓ = 1 ∧ t ∉ E) ∨ (bit t ℓ = 0 ∧ t ∈ E) then 1 else 0) :=
  lemma_B5 hI hℓ α hE
example {I : Finset ℕ} {k ℓ : ℕ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) {E : Finset ℕ}
    (hE : E ⊆ I) : JH k ℓ E = cin ℓ k E := lemma_B6 hI hℓ hE

-- Lemma C (Lemma 7.7): (C3), (C5) and (C6)
example {I : Finset ℕ} {k ℓ c : ℕ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hne : I.Nonempty)
    (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    JH k ℓ D₀ = (if bit c ℓ = 1 then 1 else 0) * sat I k ℓ c * JH c (ℓ % 2 ^ c) D₀ :=
  lemma_C3 hI hℓ hne hc hD
example {I : Finset ℕ} {k c : ℕ} (hI : ∀ t ∈ I, t < k) (hne : I.Nonempty) (hc : c = I.max' hne)
    {Δ : Finset ℕ} (hΔ : Δ ⊆ I) (hcΔ : c ∉ Δ) (hΔne : Δ ≠ ∅) :
    gamma k I Δ = gamma c (I.erase c) Δ + (k - c) := lemma_C5_not_mem hI hne hc hΔ hcΔ hΔne
example {I : Finset ℕ} {k ℓ c : ℕ} (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (α : ℤ)
    (hne : I.Nonempty) (hc : c = I.max' hne) {D₀ : Finset ℕ} (hD : D₀ ⊆ I.erase c) :
    xH I k ℓ α D₀ = xH (I.erase c) c (ℓ % 2 ^ c) α D₀
      + (-tau I k ℓ α c - (if bit c ℓ = 1 then (kap I k ℓ c : ℤ) else 0) * JH c (ℓ % 2 ^ c) D₀
        + (if bit c ℓ = 0 then (kap I k ℓ c : ℤ) else 0) * JH c (ℓ % 2 ^ c) (I.erase c \ D₀)) :=
  lemma_C6 hI hℓ α hne hc hD

#print axioms lemma_A0_antisymm
#print axioms lemma_A0_upset
#print axioms lemma_A
#print axioms lemma_A_exactly_one_zero
#print axioms lemma_A'_cost
#print axioms lemma_A'_clock
#print axioms lemma_B1
#print axioms lemma_B2
#print axioms lemma_B3
#print axioms lemma_B4
#print axioms lemma_B5
#print axioms lemma_B6
#print axioms lemma_C1
#print axioms lemma_C2
#print axioms lemma_C3
#print axioms lemma_C4
#print axioms lemma_C5_not_mem
#print axioms lemma_C5_mem
#print axioms lemma_C6
#print axioms lemma_C7
