import RequestProject.Rulers.All

/-! Auditor's check file for Lean piece C3 (Grepy Escribano, 6 Oct 2026).
First the encodings, written out by hand from `C3_rulers_gold_clocks.md` and closed by `rfl`;
then the statements, restated by hand and closed by the certified theorems; then `#print axioms`. -/

open Rulers Finset

-- Encodings, by hand from the file's *Setting*
example (x : ℕ) : s2 x = (Nat.digits 2 x).count 1 := rfl
example (x : ℕ) : v2 x = padicValNat 2 x := rfl
example (a b : ℕ) : kappa a b = (s2 a : ℤ) + s2 b - s2 (a + b) := rfl
example (x : ℕ) : phi x = (x : ℤ) + v2 x := rfl
example (E : Finset ℕ) : oE E = ∑ t ∈ E, 2 ^ t := rfl
example (k : ℕ) (I : Finset ℕ) (t : ℕ) :
    next k I t = minOr k ((insert k I).filter (fun u => t < u)) := rfl
example (k : ℕ) (I : Finset ℕ) (t : ℕ) : h k I t = next k I t - t := rfl
example (k : ℕ) (E : Finset ℕ) (hE : E.Nonempty) : minOr k E = E.min' hE := by
  simp [minOr, hE]
example (k : ℕ) : minOr k ∅ = k := rfl
example (k : ℕ) (I : Finset ℕ) : lam k I + 1 = 2 ^ k + oE I := by
  unfold lam; have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
example (k : ℕ) (Δ : Finset ℕ) (hΔ : Δ ≠ ∅) :
    delta k Δ = (k : ℤ) - Δ.card - minOr k Δ := by simp [delta, hΔ]
example (k : ℕ) (I Δ : Finset ℕ) (hΔ : Δ ≠ ∅) :
    gamma k I Δ = ∑ u ∈ (I \ Δ).filter (fun u => minOr k Δ < u), h k I u := by
  simp [gamma, hΔ]
example (k : ℕ) (I : Finset ℕ) (α : ℤ) (μ : ℕ) (E : Finset ℕ) :
    ruler k I α μ E = ∑ t ∈ E, ((h k I t : ℤ) - α * 2 ^ t) - kappa μ (oE E) := rfl
example (k : ℕ) (I : Finset ℕ) (α : ℤ) (E : Finset ℕ) :
    rulerSharp k I α E = ∑ t ∈ E, ((h k I t : ℤ) - α * 2 ^ t) - kappa (2 ^ k - 1) (oE E) := rfl
example (k : ℕ) (I D : Finset ℕ) (i : ℕ) :
    clock k I i D = phi (xi k I D) + kappa (i + oE D - 1) (xi k I D)
      + ∑ t ∈ D, (h k I t : ℤ) := by simp [clock, hSum]
example (k : ℕ) (I D : Finset ℕ) (m : ℕ) :
    xD k I m D = ruler k I 1 m D - ruler k I 1 (m + 2 ^ k) (I \ D) := rfl

-- Lemma 5.0
example (k : ℕ) (I D : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hD : D ⊆ I) :
    1 ≤ (2 : ℤ) ^ k + oE I - 2 * oE D := by
  have := lemma_5_0_xi hI hD; omega

-- Lemma 5.1 (a) and (b)
example (k : ℕ) (I Δ : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hΔ : Δ ⊆ I) :
    delta k Δ = ∑ t ∈ Δ, ((h k I t : ℤ) - 1) + gamma k I Δ := lemma_5_1_a hI hΔ
example (k : ℕ) (I Δ : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hΔ : Δ ⊆ I) :
    gamma k I Δ = 0 ↔ Δ = ∅ ∨ Δ = I.filter (fun t => minOr k Δ ≤ t) := lemma_5_1_b hI hΔ

-- Legendre sums
example (μ x y : ℕ) (hxy : x ≤ y) :
    (∑ d ∈ Ico x y, (padicValNat 2 (μ + 1 + d) : ℤ)) = ((y : ℤ) - x) - s2 (μ + y) + s2 (μ + x) :=
  legendre_sum_shift μ x y hxy
example (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    (∑ d ∈ Ico x y, (padicValNat 2 d : ℤ)) = ((y : ℤ) - x) - s2 (y - 1) + s2 (x - 1) :=
  legendre_sum x y hx hxy

-- Proposition 5.2: sum over d = o_a, …, o_b + K − 1 of α + v_2(i + d); m = i − 1
example (k : ℕ) (I a b : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hba : b ⊆ a) (ha : a ⊆ I)
    (α : ℤ) (hα : 1 ≤ α) (i : ℕ) (hi : 1 ≤ i) :
    1 - (2 : ℤ) ^ k + oE (a \ b) + delta k (a \ b) +
        ∑ d ∈ Ico (oE a) (oE b + 2 ^ k), (α + (padicValNat 2 (i + d) : ℤ)) =
      α * 2 ^ k + kappa (i - 1) (2 ^ k) + ruler k I α (i - 1) a -
        ruler k I α (i - 1 + 2 ^ k) b + gamma k I (a \ b) :=
  proposition_5_2 hI hba ha α hα i hi

-- Proposition 5.3: α = 1, i ≥ 1, every dancer D (the empty one included)
example (k : ℕ) (I D : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hD : D ⊆ I) (i : ℕ) (hi : 1 ≤ i) :
    clock k I i D = k + 2 ^ k + kappa (i - 1) (2 ^ k)
      + (ruler k I 1 (i - 1) D - ruler k I 1 (i - 1 + 2 ^ k) (I \ D)) :=
  proposition_5_3 hI hD i hi

-- Proposition 5.4 (a), (b), (c)
example (k : ℕ) (I E : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hE : E ⊆ I) (hne : E.Nonempty) :
    kappa (2 ^ k - 1) (oE E) = (k : ℤ) - E.min' hne := by
  have := proposition_5_4_a hI hE
  rwa [dif_neg (nonempty_iff_ne_empty.1 hne)] at this
example (k : ℕ) (I : Finset ℕ) (hI : ∀ t ∈ I, t < k) :
    kappa (2 ^ k - 1) (oE ∅) = 0 := by
  have := proposition_5_4_a hI (empty_subset I); simpa using this
example (k : ℕ) (I D b : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hDne : D ≠ ∅) (hD : D ⊆ I)
    (hbD : b ⊆ D) (α : ℤ) (hα : 1 ≤ α) :
    1 - (2 : ℤ) ^ k + oE (D \ b) + delta k (D \ b) +
        ∑ d ∈ Ico (oE D) (oE b + 2 ^ k), (α + (padicValNat 2 d : ℤ)) =
      α * 2 ^ k + rulerSharp k I α D - rulerSharp k I α b + gamma k I (D \ b) :=
  proposition_5_4_b hI hDne hD hbD α hα
example (k : ℕ) (I D : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hDne : D ≠ ∅) (hD : D ⊆ I) :
    clock k I 0 D = k + 2 ^ k + (rulerSharp k I 1 D - rulerSharp k I 1 (I \ D)) :=
  proposition_5_4_c hI hDne hD

#print axioms lemma_5_0_xi
#print axioms lemma_5_0_sdiff
#print axioms lemma_5_1_a
#print axioms lemma_5_1_b
#print axioms legendre_sum_shift
#print axioms legendre_sum
#print axioms proposition_5_2
#print axioms proposition_5_3
#print axioms proposition_5_4_a
#print axioms proposition_5_4_b
#print axioms proposition_5_4_c
