import RequestProject.AntitonicFit.All
import RequestProject.AntitonicFit.Examples
import RequestProject.AntitonicFit.Gluing
import RequestProject.AntitonicFit.Antisymmetry

/-! Auditor's check file for Lean piece C1 (Grepy Escribano, 6 Oct 2026).
Statements restated by hand from `C1_antitonic_fits.md`, then closed by the certified theorems;
then `#print axioms` of every main theorem. -/

open AntitonicFit Finset

-- (a) fit is a minimizer (its defining property), not an algorithm
example (N : ℕ) (x : ℕ → ℝ) :
    (∀ i, i + 1 < N → fit N x (i + 1) ≤ fit N x i) ∧
    ∀ y : ℕ → ℝ, (∀ i, i + 1 < N → y (i + 1) ≤ y i) →
      ∑ j ∈ range N, (x j - fit N x j) ^ 2 ≤ ∑ j ∈ range N, (x j - y j) ^ 2 :=
  fit_isFit N x

-- (b) the integer fit: ceilings first, non-negative remainder
example (S : ℤ) (P k : ℕ) :
    blockF S P k = if (k : ℤ) < S % (P : ℤ) then ⌈(S : ℝ) / P⌉ else ⌊(S : ℝ) / P⌋ := rfl

-- (c) cut and strict cut
example (N : ℕ) (x : ℕ → ℝ) (b : ℕ) :
    IsStrictCut N x b ↔
      (0 < b ∧ b < N ∧ ∀ j < N, fit N x j = (if j < b then fit b x j else fit (N - b) (fun i => x (b + i)) (j - b)))
      ∧ fit N x b < fit N x (b - 1) := Iff.rfl

-- (d) Lemma 7.2 (b2): integer x, δ; δ non-increasing and constant on every level set of fit(x)
example (N : ℕ) (x δ : ℕ → ℤ) (hδ : ∀ i, i + 1 < N → (δ (i + 1) : ℝ) ≤ δ i)
    (hc : ∀ i j, i < N → j < N → fit N (fun k => (x k : ℝ)) i = fit N (fun k => (x k : ℝ)) j → δ i = δ j) :
    ∀ j < N, ifit N (x + δ) j = ifit N x j + δ j :=
  (lemma_7_2_b2 (N := N) hδ hc).2.2

-- (e) the example (3,4,3,4), δ = (1,1,0,0): three facts
example : IsCut 4 (toR exX) 2 ∧ ¬ IsStrictCut 4 (toR exX) 2 ∧ ifit 4 (exX + exδ) 1 ≠ ifit 4 exX 1 + exδ 1 :=
  ⟨example_b2_hypothesis_needed.1, example_b2_hypothesis_needed.2.1, example_b2_hypothesis_needed.2.2.2⟩

-- (f) Lemma 7.3: max on the first half, min on the second
example (M : ℕ) (x : ℕ → ℝ) (hx : ∀ j < 2 * M, x (2 * M - 1 - j) = -x j) (j : ℕ) (hj : M ≤ j) (hj2 : j < 2 * M) :
    fit (2 * M) x j = min (-(fit M x (M - 1 - (j - M)))) 0 := by
  have h := lemma_7_3_fit hx j hj2
  simpa [concat, mirror, show ¬ j < M by omega] using h

-- Lemma 7.1
example (N : ℕ) (x z : ℕ → ℝ) (hz : NonIncr N z) :
    (∀ j < N, z j = fit N x j) ↔ ∀ p q, IsLevelInterval N z p q →
      ∑ j ∈ Icc p q, (x j - z j) = 0 ∧ ∀ s, p ≤ s → s ≤ q → ∑ j ∈ Icc p s, (x j - z j) ≤ 0 :=
  lemma_7_1 hz

#print axioms existsUnique_fit
#print axioms lemma_7_1
#print axioms consequence_L
#print axioms consequence_D_cut
#print axioms consequence_D_strict_iff
#print axioms lemma_7_2_a
#print axioms lemma_7_2_b1
#print axioms lemma_7_2_b2
#print axioms lemma_7_2_b3
#print axioms lemma_7_2_b3_b2
#print axioms lemma_7_2_c
#print axioms example_b2_hypothesis_needed
#print axioms A1
#print axioms A2
#print axioms A3
#print axioms lemma_7_3_Z2
#print axioms lemma_7_3_fit
#print axioms lemma_7_3_ifit
