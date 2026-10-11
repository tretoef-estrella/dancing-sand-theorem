import RequestProject.SmithBounds.All

/-! Auditor's check file for Lean piece C2 (Grepy Escribano, 6 Oct 2026).
Statements restated by hand from `C2_smith_bounds.md`, closed by the certified theorems;
then `#print axioms`. -/

open SmithBounds AntitonicFit Finset

-- (a) Lemma A (A1): the determinant of the minor rows A × columns B, bijections inside the support
example {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] (M : Matrix n n R) (π : R)
    (supp : n → n → Prop) (hsupp : ∀ a b, ¬ supp a b → M a b = 0) (c : n → n → ℕ)
    (hc : ∀ a b, π ^ c a b ∣ M a b) {A B : Finset n} {r : ℕ} (e : Fin r ≃ A) (f : Fin r ≃ B) (T : ℕ)
    (hT : ∀ β : A ≃ B, (∀ a : A, supp a (β a)) → T ≤ ∑ a : A, c a (β a)) :
    π ^ T ∣ (M.submatrix (fun i => ((e i : A) : n)) (fun j => ((f j : B) : n))).det :=
  lemma_A1 M π supp hsupp c hc e f T hT

-- (b) Lemma B: p^(v+1) does not divide the sum
example (p : ℤ) (hp : 2 ≤ p) (s : Finset ℕ) (t : ℕ → ℤ) (i₀ : ℕ) (hi : i₀ ∈ s) (v : ℕ)
    (h1 : p ^ v ∣ t i₀) (h2 : ¬ p ^ (v + 1) ∣ t i₀) (h3 : ∀ i ∈ s, i ≠ i₀ → p ^ (v + 1) ∣ t i) :
    ¬ p ^ (v + 1) ∣ ∑ i ∈ s, t i :=
  (lemma_B p hp s t i₀ hi v h1 h2 h3).2

-- (c) Lemma 6.4: the last r positions, ifit of C1, convexity as non-decreasing increments, d 0 = 0
example (N : ℕ) (x d : ℕ → ℤ)
    (hconv : ∀ r, r + 2 ≤ N → d (r + 1) - d r ≤ d (r + 2) - d (r + 1)) (hd0 : d 0 = 0)
    (hdU : ∀ r ≤ N, d r ≤ ∑ j ∈ Ico (N - r) N, x j) :
    ∀ r ≤ N, d r ≤ ∑ j ∈ Ico (N - r) N, ifit N x j :=
  lemma_6_4 (N := N) (x := x) d hconv hd0 hdU

-- Lemma C0: Y(N) = U(N)
example (N : ℕ) (x : ℕ → ℤ) : ∑ j ∈ Ico (N - N) N, ifit N x j = ∑ j ∈ Ico (N - N) N, x j :=
  lemma_C0_total (N := N) (x := x)

-- (d) Theorem U: (U2) pairs j with N - 1 - j; r rows, β injective; the last r values of ŷ
example (N r : ℕ) (arr : ℕ → ℕ → Prop) (c : ℕ → ℕ → ℝ) (yhat v w : ℕ → ℝ)
    (hv : ∀ j, j + 1 < N → v (j + 1) ≤ v j) (hw : ∀ j, j + 1 < N → w (j + 1) ≤ w j)
    (hU2 : ∀ j < N, v j - w (N - 1 - j) = yhat j)
    (hU3 : ∀ a < N, ∀ b < N, arr a b → v a - w b ≤ c a b)
    (Rows : Finset ℕ) (β : ℕ → ℕ) (hR : Rows ⊆ range N) (hcard : Rows.card = r)
    (hinj : Set.InjOn β Rows) (hβ : ∀ a ∈ Rows, β a < N) (harr : ∀ a ∈ Rows, arr a (β a)) :
    ∑ j ∈ Ico (N - r) N, yhat j ≤ ∑ a ∈ Rows, c a (β a) :=
  theorem_U arr c yhat v w hv hw hU2 hU3 ⟨hR, hcard, hinj, hβ, harr⟩

#print axioms lemma_A1
#print axioms lemma_A2
#print axioms lemma_B
#print axioms corollary_B'
#print axioms lemma_C0
#print axioms lemma_C0_total
#print axioms lemma_6_4
#print axioms lemma_D0
#print axioms theorem_U
