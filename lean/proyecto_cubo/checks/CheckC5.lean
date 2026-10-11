import RequestProject.Divisors.All

/-! Auditor's check file for Lean piece C5 (Grepy Escribano, 6 Oct 2026).
Encodings written out by hand from `C5_divisors_theorem_65.md` and closed by `rfl`; statements
restated by hand and closed by the certified theorems; then `#print axioms`. -/

open Divisors Finset Matrix

-- Encodings
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) (A B : Finset (Fin n))
    (hA : A.card = r) (hB : B.card = r) :
    minor M r A B = det (M.submatrix (A.orderEmbOfFin hA) (B.orderEmbOfFin hB)) :=
  minor_of_card M hA hB
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    minorVals M r = {v | ∃ A B : Finset (Fin n), A.card = r ∧ B.card = r ∧ minor M r A B ≠ 0 ∧
      padicValInt 2 (minor M r A B) = v} := rfl
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) : dd M r = sInf (minorVals M r) := rfl
example (C : ℤ) (e : ℕ → ℤ) (r : ℕ) : dHat C e r = (∑ i ∈ range r, e i) - r * C := rfl

-- Setting: dd_0 = 0, dd_n = v_2(det M), and the minimum is attained
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : dd M 0 = 0 := dd_zero M
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : det M ≠ 0) :
    dd M n = padicValInt 2 (det M) := dd_top hM
example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hM : det M ≠ 0) (r : ℕ) (hr : r ≤ n) :
    dd M r ∈ minorVals M r := dd_mem (minorVals_nonempty hM hr)

-- Cauchy–Binet
example {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ) (B : Matrix (Fin n) (Fin r) ℤ) :
    det (A * B) = ∑ S : {S : Finset (Fin n) // S.card = r},
      det (A.submatrix id (S.1.orderEmbOfFin S.2)) *
        det (B.submatrix (S.1.orderEmbOfFin S.2) id) := cauchy_binet A B

-- Lemma A1
example {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd (det P)) (hQ : Odd (det Q))
    (r : ℕ) (hr : r ≤ n) : dd (P * M * Q) r = dd M r := lemma_A1 M P Q hP hQ r

-- Lemma A2
example {n : ℕ} (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ) (hu : ∀ i, Odd (u i))
    (r : ℕ) (hr : r ≤ n) :
    dd (diagonal fun i => u i * 2 ^ e i) r = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i :=
  lemma_A2 e he u hu hr

-- Corollary A3
example {n : ℕ} (M P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd (det P)) (hQ : Odd (det Q))
    (e : Fin n → ℕ) (he : Monotone e) (u : Fin n → ℤ) (hu : ∀ i, Odd (u i))
    (hD : P * M * Q = diagonal fun i => u i * 2 ^ e i) :
    (∀ r ≤ n, dd M r = ∑ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < r), e i) ∧
    (∀ r : Fin n, (e r : ℤ) = (dd M (r + 1) : ℤ) - dd M r) ∧
    (∀ r, r + 2 ≤ n → (dd M (r + 1) : ℤ) - dd M r ≤ (dd M (r + 2) : ℤ) - dd M (r + 1)) :=
  ⟨fun _ hr => corollary_A3_sum M P Q hP hQ e he u hu hD hr,
   corollary_A3_increment M P Q hP hQ e he u hu hD,
   fun r hr => corollary_A3_convex M P Q hP hQ e he u hu hD r hr⟩

-- Theorem B (Theorem 6.5), with (M), and Corollary B'
example (N : ℕ) (x : ℕ → ℤ) (C : ℤ) (e : ℕ → ℤ)
    (he : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j ≤
      (∑ i ∈ range r, e i) - r * C)
    (hU : ∀ r ≤ N, (∑ i ∈ range r, e i) - r * C ≤ ∑ j ∈ Ico (N - r) N, x j)
    (hM : ∀ j, j + 1 < N → AntitonicFit.ifit N x (j + 1) ≤ AntitonicFit.ifit N x j) :
    (∀ r ≤ N, (∑ i ∈ range r, e i) - r * C = ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j) ∧
      ∀ i < N, e i = C + AntitonicFit.ifit N x (N - 1 - i) :=
  theorem_B N x C e he hF hU hM
example (N : ℕ) (x : ℕ → ℤ) (C : ℤ) (e : ℕ → ℤ)
    (he : ∀ i j, i ≤ j → j < N → e i ≤ e j)
    (hF : ∀ r ≤ N, ∑ j ∈ Ico (N - r) N, AntitonicFit.ifit N x j ≤ dHat C e r)
    (hU : ∀ r ≤ N, dHat C e r ≤ ∑ j ∈ Ico (N - r) N, x j) :
    ∀ j, j + 1 < N → AntitonicFit.ifit N x (j + 1) ≤ AntitonicFit.ifit N x j :=
  corollary_B' N x C e he hF hU

#print axioms cauchy_binet
#print axioms minorVals_nonempty
#print axioms dd_top
#print axioms lemma_A1
#print axioms lemma_A2
#print axioms corollary_A3_sum
#print axioms corollary_A3_increment
#print axioms corollary_A3_convex
#print axioms theorem_B
#print axioms theorem_B_without_M
#print axioms corollary_B'
