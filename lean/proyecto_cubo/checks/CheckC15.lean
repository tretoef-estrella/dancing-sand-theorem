import RequestProject.DanceSmith.All

/-! Auditor's check file for Lean piece C15 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C15_smith_form_of_the_dance_matrix.md` and closed by
`rfl`/`decide`; the main statements restated by hand with every object unfolded and closed by the
certified theorems; then `#print axioms`. -/

open Finset Matrix Windows TheoremF DanceSmith

-- bit reversal on m bits
example : bitRev 2 1 = 2 := by decide
example : bitRev 3 1 = 4 := by decide
example : bitRev 3 6 = 3 := by decide
-- sl, Mo, the clocks, C and ŷ♯
example (ds : List Bool) (p : Fin (2 ^ Dance.mCount ds)) :
    (sl ds p : ℕ) = bitRev (Dance.mCount ds) p := rfl
example (ds : List Bool) (α i : ℕ) (p q : Fin (2 ^ Dance.mCount ds)) :
    Mo ds α i p q = finalMatrix ℤ ds α i (sl ds p) (sl ds q) := rfl
example (ds : List Bool) (α i j : ℕ) :
    xClk ds α i j = GoldenMatching.xVal ds.length (Ids ds) (α : ℤ) (i - 1) (dancer (Ids ds) j) := rfl
example (ds : List Bool) (α i : ℕ) :
    yHat ds α i = AntitonicFit.ifit (2 ^ Dance.mCount ds) (xClk ds α i) := rfl
example (ds : List Bool) (α i : ℕ) :
    Cst ds α i = (α : ℤ) * 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length) := rfl
example (ds : List Bool) (α : ℕ) :
    yHatS ds α = CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) := rfl

-- (P1)
example (ds : List Bool) (p : Fin (2 ^ Dance.mCount ds)) :
    Dset ds (bitRev (Dance.mCount ds) p) = dancer (Ids ds) p :=
  (P1 ds).2.2 p
example (ds : List Bool) : Function.Bijective (sl ds) := (P1 ds).2.1

-- (P2)
example {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℤ) (r : ℕ) :
    Divisors.dd (M.submatrix σ σ) r = Divisors.dd M r := P2_general σ M r

-- (Q1)
example (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, Odd P.det ∧ Odd Q.det ∧
      ∃ ρ ≤ n, ∃ e : ℕ → ℕ, (∀ i j, i ≤ j → j < ρ → e i ≤ e j) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
          P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < ρ then u j * 2 ^ e j else 0) :=
  Q1 n A

-- (Q2)
example {n ρ : ℕ} (e : ℕ → ℕ) (u : ℕ → ℤ) (A P Q : Matrix (Fin n) (Fin n) ℤ)
    (hP : Odd P.det) (hQ : Odd Q.det) (hρ : ρ ≤ n)
    (he : ∀ i j, i ≤ j → j < ρ → e i ≤ e j) (hu : ∀ j, Odd (u j))
    (hD : P * A * Q = diagonal (fun j : Fin n => if (j : ℕ) < ρ then u j * 2 ^ e j else 0)) :
    (∀ r ≤ ρ, Divisors.dd A r = ∑ j ∈ range r, e j) ∧
      (∀ r, ρ < r → ∀ B C : Finset (Fin n), B.card = r → C.card = r →
        Divisors.minor A r B C = 0) ∧ (A.det ≠ 0 ↔ ρ = n) :=
  Q2 A P Q hP hQ hρ he hu hD

-- (S1), with Mo and C written out
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    (p q : Fin (2 ^ Dance.mCount ds)) (h : dancer (Ids ds) q ⊆ dancer (Ids ds) p) :
    finalMatrix ℤ ds α i (sl ds p) (sl ds q) ≠ 0 ∧
      ∃ n : ℕ, (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length) +
          GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
        2 ^ n ∣ finalMatrix ℤ ds α i (sl ds p) (sl ds q) ∧
        ¬ 2 ^ (n + 1) ∣ finalMatrix ℤ ds α i (sl ds p) (sl ds q) :=
  (S1 ds hk α i hα hi p q).2 h
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    (p q : Fin (2 ^ Dance.mCount ds)) (h : ¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p) :
    finalMatrix ℤ ds α i (sl ds p) (sl ds q) = 0 :=
  (S1 ds hk α i hα hi p q).1 h

-- (S2), with ŷ written out
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) (r : ℕ)
    (hr : r ≤ 2 ^ Dance.mCount ds) :
    (Divisors.dd (finalMatrix ℤ ds α i) r : ℤ) =
      r * ((α : ℤ) * 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length)) +
        ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds),
          AntitonicFit.ifit (2 ^ Dance.mCount ds) (fun j =>
            GoldenMatching.xVal ds.length (Ids ds) (α : ℤ) (i - 1) (dancer (Ids ds) j)) j :=
  (S2 ds hk α i hα hi).1 r hr
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    (finalMatrix ℤ ds α i).det ≠ 0 := (S2 ds hk α i hα hi).2.1

-- (S3)
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds,
            (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length) +
              AntitonicFit.ifit (2 ^ Dance.mCount ds) (fun j =>
                GoldenMatching.xVal ds.length (Ids ds) (α : ℤ) (i - 1) (dancer (Ids ds) j))
                (2 ^ Dance.mCount ds - 1 - j)) ∧
          P * finalMatrix ℤ ds α i * Q =
            diagonal (fun j : Fin (2 ^ Dance.mCount ds) => u j * 2 ^ E j) :=
  S3 ds hk α i hα hi

-- (Z1)
example (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) :
    (finalMatrix ℤ ds α 0).det = 0 ∧ (Ids ds = ∅ → finalMatrix ℤ ds α 0 = 0) := Z1 ds α hα

-- (Z2), with ŷ♯ written out
example (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) (r : ℕ)
    (hr : r ≤ 2 ^ Dance.mCount ds - 1) :
    (Divisors.dd (finalMatrix ℤ ds α 0) r : ℤ) = r * ((α : ℤ) * 2 ^ ds.length) +
      ∑ j ∈ Ico (2 ^ Dance.mCount ds - 1 - r) (2 ^ Dance.mCount ds - 1),
        CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) j :=
  (Z2 ds hk α hα hne).1 r hr

-- (Z3)
example (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
            (E j : ℤ) = (α : ℤ) * 2 ^ ds.length +
              CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ)
                (2 ^ Dance.mCount ds - 2 - j)) ∧
          P * finalMatrix ℤ ds α 0 * Q = diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then u j * 2 ^ E j else 0) :=
  Z3 ds hk α hα hne

#print axioms P1
#print axioms P2_general
#print axioms P2
#print axioms Q1
#print axioms Q2
#print axioms S1
#print axioms S2
#print axioms S3
#print axioms Z1
#print axioms Z2
#print axioms Z3
