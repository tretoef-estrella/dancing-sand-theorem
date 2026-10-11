module

public import RequestProject.AntitonicFit.All

/-!
# `C37_the_mirror_that_doubles.md`: Part F — the fit of a doubled sequence

Namespace `Mirror`.  C1's `AntitonicFit.fit`, `ifit`, `toR`, `levelSet` and the characterization
of the fit (Lemma 7.1, in its global form `fit_kkt` / `fit_eq_of_kkt`) are used directly.

## Encoding

A sequence of length `N` is a function `x : ℕ → ℝ` (or `ℕ → ℤ`) read at positions `< N`, as in C1.
The doubled sequence (every entry written twice) is `fun j => x (j / 2)`, of length `2 * N`.
-/

@[expose] public section

namespace Mirror

open Finset AntitonicFit

/-- Sums of a doubled sequence: `Σ_{j<n} f(⌊j/2⌋) = Σ_{j<⌊n/2⌋} f j + Σ_{j<⌊(n+1)/2⌋} f j`
(auxiliary for Part F of `C37_the_mirror_that_doubles.md`). -/
lemma sum_range_half {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ range n, f (j / 2) = ∑ j ∈ range (n / 2), f j + ∑ j ∈ range ((n + 1) / 2), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega,
        show (2 * m + 1 + 1) / 2 = m + 1 by omega, sum_range_succ]
      abel
    · rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
        show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega, sum_range_succ]
      abel

/-- **(F1)** of `C37_the_mirror_that_doubles.md`: for every `N`, `x : ℕ → ℝ` and `j < 2 * N`,
`AntitonicFit.fit (2 * N) (fun j => x (j / 2)) j = AntitonicFit.fit N x (j / 2)`.
By the characterization of the fit (C1, Lemma 7.1, global form, and uniqueness). -/
theorem F1 (N : ℕ) (x : ℕ → ℝ) (j : ℕ) (hj : j < 2 * N) :
    fit (2 * N) (fun j => x (j / 2)) j = fit N x (j / 2) := by
  refine fit_eq_of_kkt (z := fun j => fit N x (j / 2)) ?_ j hj
  obtain ⟨hmono, hle, htot, hdrop⟩ := fit_kkt N x
  have hres : ∀ n, resid (fun j => x (j / 2)) (fun j => fit N x (j / 2)) n =
      resid x (fit N x) (n / 2) + resid x (fit N x) ((n + 1) / 2) := fun n => by
    unfold resid; exact sum_range_half (fun j => x j - fit N x j) n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact hmono.anti (Nat.div_le_div_right (by omega)) (by omega)
  · intro n hn
    rw [hres]
    linarith [hle (n / 2) (by omega), hle ((n + 1) / 2) (by omega)]
  · rw [hres, show 2 * N / 2 = N by omega, show (2 * N + 1) / 2 = N by omega, htot, add_zero]
  · intro s hs hlt
    simp only at hlt
    rw [hres]
    rcases Nat.even_or_odd' s with ⟨m, rfl | rfl⟩
    · rw [show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega] at hlt
      exact absurd hlt (lt_irrefl _)
    · rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega] at hlt
      rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega,
        hdrop m (by omega) hlt, add_zero]

/-- The integer-fit block rule is invariant under doubling: for `b < 2`,
`blockF (2S) (2P) (2r + b) = blockF S P r` (auxiliary for (F2) of
`C37_the_mirror_that_doubles.md`). -/
lemma blockF_double (S : ℤ) (P r b : ℕ) (hb : b < 2) :
    blockF (2 * S) (2 * P) (2 * r + b) = blockF S P r := by
  unfold blockF
  have hmod : 2 * S % ((2 * P : ℕ) : ℤ) = 2 * (S % (P : ℤ)) := by
    push_cast
    exact Int.mul_emod_mul_of_pos _ _ (by norm_num)
  have hdiv : ((2 * S : ℤ) : ℝ) / ((2 * P : ℕ) : ℝ) = (S : ℝ) / (P : ℝ) := by
    push_cast
    exact mul_div_mul_left _ _ (by norm_num)
  rw [hmod, hdiv]
  have : ((2 * r + b : ℕ) : ℤ) < 2 * (S % (P : ℤ)) ↔ (r : ℤ) < S % (P : ℤ) := by
    push_cast; omega
  simp only [this]

/-- The rank of `j` in a doubled level set: if `p (j / 2)`, then
`#{i < j : p (i / 2)} = 2 · #{i < j / 2 : p i} + j % 2` (auxiliary for (F2) of
`C37_the_mirror_that_doubles.md`). -/
lemma rank_half (p : ℕ → Prop) [DecidablePred p] (j : ℕ) (hpj : p (j / 2)) :
    ((range j).filter (fun i => p (i / 2))).card = 2 * ((range (j / 2)).filter p).card + j % 2 := by
  rw [card_filter, card_filter, sum_range_half (fun i => if p i then 1 else 0) j]
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · rw [show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega,
      show 2 * m % 2 = 0 by omega]
    ring
  · rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
      show (2 * m + 1) % 2 = 1 by omega, sum_range_succ]
    rw [show (2 * m + 1) / 2 = m by omega] at hpj
    rw [if_pos hpj]
    ring

/-- **(F2)** of `C37_the_mirror_that_doubles.md`: for every `N`, `x : ℕ → ℤ` and every `j`,
`AntitonicFit.ifit (2 * N) (fun j => x (j / 2)) j = AntitonicFit.ifit N x (j / 2)`.
A doubled level set has `2P` positions and sum `2S`, and the rank of `j` in it is twice the rank of
`j / 2` plus `j % 2`. -/
theorem F2 (N : ℕ) (x : ℕ → ℤ) (j : ℕ) :
    ifit (2 * N) (fun j => x (j / 2)) j = ifit N x (j / 2) := by
  by_cases hj : j < 2 * N
  swap
  · rw [ifit_of_le (by omega), ifit_of_le (by omega)]
  have hj2 : j / 2 < N := by omega
  rw [ifit_of_lt hj, ifit_of_lt hj2]
  set f := fit N (toR x) with hf
  set p : ℕ → Prop := fun i => f i = f (j / 2) with hp
  have hfit : ∀ i < 2 * N, fit (2 * N) (toR fun j => x (j / 2)) i = f (i / 2) :=
    fun i hi => F1 N (toR x) i hi
  have hL : levelSet N f (j / 2) = (range N).filter p := rfl
  have hL2 : levelSet (2 * N) (fit (2 * N) (toR fun j => x (j / 2))) j =
      (range (2 * N)).filter (fun i => p (i / 2)) := by
    ext i
    simp only [levelSet, mem_filter, mem_range, hp]
    constructor
    · rintro ⟨hi, he⟩
      rw [hfit i hi, hfit j hj] at he
      exact ⟨hi, he⟩
    · rintro ⟨hi, he⟩
      rw [hfit i hi, hfit j hj]
      exact ⟨hi, he⟩
  have hpj : p (j / 2) := rfl
  -- the three quantities of the block rule
  have hcard : ((range (2 * N)).filter (fun i => p (i / 2))).card =
      2 * ((range N).filter p).card := by
    rw [card_filter, card_filter,
      sum_range_half (fun i => if p i then 1 else 0) (2 * N),
      show 2 * N / 2 = N by omega, show (2 * N + 1) / 2 = N by omega, two_mul]
  have hsum : ∑ i ∈ (range (2 * N)).filter (fun i => p (i / 2)), x (i / 2) =
      2 * ∑ i ∈ (range N).filter p, x i := by
    rw [sum_filter, sum_filter, sum_range_half (fun i => if p i then x i else 0) (2 * N),
      show 2 * N / 2 = N by omega, show (2 * N + 1) / 2 = N by omega, two_mul]
  have hrank : (((range (2 * N)).filter (fun i => p (i / 2))).filter (· < j)).card =
      2 * (((range N).filter p).filter (· < j / 2)).card + j % 2 := by
    have e1 : ((range (2 * N)).filter (fun i => p (i / 2))).filter (· < j) =
        (range j).filter (fun i => p (i / 2)) := by
      ext i; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h', h⟩
      · rintro ⟨h', h⟩; exact ⟨⟨by omega, h⟩, h'⟩
    have e2 : ((range N).filter p).filter (· < j / 2) = (range (j / 2)).filter p := by
      ext i; simp only [mem_filter, mem_range]; constructor
      · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h', h⟩
      · rintro ⟨h', h⟩; exact ⟨⟨by omega, h⟩, h'⟩
    rw [e1, e2]
    exact rank_half p j hpj
  rw [hL2, hL, hcard, hsum, hrank]
  exact blockF_double _ _ _ _ (Nat.mod_lt _ (by norm_num))

end Mirror
