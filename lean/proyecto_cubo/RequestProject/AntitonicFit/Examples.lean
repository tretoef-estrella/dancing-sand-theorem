module

public import RequestProject.AntitonicFit.Cuts

/-!
# Worked examples of `C1_antitonic_fits.md`

* The example showing that **the hypothesis of (b2) cannot be dropped**:
  `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)`.
* The example in *Definition (integer fit)* showing that the integer fit is not non-increasing
  in general: `x = (−2, −2, 0, −2, −1)`.
* The antisymmetric example of the *Checks* section: `x = (2, −1, 1, −2)`.

Finite sequences are written as lists: `fun j => l.getD j 0` is the sequence with entries `l`
(and value `0` at positions `≥ l.length`).
-/

@[expose] public section

namespace AntitonicFit

open Finset

theorem fit_eq_list {N : ℕ} {x : ℕ → ℝ} {l : List ℝ} (hl : l.length = N)
    (h : KKT N x (fun j => l.getD j 0)) : fit N x = fun j => l.getD j 0 := by
  funext j
  by_cases hj : j < N
  · exact fit_eq_of_kkt h j hj
  · rw [fit_of_le (by omega), List.getD_eq_default _ _ (by omega)]

theorem ifit_eq_list {N : ℕ} {x : ℕ → ℤ} {l : List ℤ} (hl : l.length = N)
    (h : ∀ j < N, ifit N x j = l.getD j 0) : ifit N x = fun j => l.getD j 0 := by
  funext j
  by_cases hj : j < N
  · exact h j hj
  · rw [ifit_of_le (by omega), List.getD_eq_default _ _ (by omega)]

/-! ## The example `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)` -/

/-- The sequence `x = (3, 4, 3, 4)` of the example after Lemma 7.2 in `C1_antitonic_fits.md`. -/
def exX : ℕ → ℤ := fun j => [3, 4, 3, 4].getD j 0

/-- The sequence `δ = (1, 1, 0, 0)` of the example after Lemma 7.2 in `C1_antitonic_fits.md`. -/
def exδ : ℕ → ℤ := fun j => [1, 1, 0, 0].getD j 0

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`: `fit(3, 4, 3, 4) = (7/2, 7/2, 7/2, 7/2)`. -/
theorem fit_exX : fit 4 (toR exX) = fun j => ([7/2, 7/2, 7/2, 7/2] : List ℝ).getD j 0 := by
  refine fit_eq_list rfl ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; have : i < 3 := by omega
    interval_cases i <;> norm_num
  · intro n hn; interval_cases n <;> norm_num [resid, sum_range_succ, toR, exX]
  · norm_num [resid, sum_range_succ, toR, exX]
  · intro s hs hlt; have : s < 3 := by omega
    interval_cases s <;> norm_num at hlt

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`: `x = (3, 4, 3, 4)` is cut at `2`. -/
theorem exX_isCut : IsCut 4 (toR exX) 2 := by
  refine isCut_iff_resid.2 ⟨by norm_num, by norm_num, ?_⟩
  rw [fit_exX]
  norm_num [resid, sum_range_succ, toR, exX]

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`: the cut of `x = (3, 4, 3, 4)` at `2` is
not strict. -/
theorem exX_not_strictCut : ¬ IsStrictCut 4 (toR exX) 2 := by
  rintro ⟨-, h⟩
  rw [fit_exX] at h
  norm_num at h

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`: `x + δ = (4, 5, 3, 4)`. -/
theorem exX_add_exδ : exX + exδ = fun j => [4, 5, 3, 4].getD j 0 := by
  funext j
  by_cases hj : j < 4
  · interval_cases j <;> rfl
  · simp only [Pi.add_apply, exX, exδ]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`:
`fit(4, 5, 3, 4) = (9/2, 9/2, 7/2, 7/2)`. -/
theorem fit_exX_add_exδ :
    fit 4 (toR (exX + exδ)) = fun j => ([9/2, 9/2, 7/2, 7/2] : List ℝ).getD j 0 := by
  rw [exX_add_exδ]
  refine fit_eq_list rfl ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; have : i < 3 := by omega
    interval_cases i <;> norm_num
  · intro n hn; interval_cases n <;> norm_num [resid, sum_range_succ, toR]
  · norm_num [resid, sum_range_succ, toR]
  · intro s hs hlt; have : s < 3 := by omega
    interval_cases s <;> first | (norm_num at hlt; done) | norm_num [resid, sum_range_succ, toR]

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`: `ifit(x + δ) = ifit(4, 5, 3, 4) =
(5, 4, 4, 3)`. -/
theorem ifit_exX_add_exδ : ifit 4 (exX + exδ) = fun j => [5, 4, 4, 3].getD j 0 := by
  have h1 : IsLevelInterval 4 (fit 4 (toR (exX + exδ))) 0 1 := by
    rw [fit_exX_add_exδ]
    refine ⟨by norm_num, by norm_num, fun i hi => ?_⟩
    interval_cases i <;> norm_num
  have h2 : IsLevelInterval 4 (fit 4 (toR (exX + exδ))) 2 3 := by
    rw [fit_exX_add_exδ]
    refine ⟨by norm_num, by norm_num, fun i hi => ?_⟩
    interval_cases i <;> norm_num
  refine ifit_eq_list rfl fun j hj => ?_
  interval_cases j
  · rw [ifit_eq_of_level h1 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h1 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h2 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h2 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`: `ifit(3, 4, 3, 4) = (4, 4, 3, 3)`. -/
theorem ifit_exX : ifit 4 exX = fun j => [4, 4, 3, 3].getD j 0 := by
  have h1 : IsLevelInterval 4 (fit 4 (toR exX)) 0 3 := by
    rw [fit_exX]
    refine ⟨by norm_num, by norm_num, fun i hi => ?_⟩
    interval_cases i <;> norm_num
  refine ifit_eq_list rfl fun j hj => ?_
  rw [ifit_eq_of_level h1 (by norm_num) (by omega), blockF_eq _ (by norm_num)]
  interval_cases j <;> decide

/-- Example after Lemma 7.2 in `C1_antitonic_fits.md`:
`ifit(x) + δ = (4, 4, 3, 3) + δ = (5, 5, 3, 3)`. -/
theorem ifit_exX_add : ifit 4 exX + exδ = fun j => [5, 5, 3, 3].getD j 0 := by
  rw [ifit_exX]
  funext j
  by_cases hj : j < 4
  · interval_cases j <;> rfl
  · simp only [Pi.add_apply, exδ]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

/-- **The hypothesis of (b2) cannot be dropped** (`C1_antitonic_fits.md`, example after
Lemma 7.2): for `x = (3, 4, 3, 4)` and `δ = (1, 1, 0, 0)`, `x` is cut at `2`, the cut is not
strict, and `ifit(x + δ) ≠ ifit(x) + δ` (they differ at position `1`). -/
theorem example_b2_hypothesis_needed :
    IsCut 4 (toR exX) 2 ∧ ¬ IsStrictCut 4 (toR exX) 2 ∧ ifit 4 (exX + exδ) ≠ ifit 4 exX + exδ ∧
      ifit 4 (exX + exδ) 1 ≠ (ifit 4 exX + exδ) 1 := by
  have h : ifit 4 (exX + exδ) 1 ≠ (ifit 4 exX + exδ) 1 := by
    rw [ifit_exX_add_exδ, ifit_exX_add]; decide
  exact ⟨exX_isCut, exX_not_strictCut, fun he => h (by rw [he]), h⟩

/-- Complement to the example after Lemma 7.2 in `C1_antitonic_fits.md`: this `δ` satisfies the
setting of (b) with the single cut `b_1 = 2` (it is non-increasing and constant on `[0, 2)` and
`[2, 4)`), but it is not constant on the level sets of `fit(x)` (the hypothesis of (b2)). -/
theorem example_b2_setting :
    NonIncr 4 (toR exδ) ∧ (∀ j, j + 1 < 4 → j + 1 ∉ ({2} : Finset ℕ) → exδ (j + 1) = exδ j) ∧
      ¬ ConstOnLevelSets 4 (fit 4 (toR exX)) exδ := by
  refine ⟨fun i hi => ?_, fun j hj hB => ?_, fun h => ?_⟩
  · have : i < 3 := by omega
    interval_cases i <;> norm_num [toR, exδ]
  · have : j < 3 := by omega
    interval_cases j <;> simp_all [exδ]
  · have := h 1 2 (by norm_num) (by norm_num) (by rw [fit_exX]; norm_num)
    exact absurd this (by decide)

/-! ## The example `x = (−2, −2, 0, −2, −1)`: the integer fit is not non-increasing -/

/-- The sequence `x = (−2, −2, 0, −2, −1)` of *Definition (integer fit)* in
`C1_antitonic_fits.md`. -/
def exY : ℕ → ℤ := fun j => [-2, -2, 0, -2, -1].getD j 0

/-- *Definition (integer fit)* in `C1_antitonic_fits.md`:
`fit(−2, −2, 0, −2, −1) = (−4/3, −4/3, −4/3, −3/2, −3/2)`. -/
theorem fit_exY :
    fit 5 (toR exY) = fun j => ([-4/3, -4/3, -4/3, -3/2, -3/2] : List ℝ).getD j 0 := by
  refine fit_eq_list rfl ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; have : i < 4 := by omega
    interval_cases i <;> norm_num
  · intro n hn; interval_cases n <;> norm_num [resid, sum_range_succ, toR, exY]
  · norm_num [resid, sum_range_succ, toR, exY]
  · intro s hs hlt; have : s < 4 := by omega
    interval_cases s <;> first | (norm_num at hlt; done) | norm_num [resid, sum_range_succ, toR, exY]

/-- *Definition (integer fit)* in `C1_antitonic_fits.md`:
`ifit(−2, −2, 0, −2, −1) = (−1, −1, −2, −1, −2)`. -/
theorem ifit_exY : ifit 5 exY = fun j => [-1, -1, -2, -1, -2].getD j 0 := by
  have h1 : IsLevelInterval 5 (fit 5 (toR exY)) 0 2 := by
    rw [fit_exY]
    refine ⟨by norm_num, by norm_num, fun i hi => ?_⟩
    interval_cases i <;> norm_num
  have h2 : IsLevelInterval 5 (fit 5 (toR exY)) 3 4 := by
    rw [fit_exY]
    refine ⟨by norm_num, by norm_num, fun i hi => ?_⟩
    interval_cases i <;> norm_num
  refine ifit_eq_list rfl fun j hj => ?_
  interval_cases j
  · rw [ifit_eq_of_level h1 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h1 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h1 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h2 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide
  · rw [ifit_eq_of_level h2 (by norm_num) (by norm_num), blockF_eq _ (by norm_num)]; decide

/-- *Definition (integer fit)* in `C1_antitonic_fits.md`: the integer fit is NOT non-increasing
in general; for `x = (−2, −2, 0, −2, −1)`, `ifit(x)_2 = −2 < −1 = ifit(x)_3`. -/
theorem ifit_not_nonIncr : ¬ NonIncr 5 (toR (ifit 5 exY)) := by
  intro h
  have := h 2 (by norm_num)
  rw [ifit_exY] at this
  norm_num [toR] at this

/-! ## The antisymmetric example `x = (2, −1, 1, −2)` -/

/-- The antisymmetric sequence `x = (2, −1, 1, −2)` of the *Checks* in `C1_antitonic_fits.md`. -/
noncomputable def exW : ℕ → ℝ := fun j => ([2, -1, 1, -2] : List ℝ).getD j 0

/-- *Checks* in `C1_antitonic_fits.md`: `x = (2, −1, 1, −2)` is antisymmetric. -/
theorem exW_antisymm : IsAntisymm 4 exW := by
  intro j hj
  interval_cases j <;> norm_num [exW]

/-- *Checks* in `C1_antitonic_fits.md`: `Z_1 = fit(2, −1) = (2, −1)`. -/
theorem fit_exW_prefix : fit 2 exW = fun j => ([2, -1] : List ℝ).getD j 0 := by
  refine fit_eq_list rfl ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; have : i = 0 := by omega
    subst this; norm_num
  · intro n hn; interval_cases n <;> norm_num [resid, sum_range_succ, exW]
  · norm_num [resid, sum_range_succ, exW]
  · intro s hs hlt; have : s = 0 := by omega
    subst this; norm_num [resid, sum_range_succ, exW]

/-- *Checks* in `C1_antitonic_fits.md`: `fit(2, −1, 1, −2) = (2, 0, 0, −2)`. -/
theorem fit_exW : fit 4 exW = fun j => ([2, 0, 0, -2] : List ℝ).getD j 0 := by
  refine fit_eq_list rfl ⟨?_, ?_, ?_, ?_⟩
  · intro i hi; have : i < 3 := by omega
    interval_cases i <;> norm_num
  · intro n hn; interval_cases n <;> norm_num [resid, sum_range_succ, exW]
  · norm_num [resid, sum_range_succ, exW]
  · intro s hs hlt; have : s < 3 := by omega
    interval_cases s <;> first | (norm_num at hlt; done) | norm_num [resid, sum_range_succ, exW]

end AntitonicFit
