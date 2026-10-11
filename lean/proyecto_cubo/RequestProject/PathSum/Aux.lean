module

public import RequestProject.PathSum.Defs

/-!
# `C43_path_sum.md`: auxiliary facts for (P0)–(P2)

* `coef_mul_split`: the `L`-th coefficient of `x * y` at `f` is
  `x_0(f) y_L(f) + Σ_{a=1}^{L} C(L, a) x_a(f) y_{L−a}(f − a)` (Proof sketch of (P0), (P1)).
* `piF_ne_zero`, `norm_piF_le` (`v_2(π(d)) ≥ α`), `norm_factorial_ge` (`v_2(a!) ≤ a − 1`).
* `sL_zero`, `sL_succ` (the recursion `sL(L+1, f) = −(L+1) η sL(L, f−1)/π(f)`), `sL_ne_zero`.
* `term_identity`, `term_norm_le`: the ratio of the term `a ≥ 2` of the path sum, and its bound
  (Proof sketch of (P2)).
-/

@[expose] public section

noncomputable section

namespace PathSum

open FormalOps FormalDance Doubling Finset

/-- Proof sketch of (P0), (P1) in `C43_path_sum.md`: the term `a = 0` of a product coefficient
split off. -/
lemma coef_mul_split {A : Type*} [CommRing A] (x y : Bf A) (L : ℕ) (f : ℤ) :
    (x * y).coef L f = x.coef 0 f * y.coef L f + ∑ a ∈ range L,
      (L.choose (a + 1) : A) * x.coef (a + 1) f *
        y.coef (L - (a + 1)) (f - ((a + 1 : ℕ) : ℤ)) := by
  rw [Bf.coef_mul, sum_range_succ', add_comm]
  simp

/-- `C43_path_sum.md` (auxiliary): `‖2‖ = 1/2` in `ℚ_[2]`. -/
lemma norm_two_padic : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
  have := Padic.norm_p (p := 2)
  push_cast at this
  rw [this]
  norm_num

/-- `C43_path_sum.md` (auxiliary): `π(d) ≠ 0` for `d ≥ 0` when `c ≥ 1`. -/
lemma piF_ne_zero {α c : ℕ} (hc : 1 ≤ c) {d : ℤ} (hd : 0 ≤ d) : piF α c d ≠ 0 := by
  unfold piF
  have : ((d : ℚ_[2]) + c) = ((d + c : ℤ) : ℚ_[2]) := by push_cast; ring
  rw [this]
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (Int.cast_ne_zero.mpr (by omega))

/-- Proof sketch of (P2) in `C43_path_sum.md`: `v_2(π(d)) ≥ α`, i.e. `‖π(d)‖ ≤ (1/2)^α`. -/
lemma norm_piF_le (α c : ℕ) (d : ℤ) : ‖piF α c d‖ ≤ (1 / 2 : ℝ) ^ α := by
  unfold piF
  have : ((d : ℚ_[2]) + c) = ((d + c : ℤ) : ℚ_[2]) := by push_cast; ring
  rw [this, norm_mul, norm_pow, norm_two_padic]
  exact mul_le_of_le_one_right (by positivity) (Padic.norm_int_le_one _)

/-- Proof sketch of (P2) in `C43_path_sum.md`: `v_2(n!) ≤ n − 1` for `n ≥ 1`, i.e.
`(1/2)^(n−1) ≤ ‖n!‖`. -/
lemma norm_factorial_ge (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ^ (n - 1) ≤ ‖(n.factorial : ℚ_[2])‖ := by
  have hne : (n.factorial : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Padic.norm_eq_zpow_neg_valuation hne, Padic.valuation_natCast]
  have hlt := padicValNat_factorial_lt_of_ne_zero 2 (n := n) (by omega)
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, zpow_neg, ← inv_zpow, zpow_natCast, inv_eq_one_div]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  omega

/-- `C43_path_sum.md` (auxiliary): `sL(0, f) = 1/π(f)`. -/
lemma sL_zero (α c : ℕ) (η : ℚ_[2]) (f : ℤ) : sL α c η 0 f = 1 / piF α c f := by
  simp [sL]

/-- Proof sketch of (P1) in `C43_path_sum.md`: the recursion of `sL`,
`sL(L+1, f) = −(L+1) η sL(L, f−1)/π(f)` (no hypothesis needed, as `x / 0 = 0`). -/
lemma sL_succ (α c : ℕ) (η : ℚ_[2]) (L : ℕ) (f : ℤ) :
    sL α c η (L + 1) f = -(((L : ℚ_[2]) + 1) * η * sL α c η L (f - 1)) / piF α c f := by
  unfold sL
  rw [prod_range_succ' _ (L + 1)]
  have hp : ∏ i ∈ range (L + 1), piF α c (f - ((i + 1 : ℕ) : ℤ)) =
      ∏ i ∈ range (L + 1), piF α c (f - 1 - (i : ℤ)) := by
    refine prod_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  rw [hp, Nat.factorial_succ]
  simp only [div_eq_mul_inv, mul_inv, Nat.cast_mul, Nat.cast_succ, pow_succ, Nat.cast_zero,
    sub_zero]
  ring

/-- (P2) of `C43_path_sum.md`, the side remark: `sL α c η L f ≠ 0` for `c ≥ 1`, `η ≠ 0` and
`f ≥ L`. -/
lemma sL_ne_zero {α c : ℕ} (hc : 1 ≤ c) {η : ℚ_[2]} (hη : η ≠ 0) {L : ℕ} {f : ℤ}
    (hf : (L : ℤ) ≤ f) : sL α c η L f ≠ 0 := by
  unfold sL
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero L))) (pow_ne_zero _ hη)) ?_
  rw [prod_ne_zero_iff]
  intro i hi
  have := mem_range.mp hi
  exact piF_ne_zero hc (by omega)

/-- Proof sketch of (P2) in `C43_path_sum.md`: the ratio of the term `a ≥ 2`,
`C(L, a) z sL(L−a, f−a) / (π(f) sL(L, f)) = z ∏_{i < a−1} π(f−1−i) (−1)^a / (a! η^a)`
(the product over the `a − 1` floors skipped by the jump). -/
lemma term_identity {α c : ℕ} (hc : 1 ≤ c) {η : ℚ_[2]} (hη : η ≠ 0) {L a : ℕ} (ha : 2 ≤ a)
    (haL : a ≤ L) {f : ℤ} (hf : (L : ℤ) ≤ f) (z : ℚ_[2]) :
    (L.choose a : ℚ_[2]) * z * sL α c η (L - a) (f - (a : ℕ)) / (piF α c f * sL α c η L f) =
      z * (∏ i ∈ range (a - 1), piF α c (f - 1 - i)) * (-1) ^ a /
        (a.factorial * η ^ a) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, L = b + 1 + n := ⟨L - (b + 1), by omega⟩
  rw [show b + 1 + n - (b + 1) = n by omega, Nat.add_sub_cancel]
  have hch := Nat.choose_mul_factorial_mul_factorial (show b + 1 ≤ b + 1 + n by omega)
  rw [show b + 1 + n - (b + 1) = n by omega] at hch
  have hch' : ((b + 1 + n).choose (b + 1) : ℚ_[2]) * ((b + 1).factorial : ℚ_[2]) *
      (n.factorial : ℚ_[2]) = ((b + 1 + n).factorial : ℚ_[2]) := by exact_mod_cast hch
  have hsplit : ∏ i ∈ range (b + 1 + n + 1), piF α c (f - i) =
      piF α c f * (∏ i ∈ range b, piF α c (f - 1 - i)) *
        ∏ i ∈ range (n + 1), piF α c (f - (b + 1 : ℕ) - i) := by
    rw [show b + 1 + n + 1 = (b + 1) + (n + 1) by omega, prod_range_add, prod_range_succ']
    congr 1
    · rw [mul_comm]; congr 1
      · simp
      · refine prod_congr rfl fun i _ => ?_; congr 1; push_cast; ring
    · refine prod_congr rfl fun i _ => ?_; congr 1; push_cast; ring
  have h1 : ∏ i ∈ range (n + 1), piF α c (f - (b + 1 : ℕ) - i) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro i hi
    have := mem_range.mp hi
    exact piF_ne_zero hc (by push_cast at hf ⊢; omega)
  have h0 : piF α c f ≠ 0 := piF_ne_zero hc (by omega)
  have hQ : ∏ i ∈ range b, piF α c (f - 1 - i) ≠ 0 := by
    rw [prod_ne_zero_iff]
    intro i hi
    have := mem_range.mp hi
    exact piF_ne_zero hc (by push_cast at hf; omega)
  unfold sL
  rw [hsplit, ← hch']
  have hf1 : ((b + 1).factorial : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (n.factorial : ℚ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc0 : ((b + 1 + n).choose (b + 1) : ℚ_[2]) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  field_simp
  ring_nf
  rw [mul_comm b 2, pow_mul]
  norm_num

/-- Proof sketch of (P2) in `C43_path_sum.md`: for `a ≥ 2`, `α ≥ 1`, `‖η‖ = 1` and `‖z‖ ≤ 1`,
the ratio of `term_identity` has `v_2 ≥ α(a − 1) − v_2(a!) ≥ (α − 1)(a − 1) ≥ α − 1`. -/
lemma term_norm_le {α c : ℕ} (hα : 1 ≤ α) {η : ℚ_[2]} (hη : ‖η‖ = 1) {a : ℕ} (ha : 2 ≤ a)
    (f : ℤ) {z : ℚ_[2]} (hz : ‖z‖ ≤ 1) :
    ‖z * (∏ i ∈ range (a - 1), piF α c (f - 1 - i)) * (-1) ^ a /
        (a.factorial * η ^ a)‖ ≤ (1 / 2 : ℝ) ^ (α - 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hb : 1 ≤ b := by omega
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hη, norm_neg, norm_one,
    one_pow, mul_one, mul_one, norm_prod]
  have hfac := norm_factorial_ge (b + 1) (by omega)
  rw [Nat.add_sub_cancel] at hfac
  have hQ : ∏ i ∈ range b, ‖piF α c (f - 1 - i)‖ ≤ ((1 / 2 : ℝ) ^ α) ^ b :=
    (prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => norm_piF_le _ _ _)).trans_eq
      (by simp)
  have hpos : (0 : ℝ) < (1 / 2) ^ b := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hfac)]
  calc ‖z‖ * ∏ i ∈ range b, ‖piF α c (f - 1 - i)‖ ≤ 1 * ((1 / 2 : ℝ) ^ α) ^ b :=
        mul_le_mul hz hQ (prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
    _ = ((1 / 2 : ℝ) ^ (α - 1)) ^ b * (1 / 2) ^ b := by
        rw [one_mul, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hα]
    _ ≤ (1 / 2 : ℝ) ^ (α - 1) * (1 / 2) ^ b := by
        gcongr
        exact pow_le_of_le_one (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
          (by omega)
    _ ≤ (1 / 2 : ℝ) ^ (α - 1) * ‖((b + 1).factorial : ℚ_[2])‖ := by gcongr

/-- Proof sketch of (P2) in `C43_path_sum.md` (ultrametric): `‖1 + e‖ ≤ 1` if `‖e‖ ≤ 1`. -/
lemma norm_one_add_le {e : ℚ_[2]} (he : ‖e‖ ≤ 1) : ‖1 + e‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) he)

end PathSum
