module

public import RequestProject.OddParts.PartQ

/-!
# `C52_odd_parts.md`: Part F — Fourier on the cube

* (X) `X`, (F1) `F1`, (F2) `F2`, (F3) `F3`.

Auxiliary: the orthogonality relations `orth_chi_set` (`Σ_g χ_S χ_T = 2^n [S = T]`) and
`orth_chi_pt` (`Σ_S χ_S(g) χ_S(h) = 2^n [g = h]`).
-/

@[expose] public section

noncomputable section

namespace OddParts

open CubeLaplacian Finset

lemma chi_zero (n : ℕ) (S : Finset (Fin n)) : chi n S 0 = 1 := by
  simp [chi]

lemma chi_e (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    chi n S (e n i) = if i ∈ S then -1 else 1 := by
  have h : ∀ j, ((e n i) j).val = if j = i then 1 else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp only [e, Pi.single_eq_same, if_true]; rfl
    · simp [e, hj]
  simp only [chi, h, Finset.sum_ite_eq']
  split_ifs <;> simp

/-- **(X)** of `C52_odd_parts.md`: `chi n S (g + h) = chi n S g * chi n S h`, `chi n S 0 = 1`,
`chi n S (e n i) = if i ∈ S then -1 else 1`. -/
theorem X (n : ℕ) (S : Finset (Fin n)) :
    (∀ g h : G n, chi n S (g + h) = chi n S g * chi n S h) ∧ chi n S 0 = 1 ∧
      ∀ i : Fin n, chi n S (e n i) = if i ∈ S then -1 else 1 :=
  ⟨chi_add n S, chi_zero n S, chi_e n S⟩

lemma chi_mul_self (n : ℕ) (S : Finset (Fin n)) (g : G n) : chi n S g * chi n S g = 1 := by
  rw [chi, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

lemma sum_chi_e (n : ℕ) (S : Finset (Fin n)) :
    ∑ i, chi n S (e n i) = (n : ℤ) - 2 * S.card := by
  simp only [chi_e]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  simp only [nsmul_eq_mul, mul_neg, mul_one]
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => i ∈ S)
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hc
  have : ((Finset.univ.filter fun i => i ∉ S).card : ℤ) = n - S.card := by
    have hc' : ((S.card : ℕ) : ℤ) + ((Finset.univ.filter fun i => i ∉ S).card : ℕ) = n := by
      exact_mod_cast hc
    linarith
  rw [this]; ring

/-- Translating the argument of `f` by `e n i` in a Fourier coefficient. -/
lemma sum_chi_shift (n : ℕ) (S : Finset (Fin n)) (f : G n → ℤ) (i : Fin n) :
    ∑ g, chi n S g * f (g + e n i) = chi n S (e n i) * ∑ g, chi n S g * f g := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (e n i)) _ _ (fun g => ?_)
  simp only [Equiv.coe_addRight, chi_add]
  linear_combination (-(chi n S g * f (g + e n i))) * chi_mul_self n S (e n i)

/-- **(F1)** of `C52_odd_parts.md`: `fourier n (L n f) = diagD n (fourier n f)`. -/
theorem F1 (n : ℕ) (f : G n → ℤ) :
    fourier n (CubeLaplacian.L n f) = diagD n (fourier n f) := by
  funext S
  change ∑ g, chi n S g * (lap ℤ n f g) = 2 * S.card * ∑ g, chi n S g * f g
  simp only [lap_apply, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum (s := Finset.univ)
    (f := fun i => f (_ + e n i))]
  rw [Finset.sum_comm (f := fun g i => chi n S g * f (g + e n i))]
  simp only [sum_chi_shift, ← Finset.sum_mul, sum_chi_e]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  ring

/-- **(F2)** of `C52_odd_parts.md`: `L n (ifourier n v) = ifourier n (diagD n v)`. -/
theorem F2 (n : ℕ) (v : Finset (Fin n) → ℤ) :
    CubeLaplacian.L n (ifourier n v) = ifourier n (diagD n v) := by
  funext g
  change (n : ℤ) * (∑ S, chi n S g * v S) - ∑ i, ∑ S, chi n S (g + e n i) * v S =
    ∑ S, chi n S g * (2 * S.card * v S)
  rw [Finset.sum_comm]
  simp only [chi_add, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : ∑ i, chi n S g * chi n S (e n i) * v S = chi n S g * v S * ∑ i, chi n S (e n i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h, sum_chi_e]; ring

lemma chi_eq_prod (n : ℕ) (S : Finset (Fin n)) (g : G n) :
    chi n S g = ∏ i, (if i ∈ S then (-1 : ℤ) ^ (g i).val else 1) := by
  rw [Fintype.prod_ite_mem, chi, Finset.prod_pow_eq_pow_sum]

/-- Orthogonality of the characters, summing over `G n`. -/
lemma orth_chi_set (n : ℕ) (S T : Finset (Fin n)) :
    ∑ g : G n, chi n S g * chi n T g = if S = T then (2 ^ n : ℤ) else 0 := by
  simp only [chi_eq_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (x : ZMod 2) =>
    (if i ∈ S then (-1 : ℤ) ^ x.val else 1) * (if i ∈ T then (-1 : ℤ) ^ x.val else 1))]
  have hfac : ∀ i, ∑ x : ZMod 2,
      (if i ∈ S then (-1 : ℤ) ^ x.val else 1) * (if i ∈ T then (-1 : ℤ) ^ x.val else 1) =
      if (i ∈ S ↔ i ∈ T) then 2 else 0 := by
    intro i
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp only [hS, hT, if_true, if_false,
      iff_true, iff_false, not_true, mul_one, one_mul] <;>
      decide
  simp only [hfac]
  split_ifs with hST
  · subst hST; simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra hne; push_neg at hne; exact hST (Finset.ext hne)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma add_eq_zero_iff_G {n : ℕ} (g h : G n) : g + h = 0 ↔ g = h := by
  constructor
  · intro hgh
    funext i
    have := congrFun hgh i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    generalize g i = a at this ⊢
    generalize h i = b at this ⊢
    fin_cases a <;> fin_cases b <;> simp_all
  · rintro rfl
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize g i = a
    fin_cases a <;> decide

/-- Orthogonality of the characters, summing over the subsets. -/
lemma orth_chi_pt (n : ℕ) (g h : G n) :
    ∑ S : Finset (Fin n), chi n S g * chi n S h = if g = h then (2 ^ n : ℤ) else 0 := by
  simp only [← chi_add]
  have hprod : ∀ k : G n, ∑ S : Finset (Fin n), chi n S k =
      ∏ i, (1 + (-1 : ℤ) ^ (k i).val) := by
    intro k
    rw [Finset.prod_one_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [chi, Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  by_cases hgh : g = h
  · rw [if_pos hgh, (add_eq_zero_iff_G g h).mpr hgh]; simp
  · rw [if_neg hgh]
    have hk : g + h ≠ 0 := fun h0 => hgh ((add_eq_zero_iff_G g h).mp h0)
    obtain ⟨i, hi⟩ : ∃ i, (g + h) i ≠ 0 := by
      by_contra hne; push_neg at hne; exact hk (funext hne)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    generalize (g + h) i = a at hi ⊢
    fin_cases a
    · exact absurd rfl hi
    · decide

/-- **(F3)** of `C52_odd_parts.md`: `ifourier n (fourier n f) = 2 ^ n • f` and
`fourier n (ifourier n v) = 2 ^ n • v`. -/
theorem F3 (n : ℕ) :
    (∀ f, ifourier n (fourier n f) = (2 ^ n : ℕ) • f) ∧
      (∀ v, fourier n (ifourier n v) = (2 ^ n : ℕ) • v) := by
  constructor
  · intro f
    funext g
    change ∑ S, chi n S g * ∑ h, chi n S h * f h = (2 ^ n : ℕ) • f g
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ h, ∑ S, chi n S g * (chi n S h * f h) = (if g = h then (2 ^ n : ℤ) else 0) * f h := by
      intro h
      rw [← orth_chi_pt, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp
  · intro v
    funext S
    change ∑ g, chi n S g * ∑ T, chi n T g * v T = (2 ^ n : ℕ) • v S
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ T, ∑ g, chi n S g * (chi n T g * v T) = (if S = T then (2 ^ n : ℤ) else 0) * v T := by
      intro T
      rw [← orth_chi_set, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp

end OddParts
