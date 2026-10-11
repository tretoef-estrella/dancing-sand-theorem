module

public import RequestProject.OddParts.PartB

/-!
# `C52_odd_parts.md`: Part C — the folded cube

* (X0) `X0`, (C1) `C1`, (C2) `C2`, (C3) `C3`, (C4) `C4`, (C5) `C5` (Corollary 1.4, the paper's
  form).
-/

@[expose] public section

noncomputable section

namespace OddParts

open CubeLaplacian Finset

/-- **(X0)** of `C52_odd_parts.md`: `chiBar n S (Fold.mk n g) = chi n S.1 g`. -/
theorem X0 (n : ℕ) (S : EvenS n) (g : CubeLaplacian.G n) :
    chiBar n S (Fold.mk n g) = chi n S.1 g := rfl

lemma mk_surj (n : ℕ) (x : Fold.Gbar n) : ∃ g, Fold.mk n g = x :=
  QuotientAddGroup.mk'_surjective _ x

lemma chiBar_add (n : ℕ) (S : EvenS n) (x y : Fold.Gbar n) :
    chiBar n S (x + y) = chiBar n S x * chiBar n S y := by
  obtain ⟨g, rfl⟩ := mk_surj n x
  obtain ⟨h, rfl⟩ := mk_surj n y
  rw [← map_add, X0, X0, X0, chi_add]

/-- Translating the argument of `u` by `mk (e n i)` in a folded Fourier coefficient. -/
lemma sum_chiBar_shift (n : ℕ) (S : EvenS n) (u : Fold.Gbar n → ℤ) (i : Fin n) :
    ∑ x, chiBar n S x * u (x + Fold.mk n (e n i)) =
      chi n S.1 (e n i) * ∑ x, chiBar n S x * u x := by
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (Fold.mk n (e n i))) _ _ (fun x => ?_)
  simp only [Equiv.coe_addRight, chiBar_add, X0]
  linear_combination (-(chiBar n S x * u (x + Fold.mk n (e n i)))) * chi_mul_self n S.1 (e n i)

/-- **(C1)** of `C52_odd_parts.md`: `fourierBar n (lapBar ℤ n u) = diagDBar n (fourierBar n u)`. -/
theorem C1 (n : ℕ) (u : Fold.Gbar n → ℤ) :
    fourierBar n (Fold.lapBar ℤ n u) = diagDBar n (fourierBar n u) := by
  funext S
  change ∑ x, chiBar n S x * (Fold.lapBar ℤ n u x) = 2 * S.1.card * ∑ x, chiBar n S x * u x
  simp only [Fold.lapBar_apply, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum (s := Finset.univ) (f := fun i => u (_ + Fold.mk n (e n i)))]
  rw [Finset.sum_comm (f := fun x i => chiBar n S x * u (x + Fold.mk n (e n i)))]
  simp only [sum_chiBar_shift, ← Finset.sum_mul, sum_chi_e]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  ring

/-- **(C2)** of `C52_odd_parts.md`: `lapBar ℤ n (ifourierBar n v) = ifourierBar n (diagDBar n v)`. -/
theorem C2 (n : ℕ) (v : EvenS n → ℤ) :
    Fold.lapBar ℤ n (ifourierBar n v) = ifourierBar n (diagDBar n v) := by
  funext x
  change (n : ℤ) * (∑ S, chiBar n S x * v S) -
      ∑ i, ∑ S, chiBar n S (x + Fold.mk n (e n i)) * v S =
    ∑ S, chiBar n S x * (2 * S.1.card * v S)
  rw [Finset.sum_comm]
  simp only [chiBar_add, X0, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : ∑ i, chiBar n S x * chi n S.1 (e n i) * v S =
      chiBar n S x * v S * ∑ i, chi n S.1 (e n i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h, sum_chi_e]; ring

/-! ### Orthogonality on the folded cube -/

lemma aElt_add_self (n : ℕ) : Fold.aElt n + Fold.aElt n = 0 := by
  funext i; simp only [Fold.aElt, Pi.add_apply, Pi.zero_apply]; decide

lemma aElt_ne_zero {n : ℕ} (hn : 1 ≤ n) : Fold.aElt n ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hn⟩
  simp only [Fold.aElt, Pi.zero_apply] at this
  exact absurd this (by decide)

lemma mem_zmultiples_aElt (n : ℕ) (y : CubeLaplacian.G n) :
    y ∈ AddSubgroup.zmultiples (Fold.aElt n) ↔ y = 0 ∨ y = Fold.aElt n := by
  constructor
  · rintro ⟨k, rfl⟩
    have hc : k • Fold.aElt n = fun _ => (k : ZMod 2) := by
      funext i; simp [Fold.aElt]
    show k • Fold.aElt n = 0 ∨ k • Fold.aElt n = Fold.aElt n
    rw [hc]
    generalize (k : ZMod 2) = c
    fin_cases c
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact zero_mem _
    · exact AddSubgroup.mem_zmultiples _

lemma mk_eq_mk_iff (n : ℕ) (g h : CubeLaplacian.G n) :
    Fold.mk n g = Fold.mk n h ↔ g = h ∨ g = h + Fold.aElt n := by
  change (g : Fold.Gbar n) = h ↔ _
  rw [QuotientAddGroup.eq, mem_zmultiples_aElt, neg_add_eq_zero, neg_add_eq_iff_eq_add]
  refine or_congr Iff.rfl ⟨fun hh => ?_, fun hg => ?_⟩
  · rw [hh, add_assoc, aElt_add_self, add_zero]
  · rw [hg, add_assoc, aElt_add_self, add_zero]

/-- Each fibre of `Fold.mk n` has two elements (`n ≥ 1`). -/
lemma sum_mk (n : ℕ) (hn : 1 ≤ n) (F : Fold.Gbar n → ℤ) :
    ∑ g, F (Fold.mk n g) = 2 * ∑ x, F x := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (Fold.mk n) (fun g => F (Fold.mk n g)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨g0, rfl⟩ := mk_surj n x
  have hfib : Finset.univ.filter (fun g => Fold.mk n g = Fold.mk n g0) =
      {g0, g0 + Fold.aElt n} := by
    ext g; simp [mk_eq_mk_iff]
  have hm : Fold.mk n (g0 + Fold.aElt n) = Fold.mk n g0 :=
    (mk_eq_mk_iff n _ _).mpr (Or.inr rfl)
  have hne : g0 ≠ g0 + Fold.aElt n := fun h => aElt_ne_zero hn (by simpa using h)
  rw [hfib, Finset.sum_pair hne, hm]
  ring

lemma chi_aElt (n : ℕ) (S : Finset (Fin n)) : chi n S (Fold.aElt n) = (-1) ^ S.card := by
  simp only [chi, Fold.aElt, Finset.sum_const, smul_eq_mul]
  rw [show (1 : ZMod 2).val = 1 from rfl, mul_one]

lemma two_pow_pred {n : ℕ} (hn : 1 ≤ n) : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- Orthogonality of the folded characters, summing over `Gbar n`. -/
lemma orthBar_set (n : ℕ) (hn : 1 ≤ n) (S T : EvenS n) :
    ∑ x, chiBar n S x * chiBar n T x = if S = T then (2 ^ (n - 1) : ℤ) else 0 := by
  have h := sum_mk n hn (fun x => chiBar n S x * chiBar n T x)
  simp only [X0] at h
  rw [orth_chi_set, two_pow_pred hn] at h
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  rw [← h]
  by_cases hST : S = T
  · rw [if_pos hST, if_pos (congrArg Subtype.val hST)]
  · rw [if_neg hST, if_neg (fun h' => hST (Subtype.ext h')), mul_zero]

lemma one_add_chi_aElt (n : ℕ) (S : Finset (Fin n)) :
    1 + chi n S (Fold.aElt n) = if Even S.card then 2 else 0 := by
  rw [chi_aElt]
  rcases Nat.even_or_odd S.card with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.mpr h)]; norm_num

lemma sum_evenS (n : ℕ) (F : Finset (Fin n) → ℤ) :
    2 * ∑ S : EvenS n, F S.1 = ∑ S, (1 + chi n S (Fold.aElt n)) * F S := by
  simp only [one_add_chi_aElt, ite_mul, zero_mul]
  rw [← Finset.sum_filter, Finset.mul_sum,
    Finset.sum_subtype (Finset.univ.filter fun S : Finset (Fin n) => Even S.card)
      (p := fun S => Even S.card) (by simp)]

/-- Orthogonality of the folded characters, summing over the even subsets. -/
lemma orthBar_pt (n : ℕ) (hn : 1 ≤ n) (x y : Fold.Gbar n) :
    ∑ S : EvenS n, chiBar n S x * chiBar n S y = if x = y then (2 ^ (n - 1) : ℤ) else 0 := by
  obtain ⟨g, rfl⟩ := mk_surj n x
  obtain ⟨h, rfl⟩ := mk_surj n y
  simp only [X0]
  have key := sum_evenS n (fun S => chi n S g * chi n S h)
  simp only [add_mul, one_mul, Finset.sum_add_distrib] at key
  have h2 : ∑ S, chi n S (Fold.aElt n) * (chi n S g * chi n S h) =
      ∑ S, chi n S g * chi n S (h + Fold.aElt n) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [chi_add]; ring
  rw [h2, orth_chi_pt, orth_chi_pt] at key
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  rw [key]
  simp only [mk_eq_mk_iff]
  by_cases hgh : g = h
  · have : g ≠ h + Fold.aElt n := by
      intro h'; rw [hgh] at h'; exact aElt_ne_zero hn (by simpa using h')
    rw [if_pos hgh, if_neg this, if_pos (Or.inl hgh), two_pow_pred hn, add_zero]
  · by_cases hga : g = h + Fold.aElt n
    · rw [if_neg hgh, if_pos hga, if_pos (Or.inr hga), two_pow_pred hn, zero_add]
    · rw [if_neg hgh, if_neg hga, if_neg (not_or.mpr ⟨hgh, hga⟩)]; ring

/-- **(C3)** of `C52_odd_parts.md`: for every `n ≥ 1`,
`ifourierBar n (fourierBar n u) = 2 ^ (n - 1) • u` and
`fourierBar n (ifourierBar n v) = 2 ^ (n - 1) • v`. -/
theorem C3 (n : ℕ) (hn : 1 ≤ n) :
    (∀ u, ifourierBar n (fourierBar n u) = (2 ^ (n - 1) : ℕ) • u) ∧
      (∀ v, fourierBar n (ifourierBar n v) = (2 ^ (n - 1) : ℕ) • v) := by
  constructor
  · intro u
    funext x
    change ∑ S, chiBar n S x * ∑ y, chiBar n S y * u y = (2 ^ (n - 1) : ℕ) • u x
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ y, ∑ S, chiBar n S x * (chiBar n S y * u y) =
        (if x = y then (2 ^ (n - 1) : ℤ) else 0) * u y := by
      intro y
      rw [← orthBar_pt n hn, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp
  · intro v
    funext S
    change ∑ x, chiBar n S x * ∑ T, chiBar n T x * v T = (2 ^ (n - 1) : ℕ) • v S
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ T, ∑ x, chiBar n S x * (chiBar n T x * v T) =
        (if S = T then (2 ^ (n - 1) : ℤ) else 0) * v T := by
      intro T
      rw [← orthBar_set n hn, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [this, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp

/-- **(C4)** of `C52_odd_parts.md`: for every `n ≥ 1` and every prime `p ≠ 2`,
`Syl_p K̄(n) ≃+ Syl_p (Π_{S even, S ≠ ∅} ℤ/(2|S|))`. -/
theorem C4 (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (Fold.KBar n) ≃+
      Sylp p ((S : {S : EvenS n // S.1.Nonempty}) → ZMod (2 * S.1.1.card))) := by
  obtain ⟨t⟩ := sylpQuotTransfer (LinearMap.range (Fold.lapBar ℤ n))
    (LinearMap.range (diagDBar n)) (fourierBar n) (ifourierBar n)
    (by rintro _ ⟨u, rfl⟩; exact ⟨fourierBar n u, (C1 n u).symm⟩)
    (by rintro _ ⟨v, rfl⟩; exact ⟨ifourierBar n v, C2 n v⟩)
    (2 ^ (n - 1)) (C3 n hn).1 (C3 n hn).2 p hp (not_dvd_two_pow_of_ne hp hp2 (n - 1))
  obtain ⟨d⟩ := sylpDiagQuot (fun S : EvenS n => 2 * S.1.card) (diagDBar n)
    (fun v S => by simp [diagDBar]) (fun S => S.1.Nonempty)
    (fun S hS => by simp [Finset.not_nonempty_iff_eq_empty.mp hS]) hp.ne_zero
  exact ⟨(sylpProdBotLeft p ℤ (Fold.KBar n) (sylp_int_eq_bot hp.ne_zero)).symm.trans
    ((sylpCongr p (FoldGroup.cokerBarEquivKBar n).toAddEquiv).symm.trans (t.trans d))⟩

/-- **(C5)** of `C52_odd_parts.md` (Corollary 1.4, the paper's form): for every `n ≥ 1` and every
prime `p ≠ 2`, `Syl_p K̄(n) ≃+ Syl_p (⊕_{j even, 2 ≤ j ≤ n} (ℤ/2j)^{C(n,j)})`, with
`j = 2 (t + 1)` for `t : Fin (n / 2)`. -/
theorem C5 (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p (Fold.KBar n) ≃+
      Sylp p ((t : Fin (n / 2)) → Fin (n.choose (2 * (t + 1))) → ZMod (2 * (2 * (t + 1))))) := by
  obtain ⟨c4⟩ := C4 n hn p hp hp2
  have r := piZModReindex (idxC n) (fun S : {S : EvenS n // S.1.Nonempty} => 2 * S.1.1.card)
    (fun x => 2 * (2 * (x.1 + 1))) (fun x => by simp only [idxC_card])
  have c := (LinearEquiv.piCurry ℤ (fun (t : Fin (n / 2)) (_ : Fin (n.choose (2 * (t + 1)))) =>
    ZMod (2 * (2 * (t + 1))))).toAddEquiv
  exact ⟨c4.trans (sylpCongr p (r.trans c))⟩

end OddParts
