module

public import RequestProject.PodiumCor.Layers

/-!
# `C36_the_podium_corollary.md`: Part E — the exponents of `Syl_2 K(Q_n)` (the dictionary)

Encodings as in `PodiumCor/Defs.lean`: `S n` is `CubeLaplacian.Syl2 (CubeLaplacian.K n)`,
`exps n : Multiset ℕ`, `cExp`, `layer`; `M.countP (fun e => j < e)` counts the elements of the
multiset `M` (with multiplicity) that are `> j`.  The `r`-th largest element of `exps n` is
`((exps n).sort (fun a b => b ≤ a)).getD (r − 1) 0` (the multiset sorted in decreasing order, `0`
past its end).

The general statements `cExp_le_iff` and `cExp_eq_getD` hold for any additive commutative group
whose layers are `2 ^ (M.countP (j < ·))` for a multiset `M`; (E2), (E3) are their instances.
-/

@[expose] public section

namespace PodiumCor

open Finset BaiCounts Families

/-! ### Counting in multisets and lists -/

/-- `countP` of a list sum of multisets (auxiliary for Part E of `C36_the_podium_corollary.md`). -/
lemma countP_list_sum (p : ℕ → Prop) [DecidablePred p] (l : List (Multiset ℕ)) :
    l.sum.countP p = (l.map (Multiset.countP p)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Multiset.countP_add, ih]

/-- `countP` of a finite sum of multisets (auxiliary for Part E of
`C36_the_podium_corollary.md`). -/
lemma countP_finset_sum (p : ℕ → Prop) [DecidablePred p] (s : Finset ℕ) (f : ℕ → Multiset ℕ) :
    (∑ a ∈ s, f a).countP p = ∑ a ∈ s, (f a).countP p :=
  map_sum (Multiset.countPAddMonoidHom p) f s

/-- `countP` of `replicate c a` (auxiliary for Part E of `C36_the_podium_corollary.md`). -/
lemma countP_replicate (p : ℕ → Prop) [DecidablePred p] (c a : ℕ) :
    (Multiset.replicate c a).countP p = if p a then c else 0 := by
  induction c with
  | zero => simp
  | succ c ih => rw [Multiset.replicate_succ, Multiset.countP_cons, ih]; split_ifs <;> simp

/-- `countP` is monotone in the predicate (auxiliary for Part E of
`C36_the_podium_corollary.md`). -/
lemma countP_mono (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q] (s : Multiset ℕ)
    (h : ∀ x, p x → q x) : s.countP p ≤ s.countP q := by
  simp only [Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card (Multiset.monotone_filter_right s h)

/-- `countP` of the image of `range m` (auxiliary for Part E of `C36_the_podium_corollary.md`). -/
lemma countP_map_range (m : ℕ) (f : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((range m).val.map f).countP p = ∑ x ∈ range m, if p (f x) then 1 else 0 := by
  rw [Multiset.countP_map, ← Finset.filter_val, ← Finset.card_def, Finset.card_filter]

/-- A product of `c`'s at the occurrences of `a` (auxiliary for (E1) of
`C36_the_podium_corollary.md`). -/
lemma prod_map_ite_eq (l : List ℕ) (a c : ℕ) :
    (l.map (fun x => if x = a then c else 1)).prod = c ^ l.count a := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.count_cons]
    by_cases h : x = a
    · subst h; simp [pow_succ]; ring
    · simp [h]

/-- A product of powers of `2` along a list (auxiliary for (E1) of
`C36_the_podium_corollary.md`). -/
lemma prod_map_two_pow (l : List ℕ) (f : ℕ → ℕ) :
    (l.map (fun x => 2 ^ f x)).prod = 2 ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, pow_add]

/-! ### The layers of a family -/

/-- `layer (Q e) j = 2 ^ [j < e]` (auxiliary for (E1) of `C36_the_podium_corollary.md`). -/
lemma layer_Q_pow (e j : ℕ) : layer (FamilyGroup.Q e) j = 2 ^ (if j < e then 1 else 0) := by
  rw [layer_Q]; split_ifs <;> rfl

/-- The layers of the small clocks, from C33 (S4) (auxiliary for (E1) of
`C36_the_podium_corollary.md`). -/
lemma layer_SC (d : List Bool) (j : ℕ) :
    layer (FamilyGroup.SC d) j = 2 ^ ∑ a ∈ range d.length,
      (if j < a then 1 else 0) * 2 ^ (d.length + Dance.mCount d - 1 - a) := by
  rw [layer_congr (MainTheorem.S4equiv d).toAddEquiv, layer_pi]
  simp_rw [layer_pi, layer_Q_pow, prod_const, card_univ, Fintype.card_fin, ← pow_mul,
    prod_pow_eq_pow_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (if j < a then 1 else 0) *
    2 ^ (d.length + Dance.mCount d - 1 - a))]

/-- The count of the small exponents `> j` (auxiliary for (E1) of
`C36_the_podium_corollary.md`). -/
lemma countP_smallExps (lam j : ℕ) :
    (smallExps lam).countP (fun e => j < e) = ∑ a ∈ range (ds lam).length,
      (if j < a then 1 else 0) * 2 ^ ((ds lam).length + Dance.mCount (ds lam) - 1 - a) := by
  unfold smallExps
  rw [countP_finset_sum]
  simp only [countP_replicate]
  rw [MainTheorem.S3_card]
  refine (sum_subset (s₂ := range (ds lam).length) (fun a ha => mem_range.2 (mem_Ico.1 ha).2)
    (fun a ha hna => ?_)).trans ?_
  · simp only [mem_Ico, not_and, not_lt] at hna
    simp only [mem_range] at ha
    have : a = 0 := by
      by_contra h0
      have := hna (by omega)
      omega
    subst this; simp
  · refine sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [add_comm]

/-- The layers of a product of big clocks (auxiliary for (E1) of `C36_the_podium_corollary.md`). -/
lemma layer_pi_Q (m : ℕ) (e : ℕ → ℕ) (j : ℕ) :
    layer ((p : Fin m) → FamilyGroup.Q (e p)) j =
      2 ^ ∑ x ∈ range m, if j < e x then 1 else 0 := by
  rw [layer_pi]
  simp_rw [layer_Q_pow]
  rw [prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun x => if j < e x then 1 else 0)]

/-- The layers of the group of the family `λ` at shift `i` (C33 `XFam`):
`layer (XFam λ i) j = 2 ^ #{e ∈ famExps λ i : j < e} · (2 if i = 0 else 1)` (the extra factor is
the `ℤ_2` at shift `0`; auxiliary for (E1) of `C36_the_podium_corollary.md`). -/
lemma layer_XFam (lam i j : ℕ) :
    layer (MainTheorem.XFam lam i) j =
      2 ^ (famExps lam i).countP (fun e => j < e) * (if i = 0 then 2 else 1) := by
  rcases i with _ | i
  · change layer (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))) j = _
    rw [layer_prod, layer_SC, layer_prod, layer_padic,
      layer_pi_Q _ (fun q => (FamilyGroup.yPool0 (ds lam) q).toNat), famExps,
      Multiset.countP_add, countP_smallExps, bigExps, countP_map_range, MainTheorem.S3_card,
      if_pos rfl, pow_add]
    ring
  · change layer (FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)) j = _
    rw [layer_prod, layer_SC, layer_pi_Q _ (fun p => (FamilyGroup.yPool (ds lam) (i + 1) p).toNat),
      famExps, Multiset.countP_add, countP_smallExps, bigExps, countP_map_range,
      MainTheorem.S3_card, if_neg (by omega), pow_add, mul_one]

/-! ### (E1) -/

/-- **(E1)** of `C36_the_podium_corollary.md`: for `n ≥ 1` and every `j`,
`layer (S n) j = 2 ^ #{e ∈ exps n : j < e}` (`S n = Syl2 (K n)`).  From C33 (M2), (D1) and the
cancellation of the two factors `ℤ_2`. -/
theorem E1 (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    layer (CubeLaplacian.Syl2 (CubeLaplacian.K n)) j =
      2 ^ ((exps n).countP (fun e => j < e)) := by
  obtain ⟨e⟩ := MainTheorem.M2 n hn
  have h := layer_congr e j
  rw [layer_prod, layer_padic, layer_pi] at h
  simp_rw [layer_XFam, List.get_eq_getElem] at h
  have hF := Fin.prod_univ_fun_getElem (FamDec.L n) (fun lam =>
    2 ^ (famExps lam ((n - lam) / 2)).countP (fun e => j < e) *
      (if (n - lam) / 2 = 0 then 2 else 1))
  simp only at hF
  have h1 : (FamDec.L n).count n = 1 := FamDec.m_self n
  have hprod : ((FamDec.L n).map (fun lam => if (n - lam) / 2 = 0 then 2 else 1)).prod = 2 := by
    rw [List.map_congr_left (g := fun lam => if lam = n then 2 else 1) (fun lam hlam => by
      have := FamDec.M3 n hn lam hlam
      show (if (n - lam) / 2 = 0 then 2 else 1) = (if lam = n then 2 else 1)
      by_cases h : lam = n
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]), prod_map_ite_eq, h1, pow_one]
  rw [hF, List.prod_map_mul, prod_map_two_pow, hprod] at h
  rw [exps, countP_list_sum, List.map_map]
  have : (fun lam => (famExps lam ((n - lam) / 2)).countP (fun e => j < e)) =
      Multiset.countP (fun e => j < e) ∘ (fun lam => famExps lam ((n - lam) / 2)) := rfl
  rw [← this]
  omega

/-! ### (E2), (E3) in general -/

/-- The general form of (E2) of `C36_the_podium_corollary.md`: if
`layer G j = 2 ^ #{x ∈ M : j < x}` for every `j`, then for `r, e ≥ 1`,
`e ≤ cExp G r ↔ r ≤ #{x ∈ M : e ≤ x}`. -/
theorem cExp_le_iff (G : Type*) [AddCommGroup G] (M : Multiset ℕ)
    (hM : ∀ j, layer G j = 2 ^ M.countP (fun x => j < x)) (r e : ℕ) (hr : 1 ≤ r) (he : 1 ≤ e) :
    e ≤ cExp G r ↔ r ≤ M.countP (fun x => e ≤ x) := by
  set S := {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ layer G (e - 1)} with hS
  have hmem : ∀ e, e ∈ S ↔ 1 ≤ e ∧ r ≤ M.countP (fun x => e ≤ x) := by
    intro e
    simp only [hS, Set.mem_setOf_eq, hM]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
      convert this using 2
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, Nat.pow_le_pow_right (by norm_num) ?_⟩
      convert h2 using 2
      omega
  have hbdd : BddAbove S := by
    refine ⟨M.sum, fun e he => ?_⟩
    obtain ⟨h1, h2⟩ := (hmem e).1 he
    have hpos : 0 < M.countP (fun x => e ≤ x) := by omega
    obtain ⟨x, hx, hex⟩ := Multiset.countP_pos.1 hpos
    exact hex.trans (Multiset.le_sum_of_mem hx)
  unfold cExp
  rw [← hS]
  constructor
  · intro h
    have hne : S.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, csSup_empty] at h
      simp at h
      omega
    have hm := (hmem _).1 (Nat.sSup_mem hne hbdd)
    exact hm.2.trans (countP_mono _ _ _ fun x hx => h.trans hx)
  · intro h
    exact le_csSup hbdd ((hmem e).2 ⟨he, h⟩)

/-- In a list sorted in decreasing order, for `r, e ≥ 1`: `e ≤ l[r − 1]` (`0` past the end) iff at
least `r` elements are `≥ e` (auxiliary for (E3) of `C36_the_podium_corollary.md`). -/
lemma le_getD_iff (l : List ℕ) (hl : l.Pairwise (fun a b => b ≤ a)) (r e : ℕ) (hr : 1 ≤ r)
    (he : 1 ≤ e) : e ≤ l.getD (r - 1) 0 ↔ r ≤ l.countP (fun x => e ≤ x) := by
  induction l generalizing r with
  | nil => simp; omega
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    have hzero : ¬ e ≤ a → t.countP (fun x => e ≤ x) = 0 := fun hea =>
      List.countP_eq_zero.2 fun x hx => by have := hl.1 x hx; simp; omega
    rw [List.countP_cons]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rcases r' with _ | r'
    · simp only [Nat.add_sub_cancel, List.getD_cons_zero]
      by_cases hea : e ≤ a
      · simp [hea]
      · simp [hea, hzero hea]
    · rw [show r' + 1 + 1 - 1 = r' + 1 by omega, List.getD_cons_succ]
      have := ih hl.2 (r' + 1) (by omega)
      rw [show r' + 1 - 1 = r' by omega] at this
      rw [this]
      by_cases hea : e ≤ a
      · simp [hea]
      · simp [hea, hzero hea]

/-- Two natural numbers with the same positive lower bounds are equal (auxiliary for (E3) of
`C36_the_podium_corollary.md`). -/
lemma eq_of_forall_pos_le_iff {x y : ℕ} (h : ∀ e, 1 ≤ e → (e ≤ x ↔ e ≤ y)) : x = y := by
  by_contra hxy
  rcases Nat.lt_or_gt_of_ne hxy with hl | hl
  · have := (h y (by omega)).2 le_rfl; omega
  · have := (h x (by omega)).1 le_rfl; omega

/-- The general form of (E3) of `C36_the_podium_corollary.md`: if
`layer G j = 2 ^ #{x ∈ M : j < x}` for every `j`, then for `r ≥ 1`, `cExp G r` is the `r`-th
largest element of `M` (`0` if `M` has fewer than `r` elements). -/
theorem cExp_eq_getD (G : Type*) [AddCommGroup G] (M : Multiset ℕ)
    (hM : ∀ j, layer G j = 2 ^ M.countP (fun x => j < x)) (r : ℕ) (hr : 1 ≤ r) :
    cExp G r = (M.sort (fun a b => b ≤ a)).getD (r - 1) 0 := by
  refine eq_of_forall_pos_le_iff fun e he => ?_
  rw [cExp_le_iff G M hM r e hr he,
    le_getD_iff _ (Multiset.pairwise_sort M (fun a b => b ≤ a)) r e hr he]
  conv_lhs => rw [← Multiset.sort_eq M (fun a b => b ≤ a)]
  rw [Multiset.coe_countP]

/-! ### (E2), (E3) -/

/-- **(E2)** of `C36_the_podium_corollary.md`: for `n ≥ 1` and `r, e ≥ 1`,
`e ≤ cExp (S n) r ↔ r ≤ #{x ∈ exps n : e ≤ x}`. -/
theorem E2 (n : ℕ) (hn : 1 ≤ n) (r e : ℕ) (hr : 1 ≤ r) (he : 1 ≤ e) :
    e ≤ cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r ↔
      r ≤ (exps n).countP (fun x => e ≤ x) :=
  cExp_le_iff _ _ (E1 n hn) r e hr he

/-- **(E3)** of `C36_the_podium_corollary.md`: for `n ≥ 1` and `r ≥ 1`, `cExp (S n) r` is the
`r`-th largest exponent, `((exps n).sort (· ≥ ·)).getD (r − 1) 0`. -/
theorem E3 (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : 1 ≤ r) :
    cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r =
      ((exps n).sort (fun a b => b ≤ a)).getD (r - 1) 0 :=
  cExp_eq_getD _ _ (E1 n hn) r hr

end PodiumCor
