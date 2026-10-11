module

public import RequestProject.PodiumCor.Bounds
public import RequestProject.PodiumCor.Dictionary
public import RequestProject.PodiumCor.Mult

/-!
# `C36_the_podium_corollary.md`: counting the exponents (auxiliary for Part P)

By (E2) the exponents `c_r` of `S n = Syl2 (K n)` are read off from the counts
`#{x ∈ exps n : e ≤ x}`.  This file bounds these counts with the results of Part B: above
`G = gmax (n − 1)` only the `m (n − 2) n` copies of `yPool (ds (n − 2)) 1 0` and the single
`yPool0 (ds n) 0` can occur (`upper_count`), and the families `n − 4`, `n − 2`, `n` give lower
bounds (`lower_count`).  `famCount n e λ` is the number of exponents `≥ e` of the family `λ` at
its shift `(n − λ)/2`.
-/

@[expose] public section

namespace PodiumCor

open Finset Families

/-- The number of exponents `≥ e` of the family `λ` at shift `(n − λ)/2` (auxiliary for Part P of
`C36_the_podium_corollary.md`). -/
noncomputable def famCount (n e lam : ℕ) : ℕ :=
  (famExps lam ((n - lam) / 2)).countP (fun x => e ≤ x)

/-- `#{x ∈ exps n : e ≤ x} = Σ_{λ ∈ L n} famCount n e λ` (auxiliary for Part P of
`C36_the_podium_corollary.md`). -/
lemma countP_exps (n e : ℕ) :
    (exps n).countP (fun x => e ≤ x) = ((FamDec.L n).map (famCount n e)).sum := by
  rw [exps, countP_list_sum, List.map_map]; rfl

/-- Reading off `c_r` from two counts, via (E2) (auxiliary for Part P of
`C36_the_podium_corollary.md`). -/
lemma cExp_eq_of_counts (n r : ℕ) (T : ℤ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hT : 1 ≤ T)
    (h1 : r ≤ (exps n).countP (fun x => T.toNat ≤ x))
    (h2 : (exps n).countP (fun x => T.toNat + 1 ≤ x) < r) :
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = T := by
  have a := (E2 n hn r T.toNat hr (by omega)).2 h1
  have b : ¬ (T.toNat + 1 ≤ cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r) := fun h =>
    absurd ((E2 n hn r (T.toNat + 1) hr (by omega)).1 h) (by omega)
  omega

/-- A list sum is monotone (auxiliary). -/
lemma list_sum_map_mono (l : List ℕ) (f g : ℕ → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- `Σ_{x ∈ S} count x l · f x ≤ Σ_{x ∈ l} f x` (auxiliary). -/
lemma sum_count_le (l : List ℕ) (f : ℕ → ℕ) (S : Finset ℕ) :
    ∑ x ∈ S, l.count x * f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
    have : ∑ x ∈ S, (if (a == x) = true then 1 else 0) * f x ≤ f a := by
      simp only [beq_iff_eq, ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq]
      split_ifs <;> simp
    omega

/-! ### Upper bounds above `G` -/

/-- Above `G`, the family `λ ∈ L n` has no small exponent (from (B0)). -/
lemma small_count_zero (n lam e : ℕ) (hn : 4 ≤ n) (hlam : lam ∈ FamDec.L n)
    (he : gmax (n - 1) < e) : (smallExps lam).countP (fun x => e ≤ x) = 0 := by
  have hm : FamDec.m lam n ≠ 0 := (List.count_pos_iff.2 hlam).ne'
  have hsupp := FamDec.M3 n (by omega) lam hlam
  have hB0 := B0 n lam hn hsupp.1 hm
  unfold smallExps
  rw [countP_finset_sum]
  refine sum_eq_zero fun a ha => ?_
  rw [countP_replicate, if_neg]
  simp only [mem_Ico] at ha
  omega

/-- Above `G`, a family `λ ∈ L n` with shift `≥ 2` has no exponent (from (B0), (B1)). -/
lemma famCount_far (n e lam : ℕ) (hn : 4 ≤ n) (hlam : lam ∈ FamDec.L n)
    (hi : 2 ≤ (n - lam) / 2) (he : gmax (n - 1) < e) : famCount n e lam = 0 := by
  have hm : FamDec.m lam n ≠ 0 := (List.count_pos_iff.2 hlam).ne'
  have hsupp := FamDec.M3 n (by omega) lam hlam
  have hG := gmax_ge (n - 1) (by omega)
  unfold famCount famExps
  rw [Multiset.countP_add, small_count_zero n lam e hn hlam he, zero_add]
  obtain ⟨i, hi'⟩ : ∃ i, (n - lam) / 2 = i + 1 := ⟨(n - lam) / 2 - 1, by omega⟩
  rw [hi', bigExps, countP_map_range]
  refine sum_eq_zero fun p hp => if_neg ?_
  have := B1 n lam hn hsupp.1 hm hi p (by rw [← MainTheorem.S3_card]; exact mem_range.1 hp)
  rw [hi'] at this
  omega

/-- `n − 2 ∈ L n` for `n ≥ 4` (from (L2)). -/
lemma mem_L_n2 (n : ℕ) (hn : 4 ≤ n) : n - 2 ∈ FamDec.L n := by
  have := L2 n (by omega)
  apply List.count_pos_iff.1
  change 0 < FamDec.m (n - 2) n
  rw [this]; split_ifs <;> omega

/-- `n ∈ L n` (from C31 `m_self`). -/
lemma mem_L_self (n : ℕ) : n ∈ FamDec.L n :=
  List.count_pos_iff.1 (by have := FamDec.m_self n; unfold FamDec.m at this; omega)

/-- Above `G`, the family `n − 2` has at most the exponent `yPool (ds (n − 2)) 1 0` (from (B2)). -/
lemma famCount_n2_le (n e : ℕ) (hn : 4 ≤ n) (he : gmax (n - 1) < e) :
    famCount n e (n - 2) ≤ if (e : ℤ) ≤ FamilyGroup.yPool (ds (n - 2)) 1 0 then 1 else 0 := by
  have hG := gmax_ge (n - 1) (by omega)
  unfold famCount famExps
  rw [show (n - (n - 2)) / 2 = 0 + 1 by omega, Multiset.countP_add,
    small_count_zero n (n - 2) e hn (mem_L_n2 n hn) he, zero_add, bigExps, countP_map_range,
    Nat.zero_add, sum_eq_single 0]
  · split_ifs <;> omega
  · intro p hp hp0
    have := (B2 n hn).2 p (by omega) (by rw [← MainTheorem.S3_card]; exact mem_range.1 hp)
    rw [if_neg (by omega)]
  · intro h; exact absurd (mem_range.2 (Nat.two_pow_pos _)) h

/-- Above `G`, the family `n` has at most the exponent `yPool0 (ds n) 0`, if `s ≥ 1` (from (B3)). -/
lemma famCount_n_le (n e : ℕ) (X : ℤ) (hn : 4 ≤ n) (he : gmax (n - 1) < e)
    (hX : 1 ≤ (Windows.Ids (ds n)).card → FamilyGroup.yPool0 (ds n) 0 ≤ X) :
    famCount n e n ≤ if (e : ℤ) ≤ X then 1 else 0 := by
  have hG := gmax_ge (n - 1) (by omega)
  unfold famCount famExps
  rw [Nat.sub_self, Nat.zero_div, Multiset.countP_add,
    small_count_zero n n e hn (mem_L_self n) he, zero_add, bigExps, countP_map_range]
  rcases Nat.eq_zero_or_pos (Windows.Ids (ds n)).card with h0 | hpos
  · rw [h0]; simp
  · rw [sum_eq_single 0]
    · have := hX hpos
      split_ifs <;> omega
    · intro q hq hq0
      have := (B3 n hn).1 q (by omega) (by rw [← MainTheorem.S3_card]; exact mem_range.1 hq)
      rw [if_neg (by omega)]
    · intro h
      have : 2 ≤ 2 ^ (Windows.Ids (ds n)).card :=
        (Nat.pow_le_pow_right (by norm_num) hpos).trans_eq' (by norm_num)
      exact absurd (mem_range.2 (by omega)) h

/-- Above `G` (`e > G`), `#{x ∈ exps n : e ≤ x} ≤ m (n − 2) n · [e ≤ yPool (ds (n − 2)) 1 0] +
[e ≤ X]` for any `X` bounding `yPool0 (ds n) 0` when `s ≥ 1` (auxiliary for Part P of
`C36_the_podium_corollary.md`). -/
lemma upper_count (n e : ℕ) (X : ℤ) (hn : 4 ≤ n) (he : gmax (n - 1) < e)
    (hX : 1 ≤ (Windows.Ids (ds n)).card → FamilyGroup.yPool0 (ds n) 0 ≤ X) :
    (exps n).countP (fun x => e ≤ x) ≤
      FamDec.m (n - 2) n * (if (e : ℤ) ≤ FamilyGroup.yPool (ds (n - 2)) 1 0 then 1 else 0) +
        (if (e : ℤ) ≤ X then 1 else 0) := by
  rw [countP_exps]
  refine (list_sum_map_mono _ _ (fun lam =>
    (if lam = n - 2 then (if (e : ℤ) ≤ FamilyGroup.yPool (ds (n - 2)) 1 0 then 1 else 0) else 0) +
      (if lam = n then (if (e : ℤ) ≤ X then 1 else 0) else 0)) fun lam hlam => ?_).trans ?_
  · have hsupp := FamDec.M3 n (by omega) lam hlam
    dsimp only
    by_cases h1 : lam = n - 2
    · subst h1; rw [if_pos rfl, if_neg (show n - 2 ≠ n by omega), add_zero]; exact famCount_n2_le n e hn he
    by_cases h2 : lam = n
    · subst h2; rw [if_neg h1, if_pos rfl, zero_add]; exact famCount_n_le lam e X hn he hX
    · rw [if_neg h1, if_neg h2, famCount_far n e lam hn hlam (by omega) he]
  · rw [List.sum_map_add, FamDec.sum_map_eq_count_mul _ _ (n - 2) _ (fun _ _ => rfl),
      FamDec.sum_map_eq_count_mul _ _ n _ (fun _ _ => rfl)]
    have := FamDec.m_self n
    unfold FamDec.m at this ⊢
    rw [this, one_mul]

/-! ### Lower bounds -/

/-- The families `n − 4`, `n − 2`, `n` contribute
`m (n − 4) n · famCount (n − 4) + m (n − 2) n · famCount (n − 2) + famCount n` (auxiliary for
Part P of `C36_the_podium_corollary.md`). -/
lemma lower_count (n e : ℕ) (hn : 4 ≤ n) :
    FamDec.m (n - 4) n * famCount n e (n - 4) + FamDec.m (n - 2) n * famCount n e (n - 2) +
      famCount n e n ≤ (exps n).countP (fun x => e ≤ x) := by
  rw [countP_exps]
  have := sum_count_le (FamDec.L n) (famCount n e) {n - 4, n - 2, n}
  rw [sum_insert (by simp; omega), sum_insert (by simp; omega), sum_singleton] at this
  have h1 := FamDec.m_self n
  unfold FamDec.m at h1 ⊢
  rw [h1, one_mul] at this
  omega

/-- One exponent `≥ e` among the big clocks at `0` (auxiliary). -/
lemma big_ge_one (m : ℕ) (hm : 1 ≤ m) (h : ℕ → ℤ) (e : ℕ) (h0 : (e : ℤ) ≤ h 0) :
    1 ≤ ((range m).val.map (fun p => (h p).toNat)).countP (fun x => e ≤ x) := by
  rw [countP_map_range]
  have := single_le_sum (f := fun p => if e ≤ (h p).toNat then 1 else 0)
    (fun _ _ => Nat.zero_le _) (mem_range.2 (show 0 < m by omega))
  simp only at this
  rw [if_pos (by omega)] at this
  exact this

/-- Two exponents `≥ e` among the big clocks at `0`, `1` (auxiliary). -/
lemma big_ge_two (m : ℕ) (hm : 2 ≤ m) (h : ℕ → ℤ) (e : ℕ) (h0 : (e : ℤ) ≤ h 0)
    (h1 : (e : ℤ) ≤ h 1) :
    2 ≤ ((range m).val.map (fun p => (h p).toNat)).countP (fun x => e ≤ x) := by
  rw [countP_map_range]
  have := sum_le_sum_of_subset (f := fun p => if e ≤ (h p).toNat then 1 else 0)
    (show ({0, 1} : Finset ℕ) ⊆ range m by intro x hx; simp at hx; simp; omega)
  rw [sum_pair (by norm_num)] at this
  simp only at this
  rw [if_pos (by omega), if_pos (by omega)] at this
  exact this

/-- `1 ≤ famCount n e (n − 2)` if `e ≤ yPool (ds (n − 2)) 1 0` (auxiliary). -/
lemma famCount_n2_ge_one (n e : ℕ) (hn : 4 ≤ n)
    (h : (e : ℤ) ≤ FamilyGroup.yPool (ds (n - 2)) 1 0) : 1 ≤ famCount n e (n - 2) := by
  unfold famCount famExps
  rw [show (n - (n - 2)) / 2 = 0 + 1 by omega, Multiset.countP_add, bigExps]
  have := big_ge_one (2 ^ (Windows.Ids (ds (n - 2))).card) Nat.one_le_two_pow
    (fun p => FamilyGroup.yPool (ds (n - 2)) (0 + 1) p) e h
  beta_reduce at this
  omega

/-- `2 ≤ famCount n e (n − 2)` for even `n` and `e ≤ G` (from (B7); auxiliary). -/
lemma famCount_n2_ge_two (n e : ℕ) (hn : 4 ≤ n) (hev : n % 2 = 0)
    (h : (e : ℤ) ≤ gmax (n - 1)) : 2 ≤ famCount n e (n - 2) := by
  obtain ⟨h0, h1, hN⟩ := B7 n hn hev
  unfold famCount famExps
  rw [show (n - (n - 2)) / 2 = 0 + 1 by omega, Multiset.countP_add, bigExps]
  have := big_ge_two (2 ^ (Windows.Ids (ds (n - 2))).card) (by rw [MainTheorem.S3_card]; exact hN)
    (fun p => FamilyGroup.yPool (ds (n - 2)) (0 + 1) p) e (by simp only; rw [h0]; exact h)
    (by simp only; rw [h1]; exact h)
  beta_reduce at this
  omega

/-- `1 ≤ famCount n e (n − 4)` if `e ≤ yPool (ds (n − 4)) 2 0` (auxiliary). -/
lemma famCount_n4_ge_one (n e : ℕ) (hn : 4 ≤ n)
    (h : (e : ℤ) ≤ FamilyGroup.yPool (ds (n - 4)) 2 0) : 1 ≤ famCount n e (n - 4) := by
  unfold famCount famExps
  rw [show (n - (n - 4)) / 2 = 1 + 1 by omega, Multiset.countP_add, bigExps]
  have := big_ge_one (2 ^ (Windows.Ids (ds (n - 4))).card) Nat.one_le_two_pow
    (fun p => FamilyGroup.yPool (ds (n - 4)) (1 + 1) p) e h
  beta_reduce at this
  omega

/-- `1 ≤ famCount n e n` if `s ≥ 1` and `e ≤ yPool0 (ds n) 0` (auxiliary). -/
lemma famCount_n_ge_one (n e : ℕ) (hs : 1 ≤ (Windows.Ids (ds n)).card)
    (h : (e : ℤ) ≤ FamilyGroup.yPool0 (ds n) 0) : 1 ≤ famCount n e n := by
  unfold famCount famExps
  rw [Nat.sub_self, Nat.zero_div, Multiset.countP_add, bigExps]
  have h2 : 2 ≤ 2 ^ (Windows.Ids (ds n)).card :=
    (Nat.pow_le_pow_right (by norm_num) hs).trans_eq' (by norm_num)
  have := big_ge_one (2 ^ (Windows.Ids (ds n)).card - 1) (by omega)
    (fun q => FamilyGroup.yPool0 (ds n) q) e h
  beta_reduce at this
  omega

end PodiumCor
