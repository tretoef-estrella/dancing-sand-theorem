module

public import RequestProject.BaiCounts.Clocks
public import RequestProject.BaiCounts.Counts

/-!
# `C34_bais_counts.md`: Part F — the layers of one family

Encodings (namespace `BaiCounts`):

* `l0`, `l1` are the layers of `Layers.lean` (`ℓ_0(G) = |G/2G|`, `ℓ_1(G) = |2G/4G|`).
* `XFam lam i` is C33's group of the family `λ` at shift `i` (with its product additive group
  structure); `FamilyGroup.SC` are the small clocks and `FamilyGroup.Q e` the big clocks of C16.
* `c1 lam` is `c₁(λ)` (see `Counts.lean`).
-/

@[expose] public section

namespace BaiCounts

open Finset Families

/-! ### Layers of the clocks -/

/-- `ℓ_0(Q e) = 2` for `e ≥ 1` (Part F sketch of `C34_bais_counts.md`). -/
lemma l0_Qf {e : ℕ} (he : 1 ≤ e) : l0 (FamilyGroup.Q e) = 2 := l0_Q he

/-- `ℓ_1(Q e) = 2` for `e ≥ 2` (Part F sketch of `C34_bais_counts.md`). -/
lemma l1_Qf {e : ℕ} (he : 2 ≤ e) : l1 (FamilyGroup.Q e) = 2 := l1_Q he

/-- `ℓ_0(Q a) = 2` for `a ≥ 1` and `1` for `a = 0` (Part F sketch of `C34_bais_counts.md`; the case `a = 0` by C33 `S4_Q0`). -/
lemma l0_Q_ite (a : ℕ) : l0 (FamilyGroup.Q a) = 2 ^ (if 1 ≤ a then 1 else 0) := by
  split_ifs with h
  · rw [pow_one]; exact l0_Qf h
  · obtain rfl : a = 0 := by omega
    haveI := MainTheorem.S4_Q0
    exact l0_of_subsingleton _

/-- `ℓ_1(Q a) = 2` for `a ≥ 2` and `1` for `a ≤ 1` (Part F sketch of `C34_bais_counts.md`). -/
lemma l1_Q_ite (a : ℕ) : l1 (FamilyGroup.Q a) = 2 ^ (if 2 ≤ a then 1 else 0) := by
  split_ifs with h
  · rw [pow_one]; exact l1_Qf h
  · exact l1_Q_le_one (by omega)

/-- `ℓ_0` of the small clocks (auxiliary for (F1) of `C34_bais_counts.md`), from C33 (S4) and
(S4) `Q 0 = 0`. -/
lemma l0_SC (ds : List Bool) :
    l0 (FamilyGroup.SC ds) = 2 ^ ∑ a ∈ range ds.length,
      (if 1 ≤ a then 1 else 0) * 2 ^ (ds.length + Dance.mCount ds - 1 - a) := by
  rw [l0_congr (MainTheorem.S4equiv ds).toAddEquiv, l0_pi]
  simp_rw [l0_pi, l0_Q_ite, prod_const, card_univ, Fintype.card_fin, ← pow_mul,
    prod_pow_eq_pow_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (if 1 ≤ a then 1 else 0) *
    2 ^ (ds.length + Dance.mCount ds - 1 - a))]

/-- `ℓ_1` of the small clocks (auxiliary for (F2) of `C34_bais_counts.md`). -/
lemma l1_SC (ds : List Bool) :
    l1 (FamilyGroup.SC ds) = 2 ^ ∑ a ∈ range ds.length,
      (if 2 ≤ a then 1 else 0) * 2 ^ (ds.length + Dance.mCount ds - 1 - a) := by
  rw [l1_congr (MainTheorem.S4equiv ds).toAddEquiv, l1_pi]
  simp_rw [l1_pi, l1_Q_ite, prod_const, card_univ, Fintype.card_fin, ← pow_mul,
    prod_pow_eq_pow_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => (if 2 ≤ a then 1 else 0) *
    2 ^ (ds.length + Dance.mCount ds - 1 - a))]

/-! ### Geometric sums -/

/-- A geometric sum `Σ_{a<j} 2^{j+m−1−a} + 2^m = 2^{j+m}` (auxiliary for Part F of `C34_bais_counts.md`). -/
lemma geom1 (j m : ℕ) : ∑ a ∈ range j, 2 ^ (j + m - (a + 1)) + 2 ^ m = 2 ^ (j + m) := by
  induction j generalizing m with
  | zero => simp
  | succ j ih =>
    have h := ih (m + 1)
    rw [sum_range_succ, show j + 1 + m - (j + 1) = m by omega]
    rw [show ∑ a ∈ range j, 2 ^ (j + 1 + m - (a + 1)) =
      ∑ a ∈ range j, 2 ^ (j + (m + 1) - (a + 1)) from
        sum_congr rfl fun a _ => by rw [show j + 1 + m = j + (m + 1) by ring]]
    rw [show j + 1 + m = j + (m + 1) by ring, pow_succ 2 m] at *
    omega

/-- `Σ_{a=1}^{k−1} 2^{k+m−1−a} + 2^m = 2^{k+m−1}` (Part F sketch of `C34_bais_counts.md`). -/
lemma sum1 (k m : ℕ) (hk : 1 ≤ k) :
    ∑ a ∈ range k, (if 1 ≤ a then 1 else 0) * 2 ^ (k + m - 1 - a) + 2 ^ m = 2 ^ (k + m - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [sum_range_succ']
  simp only [le_add_iff_nonneg_left, zero_le, if_true, one_mul, nonpos_iff_eq_zero,
    one_ne_zero, if_false, zero_mul, add_zero]
  rw [show j + 1 + m - 1 = j + m by omega, ← geom1 j m]

/-- `Σ_{a=2}^{k−1} 2^{k+m−1−a} + c₁ + 2^m = 2^{k+m−1}` (Part F sketch of
`C34_bais_counts.md`). -/
lemma sum2 (k m : ℕ) (hk : 1 ≤ k) :
    ∑ a ∈ range k, (if 2 ≤ a then 1 else 0) * 2 ^ (k + m - 1 - a) +
      (if 2 ≤ k then 2 ^ (m + k - 2) else 0) + 2 ^ m = 2 ^ (k + m - 1) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [sum_range_succ', sum_range_succ', if_pos h]
    have e : ∀ a ∈ range j, (if 2 ≤ a + 1 + 1 then 1 else 0) * 2 ^ (j + 2 + m - 1 - (a + 1 + 1)) =
        2 ^ (j + m - (a + 1)) := fun a _ => by
      rw [if_pos (by omega), one_mul, show j + 2 + m - 1 - (a + 1 + 1) = j + m - (a + 1) by omega]
    rw [sum_congr rfl e, if_neg (by omega), if_neg (by omega),
      show m + (j + 2) - 2 = j + m by omega, show j + 2 + m - 1 = (j + m) + 1 by omega, pow_succ]
    have hg := geom1 j m
    omega

/-! ### (F1), (F2) -/

/-- **(F1)** of `C34_bais_counts.md`: for `λ ≥ 1` and every `i`,
`ℓ_0 (XFam λ i) = 2 ^ (2 ^ (mCount (ds λ) + (ds λ).length − 1))`. -/
theorem F1 (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    l0 (MainTheorem.XFam lam i) = 2 ^ (2 ^ (Dance.mCount (ds lam) + (ds lam).length - 1)) := by
  have hk := MainTheorem.S2_length lam hlam
  have hs := sum1 (ds lam).length (Dance.mCount (ds lam)) hk
  rw [show Dance.mCount (ds lam) + (ds lam).length - 1 =
    (ds lam).length + Dance.mCount (ds lam) - 1 by omega]
  have hN : 1 ≤ 2 ^ Dance.mCount (ds lam) := Nat.one_le_two_pow
  rcases i with _ | i
  · change l0 (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))) = _
    rw [l0_prod, l0_SC, l0_prod, l0_pi, l0_padic,
      prod_congr rfl fun q _ => l0_Qf (by have := A3_zero lam hlam q q.2; omega),
      prod_const, card_univ, Fintype.card_fin, ← pow_succ', ← pow_add,
      show 2 ^ Dance.mCount (ds lam) - 1 + 1 = 2 ^ Dance.mCount (ds lam) by omega, hs.symm]
  · change l0 (FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)) = _
    rw [l0_prod, l0_SC, l0_pi,
      prod_congr rfl fun p _ => l0_Qf (by have := A3_pos lam hlam (i + 1) (by omega) p p.2; omega),
      prod_const, card_univ, Fintype.card_fin, ← pow_add, hs.symm]

/-- **(F2)** of `C34_bais_counts.md`: for `λ ≥ 1` and every `i`,
`ℓ_1 (XFam λ i) = 2 ^ (2 ^ (mCount (ds λ) + (ds λ).length − 1) − c₁(λ))`. -/
theorem F2 (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    l1 (MainTheorem.XFam lam i) =
      2 ^ (2 ^ (Dance.mCount (ds lam) + (ds lam).length - 1) - c1 lam) := by
  have hk := MainTheorem.S2_length lam hlam
  have hs := sum2 (ds lam).length (Dance.mCount (ds lam)) hk
  rw [show Dance.mCount (ds lam) + (ds lam).length - 1 =
    (ds lam).length + Dance.mCount (ds lam) - 1 by omega]
  have hc : c1 lam = if 2 ≤ (ds lam).length then
      2 ^ (Dance.mCount (ds lam) + (ds lam).length - 2) else 0 := rfl
  rw [← hc] at hs
  have hN : 1 ≤ 2 ^ Dance.mCount (ds lam) := Nat.one_le_two_pow
  rcases i with _ | i
  · change l1 (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))) = _
    rw [l1_prod, l1_SC, l1_prod, l1_pi, l1_padic,
      prod_congr rfl fun q _ => l1_Qf (by have := A3_zero lam hlam q q.2; omega),
      prod_const, card_univ, Fintype.card_fin, ← pow_succ', ← pow_add,
      show 2 ^ Dance.mCount (ds lam) - 1 + 1 = 2 ^ Dance.mCount (ds lam) by omega]
    congr 1
    omega
  · change l1 (FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)) = _
    rw [l1_prod, l1_SC, l1_pi,
      prod_congr rfl fun p _ => l1_Qf (by have := A3_pos lam hlam (i + 1) (by omega) p p.2; omega),
      prod_const, card_univ, Fintype.card_fin, ← pow_add]
    congr 1
    omega

end BaiCounts
