module

public import RequestProject.BaiCounts.Family

/-!
# `C34_bais_counts.md`: Part B — Corollary 1.5 (Bai's two counts)

Encodings (namespace `BaiCounts`):

* `S n := CubeLaplacian.Syl2 (CubeLaplacian.K n)` (C17), an additive subgroup viewed as an
  additive commutative group; it is written out in the statements.
* `aN n := 2 ^ (n − 2) − 2 ^ ((n − 2) / 2)` is the file's `a n` (natural-number subtraction, which
  does not truncate since `(n − 2) / 2 ≤ n − 2`).
* `l0`, `l1` are the layers of `Layers.lean`.
-/

@[expose] public section

namespace BaiCounts

open Finset Families

/-- *Part B* (B2) of `C34_bais_counts.md`: `a n := 2 ^ (n − 2) − 2 ^ ((n − 2) / 2)`, the number of
cyclic factors `ℤ/2` of `Syl_2 K(Q_n)`. -/
def aN (n : ℕ) : ℕ := 2 ^ (n - 2) - 2 ^ ((n - 2) / 2)

/-- `m 1 n = 0` for even `n ≥ 1` (by C31 (M3)); auxiliary for (B2) of `C34_bais_counts.md`. -/
lemma m_one_even (n : ℕ) (hn : 1 ≤ n) (he : n % 2 = 0) : FamDec.m 1 n = 0 :=
  List.count_eq_zero.2 fun h => by have := (FamDec.M3 n hn 1 h).2.2; omega

/-- `m 2 n = 0` for odd `n` (by C31 (M3)); auxiliary for (B2) of `C34_bais_counts.md`. -/
lemma m_two_odd (n : ℕ) (hn : 1 ≤ n) (ho : n % 2 = 1) : FamDec.m 2 n = 0 :=
  List.count_eq_zero.2 fun h => by have := (FamDec.M3 n hn 2 h).2.2; omega

/-- `Σ_j c₁(λ_j) = a n` for `n ≥ 2`, from (S3) and C31 (L3), (L4), (M3) (auxiliary for (B2) of
`C34_bais_counts.md`). -/
lemma sum_c1 (n : ℕ) (hn : 2 ≤ n) :
    ∑ j : Fin (FamDec.L n).length, c1 ((FamDec.L n).get j) = aN n := by
  have h := S3 n (by omega)
  rw [← sum_mul] at h
  have h4 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]; norm_num; ring
  have hle : 2 ^ ((n - 2) / 2) ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold aN
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · rw [m_one_even n (by omega) he, FamDec.L4 n (by omega) he] at h
    omega
  · rw [m_two_odd n (by omega) ho, FamDec.L3 n (by omega) ho,
      show (n - 1) / 2 = (n - 2) / 2 + 1 by omega, pow_succ] at h
    omega

/-- `Σ_j 2^{|I_j| + k_j − 1} = 2^{n−1}` for `n ≥ 1`, from (S2) (auxiliary for Part B of
`C34_bais_counts.md`). -/
lemma sum_half (n : ℕ) (hn : 1 ≤ n) :
    ∑ j : Fin (FamDec.L n).length,
      2 ^ (Dance.mCount (ds ((FamDec.L n).get j)) + (ds ((FamDec.L n).get j)).length - 1) =
        2 ^ (n - 1) := by
  have h := S2 n
  have e : ∀ j : Fin (FamDec.L n).length,
      2 ^ ((ds ((FamDec.L n).get j)).length + Dance.mCount (ds ((FamDec.L n).get j))) =
        2 * 2 ^ (Dance.mCount (ds ((FamDec.L n).get j)) +
          (ds ((FamDec.L n).get j)).length - 1) := fun j => by
    have hk := MainTheorem.S2_length _ (FamDec.M3 n hn _ (List.get_mem _ j)).1
    rw [← pow_succ']
    congr 1
    omega
  rw [sum_congr rfl fun j _ => e j, ← mul_sum] at h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ'] at h
  rw [Nat.add_sub_cancel]
  omega

/-- **(B1)** of `C34_bais_counts.md` (Corollary 1.5, Bai's first count): for every `n ≥ 1`,
`ℓ_0 (Syl2 (K n)) = 2 ^ (2 ^ (n − 1) − 1)`: `Syl_2 K(Q_n)` has exactly `2^{n−1} − 1` cyclic
factors.  From C33 (M2), the invariance and multiplicativity of `ℓ_0`, `ℓ_0(ℤ_[2]) = 2`, (F1) and
(S2). -/
theorem B1 (n : ℕ) (hn : 1 ≤ n) :
    l0 (CubeLaplacian.Syl2 (CubeLaplacian.K n)) = 2 ^ (2 ^ (n - 1) - 1) := by
  obtain ⟨e⟩ := MainTheorem.M2 n hn
  have h := l0_congr e
  rw [l0_prod, l0_padic, l0_pi,
    prod_congr rfl fun j _ => F1 _ (FamDec.M3 n hn _ (List.get_mem _ j)).1 _,
    prod_pow_eq_pow_sum, sum_half n hn] at h
  have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  rw [show 2 ^ (n - 1) = (2 ^ (n - 1) - 1) + 1 by omega, pow_succ'] at h
  omega

/-- **(B2)** of `C34_bais_counts.md` (Corollary 1.5, Bai's second count): for every `n ≥ 2`,
`ℓ_1 (Syl2 (K n)) = 2 ^ (2 ^ (n − 1) − 1 − a n)` with `a n = 2 ^ (n − 2) − 2 ^ ((n − 2) / 2)`:
exactly `a n` of the cyclic factors are `ℤ/2`.  From C33 (M2), the invariance and
multiplicativity of `ℓ_1`, `ℓ_1(ℤ_[2]) = 2`, (F2), (S2), (S3) and C31 (L3), (L4), (M3). -/
theorem B2 (n : ℕ) (hn : 2 ≤ n) :
    l1 (CubeLaplacian.Syl2 (CubeLaplacian.K n)) = 2 ^ (2 ^ (n - 1) - 1 - aN n) := by
  obtain ⟨e⟩ := MainTheorem.M2 n (by omega)
  have h := l1_congr e
  have hle : ∀ j ∈ (univ : Finset (Fin (FamDec.L n).length)), c1 ((FamDec.L n).get j) ≤
      2 ^ (Dance.mCount (ds ((FamDec.L n).get j)) + (ds ((FamDec.L n).get j)).length - 1) := by
    intro j _
    unfold c1
    split_ifs
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact Nat.zero_le _
  rw [l1_prod, l1_padic, l1_pi,
    prod_congr rfl fun j _ => F2 _ (FamDec.M3 n (by omega) _ (List.get_mem _ j)).1 _,
    prod_pow_eq_pow_sum, sum_tsub_distrib _ hle, sum_half n (by omega), sum_c1 n hn] at h
  have hX : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
  have hX1 : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
  have ha : aN n ≤ 2 ^ (n - 2) := Nat.sub_le _ _
  rw [show 2 ^ (n - 1) - aN n = (2 ^ (n - 1) - 1 - aN n) + 1 by omega, pow_succ'] at h
  omega

end BaiCounts
