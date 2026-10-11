module

public import RequestProject.Mirror.Families
public import RequestProject.Mirror.Clocks

/-!
# `C37_the_mirror_that_doubles.md`: Part C — Theorem 9.10 (the mirror that doubles)

Namespace `Mirror`.  For `e ≥ 1` and odd `λ < 2^e − 1`, the shift is `i = (2^e − 1 − λ) / 2`
(written out), `k = (ds λ).length`, `I = Windows.Ids (ds λ)`, `k' = (ds (λ + 1)).length`,
`I' = Windows.Ids (ds (λ + 1))` (all written out).  C33's `S1_succ`, `S3_subset` and C35's
`Podium.two_pow_dvd_oE` are used.
-/

@[expose] public section

namespace Mirror

open Finset Families Rulers

/-- If `2^{t+1} ∣ 2J + 2^t` and `J ≥ 1`, then `v₂(J) + 1 = t` (auxiliary for (C1) of
`C37_the_mirror_that_doubles.md`). -/
lemma v2_eq_of_dvd {J t : ℕ} (hJ : 1 ≤ J) (h : 2 ^ (t + 1) ∣ 2 * J + 2 ^ t) : v2 J + 1 = t := by
  have h1 : 2 ^ t ∣ 2 * J := by
    have : 2 ^ t ∣ 2 * J + 2 ^ t := (pow_dvd_pow 2 (Nat.le_succ t)).trans h
    exact (Nat.dvd_add_left (dvd_refl _)).1 this
  have h2 : ¬ 2 ^ (t + 1) ∣ 2 * J := by
    intro h2
    have : 2 ^ (t + 1) ∣ 2 ^ t := (Nat.dvd_add_right h2).1 h
    have := Nat.le_of_dvd (by positivity) this
    rw [pow_succ] at this
    have : 0 < 2 ^ t := by positivity
    omega
  have hne : 2 * J ≠ 0 := by omega
  rw [padicValNat_dvd_iff_le hne] at h1 h2
  rw [← v2_two_mul hJ]
  unfold v2
  omega

/-- The key valuation of (C1) of `C37_the_mirror_that_doubles.md`: if `I ⊆ range k`, `0 ∉ I`,
`k ≥ 1`, `D ⊆ I`, `2^k + o_I + 2i = 2^e` with `k < e`, and `i + o_D ≥ 1`, then
`v₂(i + o_D) + 1 = t₁`. -/
lemma v2_J_eq {k e i : ℕ} {I D : Finset ℕ} (hI : I ⊆ range k) (h0 : 0 ∉ I) (hD : D ⊆ I)
    (hke : k < e) (hsum : 2 ^ k + oE I + 2 * i = 2 ^ e) (hJ : 1 ≤ i + oE D) :
    v2 (i + oE D) + 1 = t1 k I := by
  apply v2_eq_of_dvd hJ
  set t := t1 k I with ht
  have htk : t ≤ k := by
    rcases I.eq_empty_or_nonempty with rfl | hne
    · rw [ht, t1, minOr_empty]
    · exact (mem_range.1 (hI (minOr_mem (k := k) hne))).le
  have hDt : 2 ^ t ∣ oE D := Podium.two_pow_dvd_oE fun u hu => minOr_le (hD hu)
  -- `A := 2^k + o_I + 2^t` is divisible by `2^{t+1}`
  have hA : 2 ^ (t + 1) ∣ 2 ^ k + oE I + 2 ^ t := by
    rcases I.eq_empty_or_nonempty with hIe | hne
    · have : t = k := by rw [ht, t1, hIe, minOr_empty]
      rw [hIe, oE_empty, this, add_zero, ← two_mul, ← pow_succ']
    · have htI : t ∈ I := minOr_mem hne
      have htk' : t < k := mem_range.1 (hI htI)
      have hsplit : oE I = 2 ^ t + oE (I.erase t) := by
        unfold oE; rw [add_sum_erase _ _ htI]
      have hE : 2 ^ (t + 1) ∣ oE (I.erase t) := Podium.two_pow_dvd_oE fun u hu => by
        have h1 : t ≤ u := minOr_le (mem_of_mem_erase hu)
        have h2 := ne_of_mem_erase hu
        omega
      rw [hsplit, show 2 ^ k + (2 ^ t + oE (I.erase t)) + 2 ^ t =
        2 ^ k + 2 ^ (t + 1) + oE (I.erase t) by rw [pow_succ]; ring]
      exact dvd_add (dvd_add (pow_dvd_pow 2 htk') (dvd_refl _)) hE
  have hB : 2 ^ (t + 1) ∣ 2 ^ e + 2 * oE D + 2 * 2 ^ t := by
    refine dvd_add (dvd_add (pow_dvd_pow 2 (by omega)) ?_) ?_
    · rw [pow_succ']; exact mul_dvd_mul_left 2 hDt
    · rw [pow_succ']
  have heq : (2 * (i + oE D) + 2 ^ t) + (2 ^ k + oE I + 2 ^ t) =
      2 ^ e + 2 * oE D + 2 * 2 ^ t := by omega
  rw [← heq] at hB
  exact (Nat.dvd_add_left hA).1 hB

/-- **(C1)** of `C37_the_mirror_that_doubles.md` (Theorem 9.10, the mirror that doubles): let
`e ≥ 1`, `λ` odd with `λ < 2^e − 1`, `i := (2^e − 1 − λ) / 2`, `k := (ds λ).length`,
`I := Ids (ds λ)`, `k' := (ds (λ + 1)).length`, `I' := Ids (ds (λ + 1))`.  For every `D ⊆ I`,
`clock k' I' i D = clock k I i D` and `clock k' I' i (insert 0 D) = clock k I i D`.
(The hypothesis `e ≥ 1` is kept as in the file; it follows from `λ < 2^e − 1`.) -/
theorem C1 (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1)
    {D : Finset ℕ} (hD : D ⊆ Windows.Ids (ds lam)) :
    clock (ds (lam + 1)).length (Windows.Ids (ds (lam + 1))) ((2 ^ e - 1 - lam) / 2) D =
        clock (ds lam).length (Windows.Ids (ds lam)) ((2 ^ e - 1 - lam) / 2) D ∧
      clock (ds (lam + 1)).length (Windows.Ids (ds (lam + 1))) ((2 ^ e - 1 - lam) / 2)
          (insert 0 D) =
        clock (ds lam).length (Windows.Ids (ds lam)) ((2 ^ e - 1 - lam) / 2) D := by
  rw [A2_length lam hodd, A2_Ids lam hodd]
  have h0 := A2_zero_notMem lam hodd
  have hIr := MainTheorem.S3_subset lam
  have hsucc := MainTheorem.S1_succ lam
  set k := (ds lam).length with hk
  set I := Windows.Ids (ds lam) with hI
  set i := (2 ^ e - 1 - lam) / 2 with hi
  have he2 : 2 ^ e % 2 = 0 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; omega
  have h2i : 2 * i = 2 ^ e - 1 - lam := by omega
  have hi1 : 1 ≤ i := by omega
  have hsumN : 2 ^ k + oE I + 2 * i = 2 ^ e := by omega
  have hoE : oE (insert 0 I) = oE I + 1 := by
    unfold oE; rw [sum_insert h0, pow_zero, add_comm]
  have hsumn : 2 ^ k + oE (insert 0 I) + 2 * i = 2 ^ e + 1 := by omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have : I = ∅ := eq_empty_of_forall_notMem fun t ht => by
        have := mem_range.1 (hIr ht); omega
      rw [this, oE_empty, h] at hsucc
      omega
    · exact h
  have hke : k < e := by
    have : 2 ^ k < 2 ^ e := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  have hIr' : insert 0 I ⊆ range k := insert_subset (mem_range.2 hk1) hIr
  have hJ : 1 ≤ i + oE D := by omega
  have hB1 := B1 k I hIr hD i e hsumN hJ
  refine ⟨?_, ?_⟩
  · rw [B2 k (insert 0 I) hIr' (hD.trans (subset_insert _ _)) i e hsumn hJ, hB1,
      A5_hSum k I h0 hD]
    have hs := s2_succ (i + oE D - 1)
    rw [Nat.sub_add_cancel hJ] at hs
    linarith
  · have hD' : insert 0 D ⊆ insert 0 I := insert_subset_insert _ hD
    have hoD : oE (insert 0 D) = oE D + 1 := by
      unfold oE; rw [sum_insert (fun h => h0 (hD h)), pow_zero, add_comm]
    rw [B2 k (insert 0 I) hIr' hD' i e hsumn (by omega), hB1, A5_hSum_insert k I hIr h0 hD,
      hoD, show i + (oE D + 1) - 1 = i + oE D by omega]
    have hv := v2_J_eq hIr h0 hD hke hsumN hJ
    have hv' : ((v2 (i + oE D) : ℕ) : ℤ) + 1 = (t1 k I : ℤ) := by exact_mod_cast hv
    push_cast
    linarith

end Mirror
