module

public import RequestProject.Podium.Defs

/-!
# Lemma 9.2: the clearings and where `φ` is largest (`C35_the_podium_arithmetic.md`, *Part L*)

Encodings as in `Podium/Defs.lean`: `P I l` is `P_l`, `tAt k I l` is `t_{l+1}`, `Y k I l` is
`Y_l`, `clear N q` is `2^q ⌊N / 2^q⌋`, `psi k I E` is `ψ(E)`; `λ` is `Rulers.lam k I` and
`s = I.card`.  The hypothesis `I ⊆ {0, …, k − 1}` is `hI : I ⊆ Finset.range k`.
-/

@[expose] public section

namespace Podium

open Finset Rulers

variable {k : ℕ} {I : Finset ℕ}

lemma lt_of_subset_range (hI : I ⊆ range k) : ∀ t ∈ I, t < k :=
  fun _ ht => mem_range.1 (hI ht)

/-- The gaps of the tail `I ∖ P_l` add up to `k − t_{l+1}`. -/
lemma sum_h_sdiff_P (hI : ∀ t ∈ I, t < k) (l : ℕ) :
    ∑ t ∈ I \ P I l, (h k I t : ℤ) = k - tAt k I l := by
  by_cases hne : (I \ P I l).Nonempty
  · have hm : tAt k I l ∈ I := (mem_sdiff.1 (minOr_mem hne)).1
    rw [sdiff_P_eq_filter hI l, ← telescope_mem hI (fun t => (t : ℤ)) hm]
    exact sum_congr rfl fun t ht => h_cast hI (mem_filter.1 ht).1
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, sum_empty, tAt, hne, minOr_empty, sub_self]

/-- The gaps of the head `P_l` add up to `t_{l+1} − t_1`. -/
lemma sum_h_P (hI : ∀ t ∈ I, t < k) (l : ℕ) :
    ∑ t ∈ P I l, (h k I t : ℤ) = tAt k I l - minOr k I := by
  have h1 := k_eq_t1_add_sum_h hI
  rw [← sum_sdiff (P_subset I l), sum_h_sdiff_P hI l, t1] at h1
  linarith

lemma psi_eq (E : Finset ℕ) : psi k I E = (hSum k I E : ℤ) - oE E := by
  simp [psi, hSum, oE, sum_sub_distrib]

/-- **(La)** of `C35_the_podium_arithmetic.md` (Lemma 9.2): `φ(λ + 1) + ψ(P_l) = φ(Y_l)` and
`v_2(Y_l) = t_{l+1}`.  The file assumes `l ≤ s`; this holds for every `l`. -/
theorem La (hI : I ⊆ range k) (l : ℕ) :
    phi (lam k I + 1) + psi k I (P I l) = phi (Y k I l) ∧ v2 (Y k I l) = tAt k I l := by
  have hI' := lt_of_subset_range hI
  have hv : v2 (Y k I l) = tAt k I l :=
    v2_K_add_oE fun t ht => hI' t (mem_sdiff.1 ht).1
  refine ⟨?_, hv⟩
  have hv0 : v2 (lam k I + 1) = minOr k I := by rw [lam_add_one]; exact v2_K_add_oE hI'
  have hs := oE_sdiff (P_subset I l)
  have hs' : ((oE (I \ P I l) : ℕ) : ℤ) + oE (P I l) = oE I := by exact_mod_cast hs
  have hP := sum_h_P hI' l
  rw [phi, phi, hv0, hv, psi_eq, hSum, lam_add_one, Y]
  push_cast
  linarith

/-- **(Lb)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), first part: `clear N q ≤ N`. -/
theorem Lb_le (N q : ℕ) : clear N q ≤ N := Nat.mul_div_le N (2 ^ q)

/-- **(Lb)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), second part: for `1 ≤ y ≤ N` there is
`q` with `1 ≤ clear N q` and `φ(y) ≤ φ(clear N q)`.  (The file's hypothesis `N ≥ 1` follows from
`1 ≤ y ≤ N` and is omitted.) -/
theorem Lb (N y : ℕ) (hy : 1 ≤ y) (hyN : y ≤ N) :
    ∃ q, 1 ≤ clear N q ∧ phi y ≤ phi (clear N q) := by
  set q := v2 y with hq
  refine ⟨q, ?_⟩
  obtain ⟨c, hc⟩ : 2 ^ q ∣ y := pow_padicValNat_dvd
  have hpos : 0 < 2 ^ q := by positivity
  have hcN : c ≤ N / 2 ^ q := by
    rw [Nat.le_div_iff_mul_le hpos]; rw [hc] at hyN; linarith
  have hyc : y ≤ clear N q := by
    rw [clear, hc]; exact Nat.mul_le_mul_left _ hcN
  have hd1 : 1 ≤ N / 2 ^ q := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hc; omega
    · omega
  have hv : q ≤ v2 (clear N q) := by
    rw [v2, clear, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]
    exact Nat.le_add_right _ _
  refine ⟨le_trans hy hyc, ?_⟩
  unfold phi
  have : (y : ℤ) ≤ clear N q := by exact_mod_cast hyc
  have : (q : ℤ) ≤ v2 (clear N q) := by exact_mod_cast hv
  linarith

/-- A nonzero clearing of `o_{E ∪ {k}}` (with `E < k`) is `o_{E_{≥q} ∪ {k}}`, `q ≤ k`. -/
lemma clear_insert_top {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) (q : ℕ)
    (h : 1 ≤ clear (oE (insert k E)) q) :
    q ≤ k ∧ clear (oE (insert k E)) q = oE (insert k (E.filter (q ≤ ·))) := by
  rw [clear_oE] at h ⊢
  by_cases hq : q ≤ k
  · rw [filter_insert, if_pos hq]; exact ⟨hq, rfl⟩
  · exfalso
    have : (insert k E).filter (q ≤ ·) = ∅ := by
      apply filter_false_of_mem
      intro t ht
      rcases mem_insert.1 ht with rfl | ht
      · exact hq
      · have := hE t ht; omega
    rw [this, oE_empty] at h
    omega

lemma P_max (I : Finset ℕ) (a b : ℕ) : P I (max a b) = P I a ∪ P I b := by
  ext x; simp only [P, mem_filter, mem_union, lt_max_iff]; tauto

/-- **(Lc)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), first part: `Y_l` is a clearing of
`λ + 1` (namely at `q = t_{l+1}`).  The file assumes `l ≤ s`; this holds for every `l`. -/
theorem Lc_Y_eq_clear (hI : I ⊆ range k) (l : ℕ) :
    ∃ q, Y k I l = clear (lam k I + 1) q := by
  have hI' := lt_of_subset_range hI
  refine ⟨tAt k I l, ?_⟩
  rw [lam_add_one, oE_insert_top hI', clear_oE, filter_insert, if_pos (tAt_le hI' l),
    ← sdiff_P_eq_filter hI' l, Y_eq_oE hI']

/-- **(Lc)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), second part: every clearing `≥ 1` of
`λ + 1` is some `Y_l` with `l ≤ s`. -/
theorem Lc_clear_eq_Y (hI : I ⊆ range k) (q : ℕ) (h : 1 ≤ clear (lam k I + 1) q) :
    ∃ l ≤ I.card, clear (lam k I + 1) q = Y k I l := by
  have hI' := lt_of_subset_range hI
  rw [lam_add_one, oE_insert_top hI'] at h ⊢
  obtain ⟨-, he⟩ := clear_insert_top hI' q h
  refine ⟨(I.filter (· < q)).card, card_filter_le _ _, ?_⟩
  rw [he, Y_eq_oE hI', filter_ge_eq_sdiff_P]

/-- **(Lc)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), third part: `Y_l ≤ Y_1` for
`l ≥ 1`.  The file assumes `1 ≤ s` and `l ≤ s`; neither (nor `I ⊆ range k`) is needed. -/
theorem Lc_Y_le_Y_one (l : ℕ) (hl : 1 ≤ l) : Y k I l ≤ Y k I 1 := by
  unfold Y
  apply Nat.add_le_add_left
  exact sum_le_sum_of_subset (sdiff_subset_sdiff (le_refl I) (P_mono I hl))

/-- **(Lc)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), fourth part: if `1 ≤ s`, every
clearing `≥ 1` of `Y_1` is some `Y_l` with `1 ≤ l ≤ s`. -/
theorem Lc_clear_Y_one (hI : I ⊆ range k) (hs : 1 ≤ I.card) (q : ℕ)
    (h : 1 ≤ clear (Y k I 1) q) :
    ∃ l, 1 ≤ l ∧ l ≤ I.card ∧ clear (Y k I 1) q = Y k I l := by
  have hI' := lt_of_subset_range hI
  have hE : ∀ t ∈ I \ P I 1, t < k := fun t ht => hI' t (mem_sdiff.1 ht).1
  rw [Y_eq_oE hI'] at h ⊢
  obtain ⟨-, he⟩ := clear_insert_top hE q h
  set l0 := (I.filter (· < q)).card
  refine ⟨max l0 1, le_max_right _ _, max_le (card_filter_le _ _) hs, ?_⟩
  rw [he, Y_eq_oE hI']
  congr 2
  have h0 := filter_ge_eq_sdiff_P I q
  ext x
  have hx := congrArg (x ∈ ·) h0
  simp only [mem_filter, mem_sdiff, eq_iff_iff] at hx
  simp only [mem_filter, mem_sdiff, P_max, mem_union]
  tauto

/-- **(Ld)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), first part: for `1 ≤ y ≤ λ + 1`
there is `l ≤ s` with `φ(y) ≤ φ(Y_l)`. -/
theorem Ld (hI : I ⊆ range k) (y : ℕ) (hy : 1 ≤ y) (hyN : y ≤ lam k I + 1) :
    ∃ l ≤ I.card, phi y ≤ phi (Y k I l) := by
  obtain ⟨q, hq1, hq⟩ := Lb _ y hy hyN
  obtain ⟨l, hl, he⟩ := Lc_clear_eq_Y hI q hq1
  exact ⟨l, hl, he ▸ hq⟩

/-- **(Ld)** of `C35_the_podium_arithmetic.md` (Lemma 9.2), second part: if `1 ≤ s`, for
`1 ≤ y ≤ Y_1` there is `l` with `1 ≤ l ≤ s` and `φ(y) ≤ φ(Y_l)`. -/
theorem Ld_one (hI : I ⊆ range k) (hs : 1 ≤ I.card) (y : ℕ) (hy : 1 ≤ y)
    (hyN : y ≤ Y k I 1) :
    ∃ l, 1 ≤ l ∧ l ≤ I.card ∧ phi y ≤ phi (Y k I l) := by
  obtain ⟨q, hq1, hq⟩ := Lb _ y hy hyN
  obtain ⟨l, hl1, hl, he⟩ := Lc_clear_Y_one hI hs q hq1
  exact ⟨l, hl1, hl, he ▸ hq⟩

end Podium
