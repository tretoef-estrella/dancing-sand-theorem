module

public import RequestProject.Rulers.All

/-!
# The podium arithmetic: definitions and Part P (`C35_the_podium_arithmetic.md`, *Setting* and
*Part P*)

Nothing from C3 is redefined: `Rulers.s2`, `v2`, `kappa`, `phi`, `oE`, `minOr`, `next`, `h`,
`t1`, `hSum`, `lam`, `xi`, `clock` are used directly.

Encodings (namespace `Podium`).  The family is `k : ℕ` and `I : Finset ℕ` with
`hI : I ⊆ Finset.range k`; `K = 2 ^ k` is written out and `s = I.card`.

* `psi k I E : ℤ` is `ψ(E) := Σ_{t ∈ E} (h_t − 2^t)`, with `h_t = Rulers.h k I t`.
* `P I l` is `P_l = {t_1, …, t_l}`, the `l` smallest elements of `I`, encoded as the elements
  `t ∈ I` with fewer than `l` elements of `I` below `t`:
  `I.filter (fun t => (I.filter (· < t)).card < l)` (for `l ≥ s` this is all of `I`).
* `tAt k I l` is `t_{l+1} := min (I ∖ P_l)`, with `min ∅ := k` (so `t_{s+1} = k`), i.e.
  `Rulers.minOr k (I \ P I l)`.
* `Y k I l` is `Y_l := K + o_{I ∖ P_l}` (`= λ + 1 − o_{P_l}`, see `P0`).
* `clear N q` is `N` with its binary digits below `q` cleared, `2 ^ q * (N / 2 ^ q)`.
-/

@[expose] public section

namespace Podium

open Finset Rulers

/-- `ψ(E) := Σ_{t ∈ E} (h_t − 2^t)` (*Setting* of `C35_the_podium_arithmetic.md`). -/
def psi (k : ℕ) (I E : Finset ℕ) : ℤ := ∑ t ∈ E, ((Rulers.h k I t : ℤ) - 2 ^ t)

/-- `P_l`, the `l` smallest elements of `I` (*Setting* of `C35_the_podium_arithmetic.md`):
the `t ∈ I` with fewer than `l` elements of `I` below `t`. -/
def P (I : Finset ℕ) (l : ℕ) : Finset ℕ := I.filter (fun t => (I.filter (· < t)).card < l)

/-- `t_{l+1} := min (I ∖ P_l)`, with `t_{s+1} = k` (*Setting* of
`C35_the_podium_arithmetic.md`). -/
def tAt (k : ℕ) (I : Finset ℕ) (l : ℕ) : ℕ := Rulers.minOr k (I \ P I l)

/-- `Y_l := K + o_{I ∖ P_l}` (*Setting* of `C35_the_podium_arithmetic.md`). -/
def Y (k : ℕ) (I : Finset ℕ) (l : ℕ) : ℕ := 2 ^ k + Rulers.oE (I \ P I l)

/-- `N` with its bits below `q` cleared, `2^q ⌊N / 2^q⌋` (*Setting* of
`C35_the_podium_arithmetic.md`). -/
def clear (N q : ℕ) : ℕ := 2 ^ q * (N / 2 ^ q)

/-! ### Auxiliary facts on binary expansions -/

lemma lam_add_one (k : ℕ) (I : Finset ℕ) : lam k I + 1 = 2 ^ k + oE I := by
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  unfold lam; omega

lemma oE_insert_top {k : ℕ} {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) :
    2 ^ k + oE E = oE (insert k E) := by
  have : k ∉ E := fun h => lt_irrefl _ (hE k h)
  simp only [oE]; rw [sum_insert this]

lemma two_pow_dvd_oE {S : Finset ℕ} {q : ℕ} (hS : ∀ t ∈ S, q ≤ t) : 2 ^ q ∣ oE S :=
  dvd_sum fun t ht => pow_dvd_pow 2 (hS t ht)

/-- `v_2(o_S) = min S` for `S ≠ ∅`. -/
lemma v2_oE {S : Finset ℕ} (hS : S.Nonempty) : v2 (oE S) = S.min' hS := by
  set m := S.min' hS
  have hm : m ∈ S := min'_mem _ _
  have hd : 2 ^ (m + 1) ∣ oE (S.erase m) := two_pow_dvd_oE fun t ht => by
    have h1 := min'_le S t (mem_of_mem_erase ht)
    have h2 := ne_of_mem_erase ht
    omega
  obtain ⟨c, hc⟩ := hd
  have h1 : oE S = 2 ^ m * (2 * c + 1) := by
    rw [oE, ← add_sum_erase _ _ hm, ← oE, hc, pow_succ]; ring
  rw [v2, h1, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]
  rfl

/-- `v_2(K + o_E) = min E` (with `min ∅ := k`) for `E ⊆ {0, …, k − 1}`. -/
lemma v2_K_add_oE {k : ℕ} {E : Finset ℕ} (hE : ∀ t ∈ E, t < k) :
    v2 (2 ^ k + oE E) = minOr k E := by
  rw [oE_insert_top hE, v2_oE (insert_nonempty _ _)]
  by_cases hne : E.Nonempty
  · rw [minOr, dif_pos hne]
    apply le_antisymm
    · exact min'_le _ _ (mem_insert_of_mem (min'_mem _ _))
    · apply le_min'
      intro y hy
      rcases mem_insert.1 hy with rfl | hy
      · exact (hE _ (min'_mem _ _)).le
      · exact min'_le _ _ hy
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [minOr_empty]

/-- Clearing the bits below `q` of `o_S` keeps the elements `≥ q` of `S`. -/
lemma clear_oE (S : Finset ℕ) (q : ℕ) : clear (oE S) q = oE (S.filter (q ≤ ·)) := by
  have hsplit : oE S = oE (S.filter (fun t => ¬ q ≤ t)) + oE (S.filter (q ≤ ·)) := by
    simp only [oE]; rw [add_comm, sum_filter_add_sum_filter_not]
  have hlt : oE (S.filter (fun t => ¬ q ≤ t)) < 2 ^ q :=
    oE_lt _ _ fun t ht => by simp at ht; omega
  obtain ⟨c, hc⟩ : 2 ^ q ∣ oE (S.filter (q ≤ ·)) :=
    two_pow_dvd_oE fun t ht => (mem_filter.1 ht).2
  rw [clear, hsplit, hc, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt,
    zero_add]

/-! ### The prefixes -/

lemma rank_mono (I : Finset ℕ) {t u : ℕ} (htu : t ≤ u) :
    (I.filter (· < t)).card ≤ (I.filter (· < u)).card :=
  card_le_card fun x hx => by rw [mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩

lemma rank_strict (I : Finset ℕ) {t u : ℕ} (ht : t ∈ I) (htu : t < u) :
    (I.filter (· < t)).card < (I.filter (· < u)).card := by
  apply card_lt_card
  refine ⟨fun x hx => by rw [mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩, fun h => ?_⟩
  have := h (mem_filter.2 ⟨ht, htu⟩)
  simp at this

lemma rank_lt_card (I : Finset ℕ) {t : ℕ} (ht : t ∈ I) : (I.filter (· < t)).card < I.card :=
  card_lt_card (filter_ssubset.2 ⟨t, ht, lt_irrefl t⟩)

lemma P_subset (I : Finset ℕ) (l : ℕ) : P I l ⊆ I := filter_subset _ _

lemma P_mono (I : Finset ℕ) {a b : ℕ} (hab : a ≤ b) : P I a ⊆ P I b :=
  fun x hx => by simp only [P, mem_filter] at hx ⊢; exact ⟨hx.1, by omega⟩

/-- Every element of `P_l` is below every element of `I ∖ P_l`. -/
lemma P_lt (I : Finset ℕ) (l : ℕ) {t u : ℕ} (ht : t ∈ P I l) (hu : u ∈ I \ P I l) : t < u := by
  by_contra hle
  push_neg at hle
  simp only [P, mem_sdiff, mem_filter, not_and, not_lt] at ht hu
  have := rank_mono I hle
  have := hu.2 hu.1
  have := ht.2
  omega

lemma P_zero (I : Finset ℕ) : P I 0 = ∅ := by simp [P]

lemma P_card_self (I : Finset ℕ) : P I I.card = I :=
  filter_true_of_mem fun _ ht => rank_lt_card I ht

lemma P_of_le_card {I : Finset ℕ} {l : ℕ} (hl : I.card ≤ l) : P I l = I :=
  filter_true_of_mem fun _ ht => lt_of_lt_of_le (rank_lt_card I ht) hl

lemma card_P {I : Finset ℕ} {l : ℕ} (hl : l ≤ I.card) : (P I l).card = l := by
  set r : ℕ → ℕ := fun t => (I.filter (· < t)).card
  have hinj : Set.InjOn r I := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hxy (rank_strict I hx h).ne
    · exact absurd hxy (rank_strict I hy h).ne'
  have himg : I.image r = range I.card := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hx
      exact mem_range.2 (rank_lt_card I ht)
    · rw [card_range, card_image_of_injOn hinj]
  have h1 : (P I l).card = ((I.image r).filter (· < l)).card := by
    rw [filter_image, card_image_of_injOn (hinj.mono (coe_subset.2 (filter_subset _ _)))]
    rfl
  rw [h1, himg]
  have : (range I.card).filter (· < l) = range l := by
    ext x; simp; omega
  rw [this, card_range]

/-- Every element of `P_l` is below `t_{l+1}`. -/
lemma P_lt_tAt {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (l : ℕ) {t : ℕ}
    (ht : t ∈ P I l) : t < tAt k I l := by
  unfold tAt
  by_cases hne : (I \ P I l).Nonempty
  · exact P_lt I l ht (minOr_mem hne)
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, minOr_empty]
    exact hI t (P_subset I l ht)

/-- `I ∖ P_l = {t ∈ I : t ≥ t_{l+1}}`. -/
lemma sdiff_P_eq_filter {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (l : ℕ) :
    I \ P I l = I.filter (tAt k I l ≤ ·) := by
  ext x
  simp only [mem_sdiff, mem_filter]
  constructor
  · rintro ⟨hx, hxP⟩
    exact ⟨hx, minOr_le (mem_sdiff.2 ⟨hx, hxP⟩)⟩
  · rintro ⟨hx, hle⟩
    refine ⟨hx, fun hxP => ?_⟩
    have := P_lt_tAt hI l hxP
    omega

lemma tAt_le {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (l : ℕ) : tAt k I l ≤ k := by
  unfold tAt
  by_cases hne : (I \ P I l).Nonempty
  · exact (hI _ (mem_sdiff.1 (minOr_mem hne)).1).le
  · rw [not_nonempty_iff_eq_empty] at hne; rw [hne, minOr_empty]

/-- `Y_l = o_{(I ∖ P_l) ∪ {k}}`. -/
lemma Y_eq_oE {k : ℕ} {I : Finset ℕ} (hI : ∀ t ∈ I, t < k) (l : ℕ) :
    Y k I l = oE (insert k (I \ P I l)) :=
  oE_insert_top fun t ht => hI t (mem_sdiff.1 ht).1

/-- The prefix of the elements of `I` below `q` is `P_l` for `l` its cardinality. -/
lemma P_card_filter_lt (I : Finset ℕ) (q : ℕ) :
    P I (I.filter (· < q)).card = I.filter (· < q) := by
  ext t
  simp only [P, mem_filter]
  constructor
  · rintro ⟨ht, hr⟩
    refine ⟨ht, ?_⟩
    by_contra hle
    push_neg at hle
    have := rank_mono I hle
    omega
  · rintro ⟨ht, htq⟩
    exact ⟨ht, rank_strict I ht htq⟩

lemma filter_ge_eq_sdiff_P (I : Finset ℕ) (q : ℕ) :
    I.filter (q ≤ ·) = I \ P I (I.filter (· < q)).card := by
  rw [P_card_filter_lt]
  ext t; simp only [mem_filter, mem_sdiff, not_and, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2 h1⟩

/-- `Y_l + o_{P_l} = λ + 1`. -/
lemma Y_add_oE_P (k : ℕ) (I : Finset ℕ) (l : ℕ) : Y k I l + oE (P I l) = lam k I + 1 := by
  rw [lam_add_one, Y, add_assoc, oE_sdiff (P_subset I l)]

/-! ### Part P -/

/-- **(P0)** of `C35_the_podium_arithmetic.md`: for `l ≤ s`, `P_l ⊆ I`, `|P_l| = l`, every
element of `P_l` is smaller than every element of `I ∖ P_l`, `P_0 = ∅`, `P_s = I`, and
`Y_l + o_{P_l} = λ + 1`.  (The hypothesis `l ≤ s` is only used for `|P_l| = l`; the hypothesis
`I ⊆ range k` is not needed.) -/
theorem P0 (k : ℕ) (I : Finset ℕ) (l : ℕ) (hl : l ≤ I.card) :
    P I l ⊆ I ∧ (P I l).card = l ∧ (∀ t ∈ P I l, ∀ u ∈ I \ P I l, t < u) ∧
      P I 0 = ∅ ∧ P I I.card = I ∧ Y k I l + oE (P I l) = lam k I + 1 := by
  exact ⟨P_subset I l, card_P hl, fun t ht u hu => P_lt I l ht hu, P_zero I, P_card_self I,
    Y_add_oE_P k I l⟩

end Podium
