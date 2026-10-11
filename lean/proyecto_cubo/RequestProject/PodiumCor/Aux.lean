module

public import RequestProject.PodiumCor.Shift2

/-!
# `C36_the_podium_corollary.md`: auxiliary facts for Parts B, P, G

Elementary facts used in the proof of Corollary 1.6 (Parts B, P, G of
`C36_the_podium_corollary.md`): bounds on `φ(y) = y + v_2(y)` (C3 `Rulers.phi`), the behaviour of
`gmax`, and the shape of the family `λ` (`d = Families.ds lam`, `k = d.length`,
`I = Windows.Ids d`, `s = I.card`, `Y_l = Podium.Y k I l`, `t₁ = Podium.tAt k I 0`).
-/

@[expose] public section

namespace PodiumCor

open Finset Families

/-! ### `φ` -/

/-- `y ≤ φ(y)` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma phi_ge (y : ℕ) : (y : ℤ) ≤ Rulers.phi y := by
  unfold Rulers.phi; omega

/-- `v_2(y) < y` for `y ≥ 1` (auxiliary for Part P of `C36_the_podium_corollary.md`). -/
lemma v2_lt (y : ℕ) (hy : 1 ≤ y) : Rulers.v2 y < y := by
  unfold Rulers.v2
  have h1 : 2 ^ padicValNat 2 y ∣ y := pow_padicValNat_dvd
  have h2 := Nat.le_of_dvd hy h1
  have h3 := Nat.lt_two_pow_self (n := padicValNat 2 y)
  omega

/-- `φ(y) ≤ 2y − 1` for `y ≥ 1` (auxiliary for Part P of `C36_the_podium_corollary.md`). -/
lemma phi_le (y : ℕ) (hy : 1 ≤ y) : Rulers.phi y ≤ 2 * y - 1 := by
  have := v2_lt y hy
  unfold Rulers.phi; omega

/-- `φ(y) = y` for odd `y` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma phi_odd (y : ℕ) (h : y % 2 = 1) : Rulers.phi y = y := by
  unfold Rulers.phi Rulers.v2
  rw [padicValNat.eq_zero_of_not_dvd (by omega)]
  simp

/-- `φ(y) ≥ y + 1` for even `y ≥ 1` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma phi_even (y : ℕ) (hy : 1 ≤ y) (h : y % 2 = 0) : (y : ℤ) + 1 ≤ Rulers.phi y := by
  unfold Rulers.phi Rulers.v2
  have := one_le_padicValNat_of_dvd (p := 2) (n := y) (by omega) (by omega)
  omega

/-- `φ(y) ≥ y + 2` for `y ≥ 1` divisible by `4` (auxiliary for Part P of
`C36_the_podium_corollary.md`). -/
lemma phi_four (y : ℕ) (hy : 1 ≤ y) (h : y % 4 = 0) : (y : ℤ) + 2 ≤ Rulers.phi y := by
  unfold Rulers.phi Rulers.v2
  have := (padicValNat_dvd_iff_le (p := 2) (a := y) (n := 2) (by omega)).1 (by omega)
  omega

/-- `v_2(y) = 1` for `y ≡ 2 (mod 4)` (auxiliary for Part P of `C36_the_podium_corollary.md`). -/
lemma v2_two_mod_four (y : ℕ) (h : y % 4 = 2) : Rulers.v2 y = 1 := by
  unfold Rulers.v2
  have h1 := (padicValNat_dvd_iff_le (p := 2) (a := y) (n := 1) (by omega)).1 (by omega)
  have h2 : ¬ 2 ≤ padicValNat 2 y := fun h2 => by
    have := (padicValNat_dvd_iff_le (p := 2) (a := y) (n := 2) (by omega)).2 h2
    omega
  omega

/-! ### `gmax` -/

/-- `φ(y) ≤ gmax N` for `1 ≤ y < N` (from (g0); auxiliary for Part B of
`C36_the_podium_corollary.md`). -/
lemma le_gmax (N y : ℕ) (h1 : 1 ≤ y) (h2 : y < N) : Rulers.phi y ≤ gmax N :=
  (g0 N (by omega)).2 y h1 h2

/-- `gmax N ≤ b` as soon as `φ(y) ≤ b` for every `1 ≤ y < N` (from (g0); auxiliary for Part B of
`C36_the_podium_corollary.md`). -/
lemma gmax_le_of (N : ℕ) (hN : 2 ≤ N) (b : ℤ) (h : ∀ y, 1 ≤ y → y < N → Rulers.phi y ≤ b) :
    gmax N ≤ b := by
  obtain ⟨x, h1, h2, he⟩ := (g0 N hN).1
  rw [he]; exact h x h1 h2

/-- `gmax (N + 1) = max (gmax N) (φ N)` for `N ≥ 2` (auxiliary for Part G of
`C36_the_podium_corollary.md`). -/
lemma gmax_succ (N : ℕ) (hN : 2 ≤ N) : gmax (N + 1) = max (gmax N) (Rulers.phi N) := by
  refine le_antisymm (gmax_le_of _ (by omega) _ fun y h1 h2 => ?_) (max_le ?_ ?_)
  · rcases Nat.lt_or_ge y N with h | h
    · exact (le_gmax N y h1 h).trans (le_max_left _ _)
    · rw [show y = N by omega]; exact le_max_right _ _
  · exact gmax_le_of _ hN _ fun y h1 h2 => le_gmax _ y h1 (by omega)
  · exact le_gmax _ N (by omega) (by omega)

/-- `N − 1 ≤ gmax N` for `N ≥ 2` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma gmax_ge (N : ℕ) (hN : 2 ≤ N) : (N : ℤ) - 1 ≤ gmax N := by
  have := le_gmax N (N - 1) (by omega) (by omega)
  have := phi_ge (N - 1)
  omega

/-- `n + 1 < 2 ^ (n − 1)` for `n ≥ 4` (auxiliary for (B0) of `C36_the_podium_corollary.md`). -/
lemma lt_two_pow_pred (n : ℕ) (hn : 4 ≤ n) : n + 1 < 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    omega

/-! ### Sums of powers of two -/

/-- `o_E ≥ 1` for a nonempty `E` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma oE_pos {E : Finset ℕ} (h : E.Nonempty) : 1 ≤ Rulers.oE E := by
  obtain ⟨t, ht⟩ := h
  have := single_le_sum (f := fun t => 2 ^ t) (fun _ _ => Nat.zero_le _) ht
  dsimp only at this
  have := Nat.one_le_two_pow (n := t)
  unfold Rulers.oE; omega

/-- `o_E ≥ 3` if `E` has at least two elements (auxiliary for Part B of
`C36_the_podium_corollary.md`). -/
lemma oE_ge_three {E : Finset ℕ} (h : 2 ≤ E.card) : 3 ≤ Rulers.oE E := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < E.card)
  have hsub : ({a, b} : Finset ℕ) ⊆ E := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have h1 := sum_le_sum_of_subset (f := fun t => 2 ^ t) hsub
  dsimp only at h1
  rw [sum_pair hab] at h1
  have ha1 := Nat.one_le_two_pow (n := a)
  have hb1 := Nat.one_le_two_pow (n := b)
  have : 2 ≤ 2 ^ a ∨ 2 ≤ 2 ^ b := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · right
      exact (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ b)).trans_eq' (by norm_num)
    · left
      exact (Nat.pow_le_pow_right (by norm_num) hpos).trans_eq' (by norm_num)
  unfold Rulers.oE; omega

/-! ### The shape of a family -/

/-- `Y_l + o_{P_l} = λ + 1` for the family `λ` (C35 `Y_add_oE_P` and C33 `S1_lam`; auxiliary for
Part B of `C36_the_podium_corollary.md`). -/
lemma Y_add (lam l : ℕ) :
    Podium.Y (ds lam).length (Windows.Ids (ds lam)) l + Rulers.oE (Podium.P (Windows.Ids (ds lam)) l)
      = lam + 1 := by
  have := Podium.Y_add_oE_P (ds lam).length (Windows.Ids (ds lam)) l
  rwa [MainTheorem.S1_lam] at this

/-- `Y_l ≥ 1` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma Y_pos (k : ℕ) (I : Finset ℕ) (l : ℕ) : 1 ≤ Podium.Y k I l := by
  unfold Podium.Y; have := Nat.one_le_two_pow (n := k); omega

/-- `Y_0 = λ + 1` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma Y_zero (lam : ℕ) : Podium.Y (ds lam).length (Windows.Ids (ds lam)) 0 = lam + 1 := by
  have := Y_add lam 0
  rw [Podium.P_zero] at this
  simpa [Rulers.oE] using this

/-- `Y_l ≤ λ + 1` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma Y_le_succ (lam l : ℕ) : Podium.Y (ds lam).length (Windows.Ids (ds lam)) l ≤ lam + 1 := by
  have := Y_add lam l; omega

/-- `Y_l ≤ λ` for `1 ≤ l ≤ s` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma Y_le_self (lam l : ℕ) (hl1 : 1 ≤ l) (hl : l ≤ (Windows.Ids (ds lam)).card) :
    Podium.Y (ds lam).length (Windows.Ids (ds lam)) l ≤ lam := by
  have h := Y_add lam l
  have hc := Podium.card_P hl
  have := oE_pos (E := Podium.P (Windows.Ids (ds lam)) l) (card_pos.1 (by omega))
  omega

/-- `Y_l + 2 ≤ λ` for `2 ≤ l ≤ s` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma Y_le_sub_two (lam l : ℕ) (hl2 : 2 ≤ l) (hl : l ≤ (Windows.Ids (ds lam)).card) :
    Podium.Y (ds lam).length (Windows.Ids (ds lam)) l + 2 ≤ lam := by
  have h := Y_add lam l
  have hc := Podium.card_P hl
  have := oE_ge_three (E := Podium.P (Windows.Ids (ds lam)) l) (by omega)
  omega

/-- `P_1 = {t}` for the least element `t` of `I` (auxiliary for Part B of
`C36_the_podium_corollary.md`). -/
lemma P_one_eq (I : Finset ℕ) (t : ℕ) (ht : t ∈ I) (hmin : ∀ u ∈ I, t ≤ u) :
    Podium.P I 1 = {t} := by
  ext x
  simp only [Podium.P, mem_filter, mem_singleton, Nat.lt_one_iff, card_eq_zero,
    filter_eq_empty_iff, not_lt]
  constructor
  · rintro ⟨hx, hlt⟩
    have h1 := hmin x hx
    have h2 := hlt ht
    omega
  · rintro rfl
    exact ⟨ht, hmin⟩

/-- `Y_1 + 2^{t₁} = λ + 1` and `t₁ = t` for the least element `t` of `I` (auxiliary for Part B of
`C36_the_podium_corollary.md`). -/
lemma Y_one_of_min (lam t : ℕ) (ht : t ∈ Windows.Ids (ds lam))
    (hmin : ∀ u ∈ Windows.Ids (ds lam), t ≤ u) :
    Podium.Y (ds lam).length (Windows.Ids (ds lam)) 1 + 2 ^ t = lam + 1 ∧
      Podium.tAt (ds lam).length (Windows.Ids (ds lam)) 0 = t := by
  refine ⟨?_, ?_⟩
  · have := Y_add lam 1
    rwa [P_one_eq _ t ht hmin, Rulers.oE, sum_singleton] at this
  · unfold Podium.tAt
    rw [Podium.P_zero, sdiff_empty]
    exact Rulers.minOr_eq_of_mem ht hmin

/-- `0 ∈ I` for even `λ ≥ 2` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma zero_mem_even (l : ℕ) : 0 ∈ Windows.Ids (ds (2 * l + 2)) := by
  rw [ds_even, Windows.Ids_cons]; simp

/-- The elements of `I` for odd `λ = 2l + 1` are the `u + 1`, `u ∈ I(l)` (auxiliary for Part B of
`C36_the_podium_corollary.md`). -/
lemma mem_Ids_odd (l t : ℕ) :
    t ∈ Windows.Ids (ds (2 * l + 1)) ↔ ∃ u ∈ Windows.Ids (ds l), u + 1 = t := by
  rw [ds_odd, Windows.Ids_cons]; simp

/-- `λ ≥ 1` has `k ≥ 1` (C33 `S2_length`), so `2^k` is even (auxiliary). -/
lemma two_pow_length_even (lam : ℕ) (hlam : 1 ≤ lam) : 2 ^ (ds lam).length % 2 = 0 := by
  obtain ⟨k', hk'⟩ : ∃ k', (ds lam).length = k' + 1 :=
    ⟨(ds lam).length - 1, by have := MainTheorem.S2_length lam hlam; omega⟩
  rw [hk', pow_succ]; omega

end PodiumCor
