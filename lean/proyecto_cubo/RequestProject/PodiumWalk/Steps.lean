module

public import RequestProject.PodiumWalk.Walk

/-!
# Bookkeeping of the walk at shifts `1` and `0` (`C35b_the_podium_walk.md`, sketches of Parts T
and Z)

Auxiliary file of `C35b_the_podium_walk.md`.  Nothing listed in the Setting is redefined.  We use
one auxiliary abbreviation:

* `tailVal k I l := −ψ(I ∖ P_l)` (with C35 `Podium.psi` and `Podium.P`), the value
  `k + K − Σ_{j > l} ψ_{t_j}` of the sketches minus `k + K`; `phi_Y` shows
  `k + K + tailVal k I l = φ(Y_l)` (from C35 `La`).

For `I ≠ ∅`, `c = max I`, `I' = I ∖ {c}`, `ψ_c = h_c − 2^c`:
`tailVal k I l = tailVal c I' l − ψ_c` for `l ≤ |I'|` and `tailVal k I |I| = 0`.  The walk increment
is `d ≡ −ψ_c` when `ℓ = 0` (`dWalk_zero`) and `d(p) = 2^c` if `p = 0`, `−ψ_c` otherwise, when
`ℓ = 2^k − 1` (`dWalk_top`).
-/

@[expose] public section

namespace PodiumWalk

open Finset AntitonicFit TheoremF Potential

/-- Auxiliary for Parts T and Z of `C35b_the_podium_walk.md`: `tailVal k I l := −ψ(I ∖ P_l)`, so that
`k + K + tailVal k I l = φ(Y_l)` (`phi_Y`). -/
def tailVal (k : ℕ) (I : Finset ℕ) (l : ℕ) : ℤ := -Podium.psi k I (I \ Podium.P I l)

variable {I : Finset ℕ} {k : ℕ} {c : ℕ}

lemma filter_lt_erase (hcmax : ∀ t ∈ I, t ≤ c) {t : ℕ} (htc : t ∈ I) (hne : t ≠ c) :
    I.filter (· < t) = (I.erase c).filter (· < t) := by
  have := lt_of_le_of_ne (hcmax t htc) hne
  ext u
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hu, hut⟩; exact ⟨⟨by omega, hu⟩, hut⟩
  · rintro ⟨⟨-, hu⟩, hut⟩; exact ⟨hu, hut⟩

lemma filter_lt_max (hcmax : ∀ t ∈ I, t ≤ c) : I.filter (· < c) = I.erase c := by
  ext u
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hu, huc⟩; exact ⟨by omega, hu⟩
  · rintro ⟨huc, hu⟩; exact ⟨hu, lt_of_le_of_ne (hcmax u hu) huc⟩

/-- `P_l` of `I` and of `I' = I ∖ {max I}` agree for `l ≤ |I'|`. -/
lemma P_erase (hcmax : ∀ t ∈ I, t ≤ c) {l : ℕ} (hl : l ≤ #(I.erase c)) :
    Podium.P I l = Podium.P (I.erase c) l := by
  ext t
  simp only [Podium.P, mem_filter, mem_erase]
  constructor
  · rintro ⟨ht, hr⟩
    have htc : t ≠ c := by
      rintro rfl
      rw [filter_lt_max hcmax] at hr
      omega
    exact ⟨⟨htc, ht⟩, by rwa [← filter_lt_erase hcmax ht htc]⟩
  · rintro ⟨⟨htc, ht⟩, hr⟩
    exact ⟨ht, by rwa [filter_lt_erase hcmax ht htc]⟩

lemma sdiff_P_erase (hcI : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) {l : ℕ} (hl : l ≤ #(I.erase c)) :
    I \ Podium.P I l = insert c ((I.erase c) \ Podium.P (I.erase c) l) := by
  rw [P_erase hcmax hl]
  have hc' : c ∉ Podium.P (I.erase c) l := fun h => by
    have := Podium.P_subset _ _ h; simp at this
  ext t
  simp only [mem_sdiff, mem_insert, mem_erase]
  constructor
  · rintro ⟨ht, hP⟩
    by_cases htc : t = c
    · exact Or.inl htc
    · exact Or.inr ⟨⟨htc, ht⟩, hP⟩
  · rintro (rfl | ⟨⟨-, ht⟩, hP⟩)
    · exact ⟨hcI, hc'⟩
    · exact ⟨ht, hP⟩

/-- `tailVal k I l = tailVal c I' l − ψ_c` for `l ≤ |I'|`. -/
lemma tailVal_step (hI : ∀ t ∈ I, t < k) (hcI : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) {l : ℕ}
    (hl : l ≤ #(I.erase c)) :
    tailVal k I l = tailVal c (I.erase c) l - ((Rulers.h k I c : ℤ) - 2 ^ c) := by
  have hnot : c ∉ (I.erase c) \ Podium.P (I.erase c) l := by simp
  unfold tailVal
  rw [sdiff_P_erase hcI hcmax hl, Podium.psi, sum_insert hnot]
  have : ∑ t ∈ (I.erase c) \ Podium.P (I.erase c) l, ((Rulers.h k I t : ℤ) - 2 ^ t) =
      Podium.psi c (I.erase c) ((I.erase c) \ Podium.P (I.erase c) l) := by
    unfold Podium.psi
    refine sum_congr rfl fun t ht => ?_
    rw [Houses.h_erase hI hcI hcmax (mem_sdiff.1 ht).1]
  rw [this]
  ring

lemma tailVal_top (k : ℕ) (I : Finset ℕ) : tailVal k I #I = 0 := by
  simp [tailVal, Podium.P_card_self, Podium.psi]

lemma tailVal_empty (k l : ℕ) : tailVal k ∅ l = 0 := by
  simp [tailVal, Podium.psi]

/-- `k + K + tailVal k I l = φ(Y_l)` (C35 `La`). -/
lemma phi_Y (hI : I ⊆ range k) (l : ℕ) :
    (k : ℤ) + 2 ^ k + tailVal k I l = Rulers.phi (Podium.Y k I l) := by
  have h1 := (Podium.La hI l).1
  have h2 := (Podium.La hI #I).1
  rw [Podium.P_card_self] at h2
  have hY : Podium.Y k I #I = 2 ^ k := by
    simp [Podium.Y, Podium.P_card_self, Rulers.oE]
  have hphiK : Rulers.phi (2 ^ k) = 2 ^ k + k := by
    simp [Rulers.phi, Rulers.v2, padicValNat.prime_pow]
  rw [hY, hphiK] at h2
  have h3 := Podium.psi_add_psi_sdiff (k := k) (I := I) (Podium.P_subset I l)
  unfold tailVal
  linarith

/-- The empty house: `ŷ(0) = 0` (Lemma 0f of C7 and (A2) of C1). -/
lemma yhat_empty {ℓ : ℕ} {α : ℤ} (h0 : #I = 0) : yhat I k ℓ α 0 = 0 := by
  have hN : 2 ^ #I = 1 := by rw [h0]; rfl
  have := A2 (lemma_0f_antisymm I k ℓ α) 0 (by rw [hN]; norm_num)
  rw [hN] at this
  unfold yhat
  rw [hN]
  simp only [Nat.sub_self] at this
  omega

/-- At shift `1` (`ℓ = 0`) the walk increment is `−ψ_c` (sketch of Part T of
`C35b_the_podium_walk.md`). -/
lemma dWalk_zero (hcmax : ∀ t ∈ I, t ≤ c) (p : ℕ) :
    dWalk I k 0 1 c p = -((Rulers.h k I c : ℤ) - 2 ^ c) := by
  have hJ : ∀ E ⊆ I.erase c, Houses.JH c 0 E = 0 := by
    intro E hE
    have := Houses.oE_lt_erase hcmax hE
    simp only [Houses.JH, zero_add]
    rw [if_neg (by omega)]
  simp [dWalk, Houses.d1, Houses.tau, Houses.typ, Houses.bit, hJ _ (lemma_0a _ _),
    hJ _ sdiff_subset]

lemma two_pow_sub_one_eq {k c : ℕ} (hck : c < k) :
    2 ^ k - 1 = (2 ^ c - 1) + 2 ^ c * (2 ^ (k - c) - 1) := by
  have h1 : 2 ^ k = 2 ^ c * 2 ^ (k - c) := by rw [← pow_add]; congr 1; omega
  have h2 : 1 ≤ 2 ^ (k - c) := Nat.one_le_two_pow
  have h3 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  rw [h1, Nat.mul_sub, mul_one]
  have h4 : 2 ^ c ≤ 2 ^ c * 2 ^ (k - c) := Nat.le_mul_of_pos_right _ (by positivity)
  generalize 2 ^ c * 2 ^ (k - c) = X at *
  omega

lemma two_pow_sub_one_mod {k c : ℕ} (hck : c < k) : (2 ^ k - 1) % 2 ^ c = 2 ^ c - 1 := by
  rw [two_pow_sub_one_eq hck, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have : 1 ≤ 2 ^ c := Nat.one_le_two_pow; omega)

lemma two_pow_sub_one_div {k c : ℕ} (hck : c < k) : (2 ^ k - 1) / 2 ^ c = 2 ^ (k - c) - 1 := by
  rw [two_pow_sub_one_eq hck, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (by have : 1 ≤ 2 ^ c := Nat.one_le_two_pow; omega), zero_add]

/-- At shift `0` (`ℓ = 2^k − 1`) the walk increment is `2^c` at `p = 0` and `−ψ_c` at `0 < p < M`
(every window has type `1` and is saturated; sketch of Part Z of `C35b_the_podium_walk.md`). -/
lemma dWalk_top (hI : ∀ t ∈ I, t < k) (hcI : c ∈ I) (hcmax : ∀ t ∈ I, t ≤ c) {p : ℕ}
    (hp : p < 2 ^ #(I.erase c)) :
    dWalk I k (2 ^ k - 1) 1 c p =
      if p = 0 then 2 ^ c else -((Rulers.h k I c : ℤ) - 2 ^ c) := by
  have hck := hI c hcI
  have hℓ : 2 ^ k - 1 < 2 ^ k := by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
  have htk := Houses.typ_kap_max hI hℓ hcI hcmax
  rw [two_pow_sub_one_div hck, Nat.sub_add_cancel Nat.one_le_two_pow, Rulers.v2,
    padicValNat.prime_pow] at htk
  have hh := Houses.h_max hI hcI hcmax
  have htyp : Houses.typ (2 ^ k - 1) c = 1 := by
    unfold Houses.typ Houses.bit
    rw [two_pow_sub_one_div hck]
    have : 2 ^ (k - c) = 2 * 2 ^ (k - c - 1) := by rw [← pow_succ']; congr 1; omega
    have : 0 < 2 ^ (k - c - 1) := by positivity
    omega
  have hJ : Houses.JH c ((2 ^ k - 1) % 2 ^ c) (dancer (I.erase c) p) = if p = 0 then 0 else 1 := by
    rw [two_pow_sub_one_mod hck]
    unfold Houses.JH
    have h1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    by_cases hp0 : p = 0
    · subst hp0
      rw [dancer_zero, Rulers.oE_empty, if_pos rfl, if_neg (by omega)]
    · have := lemma_0b (I := I.erase c) (show 0 < p by omega) hp
      rw [dancer_zero, Rulers.oE_empty] at this
      rw [if_neg hp0, if_pos (by omega)]
  have htk' : ((if Houses.typ (2 ^ k - 1) c = 1 then Houses.kap I k (2 ^ k - 1) c else 0 : ℕ) : ℤ)
      = (k - c : ℕ) := by rw [htk]
  rw [if_pos htyp] at htk'
  simp only [dWalk, Houses.d1, Houses.tau, htyp, if_true, hJ, one_ne_zero, if_false,
    zero_mul, add_zero, htk', hh]
  split_ifs <;> push_cast [hck.le] <;> ring

/-- The minimum of `I` is the minimum of `I' = I ∖ {max I}` when `I' ≠ ∅`. -/
lemma minOr_erase (hcmax : ∀ t ∈ I, t ≤ c) (hne : (I.erase c).Nonempty) :
    Rulers.minOr k I = Rulers.minOr c (I.erase c) := by
  have hm := Rulers.minOr_mem (k := c) hne
  apply Rulers.minOr_eq_of_mem (mem_of_mem_erase hm)
  intro x hx
  by_cases hxc : x = c
  · subst hxc
    exact (hcmax _ (mem_of_mem_erase hm)).trans le_rfl
  · exact Rulers.minOr_le (mem_erase.2 ⟨hxc, hx⟩)

end PodiumWalk
