module

public import RequestProject.PodiumWalk.Shift1

/-!
# Part Z of `C35b_the_podium_walk.md` (Proposition 9.4, shift `0`)

Encodings as in `Head.lean` and `Shift1.lean`; `t₁ = Podium.tAt k I 0` (`= Rulers.minOr k I`), and
the pooled clocks at shift `0` are C16 `FamilyGroup.yPool0 ds q` (`q < N − 1`, the dancer of rank
`q + 1`).  By C16 `R2` and C9 `lemma_7_9_I3`, `ŷ_0(q) = k + K + ŷ_{H♯}(q + 1)` with
`H♯ = (I, k, K − 1, 1)` (`pool_zero`), and `house_Z` follows `ŷ_{H♯}` along the walk.
-/

@[expose] public section

namespace PodiumWalk

open Finset AntitonicFit TheoremF Potential Windows

/-- **House form of Proposition 9.4** (`C35b_the_podium_walk.md`, Part Z, sketch): for the house
`H♯ = (I, k, 2^k − 1, 1)`, with `tailVal k I l = −ψ(I ∖ P_l)` and `t₁ = min I`:
(a) if `1 ≤ s`, `ŷ(1)` is the maximum of `tailVal k I 1 − 2^{t₁}` and of `tailVal k I l`,
`2 ≤ l ≤ s`;
(b) for `2 ≤ p < N`, `ŷ(p) ≤ tailVal k I l` for some `2 ≤ l ≤ s`. -/
theorem house_Z : ∀ (n : ℕ) (I : Finset ℕ) (k : ℕ), #I = n → (∀ t ∈ I, t < k) →
    (1 ≤ #I →
      tailVal k I 1 - 2 ^ Rulers.minOr k I ≤ yhat I k (2 ^ k - 1) 1 1 ∧
      (∀ l, 2 ≤ l → l ≤ #I → tailVal k I l ≤ yhat I k (2 ^ k - 1) 1 1) ∧
      (yhat I k (2 ^ k - 1) 1 1 = tailVal k I 1 - 2 ^ Rulers.minOr k I ∨
        ∃ l, 2 ≤ l ∧ l ≤ #I ∧ yhat I k (2 ^ k - 1) 1 1 = tailVal k I l)) ∧
    (∀ p, 2 ≤ p → p < 2 ^ #I →
      ∃ l, 2 ≤ l ∧ l ≤ #I ∧ yhat I k (2 ^ k - 1) 1 p ≤ tailVal k I l) := by
  intro n
  induction n with
  | zero =>
    intro I k hn _
    refine ⟨fun h => by omega, fun p h1 h2 => by rw [hn] at h2; simp at h2; omega⟩
  | succ n ih =>
    intro I k hn hI
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    obtain ⟨hcI, hcmax, hI', hck, hcard⟩ := erase_facts hI hne hc
    have hℓ : 2 ^ k - 1 < 2 ^ k := by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
    obtain ⟨hA, hB⟩ := ih (I.erase c) c (by omega) hI'
    set s := #(I.erase c) with hs
    set ψc : ℤ := (Rulers.h k I c : ℤ) - 2 ^ c with hψc
    have hT : ∀ l ≤ s, tailVal k I l = tailVal c (I.erase c) l - ψc := fun l hl =>
      tailVal_step hI hcI hcmax hl
    have htop : tailVal k I (s + 1) = 0 := by rw [hcard]; exact tailVal_top k I
    have hw : ∀ p, 0 < p → p < 2 ^ s →
        yhat I k (2 ^ k - 1) 1 p = max (yhat (I.erase c) c (2 ^ c - 1) 1 p - ψc) 0 := by
      intro p hp0 hp
      rw [walk_lt hI hℓ le_rfl hne hc hp, dWalk_top hI hcI hcmax hp, if_neg (by omega),
        two_pow_sub_one_mod hck, ← sub_eq_add_neg]
    refine ⟨fun h1 => ?_, fun p hp2 hp => ?_⟩
    · by_cases hs0 : s = 0
      · have hI'e : I.erase c = ∅ := card_eq_zero.1 hs0
        have hcard1 : #I = 1 := by omega
        have hmin : Rulers.minOr k I = c := by
          apply Rulers.minOr_eq_of_mem hcI
          intro x hx
          by_contra hlt
          have : x ∈ I.erase c := mem_erase.2 ⟨by omega, hx⟩
          rw [hI'e] at this
          simp at this
        have hy1 : yhat I k (2 ^ k - 1) 1 1 = -2 ^ c := by
          rw [walk_ge hI hℓ le_rfl hne hc (show 2 ^ s ≤ 1 by rw [hs0]; norm_num)
            (by rw [hcard1]; norm_num), show 2 ^ #I - 1 - 1 = 0 by rw [hcard1]; norm_num,
            dWalk_top hI hcI hcmax (show 0 < 2 ^ s by positivity), if_pos rfl,
            yhat_empty (I := I.erase c) hs0, zero_add, max_eq_left (by positivity)]
        have ht1 : tailVal k I 1 = 0 := by rw [← hcard1]; exact tailVal_top k I
        rw [hy1, ht1, hmin]
        refine ⟨by linarith, fun l h2 h3 => by omega, Or.inl (by ring)⟩
      · have hs1 : 1 ≤ s := by omega
        have hne' : (I.erase c).Nonempty := card_pos.1 (by omega)
        have hmin := minOr_erase (k := k) hcmax hne'
        obtain ⟨A1, A2, A3⟩ := hA hs1
        have h1M : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
        rw [hw 1 one_pos h1M, hmin, ← hcard]
        have hT1 := hT 1 hs1
        refine ⟨?_, fun l h2 h3 => ?_, ?_⟩
        · rw [hT1]
          exact le_max_of_le_left (by linarith)
        · rcases Nat.lt_or_ge l (s + 1) with h | h
          · rw [hT l (by omega)]
            exact le_max_of_le_left (by linarith [A2 l h2 (by omega)])
          · rw [show l = s + 1 by omega, htop]
            exact le_max_right _ _
        · by_cases h0 : 0 ≤ yhat (I.erase c) c (2 ^ c - 1) 1 1 - ψc
          · rw [max_eq_left h0]
            rcases A3 with he | ⟨l, h2, h3, he⟩
            · left; rw [he, hT1]; ring
            · right; exact ⟨l, h2, by omega, by rw [he, hT l h3]⟩
          · right
            exact ⟨s + 1, by omega, le_rfl, by rw [max_eq_right (by omega), htop]⟩
    · by_cases hpM : p < 2 ^ s
      · have hs1 : 1 ≤ s := by
          by_contra h
          have : s = 0 := by omega
          rw [this] at hpM
          omega
        rw [hw p (by omega) hpM, ← hcard]
        exact max_bound hT htop (by omega) (hB p hp2 hpM)
      · refine ⟨s + 1, ?_, by omega, ?_⟩
        · by_contra hlt
          have : s = 0 := by omega
          rw [this] at hpM
          have : #I = 1 := by omega
          rw [this] at hp
          omega
        · rw [htop]
          exact walk_ge_nonpos hI hℓ le_rfl hne hc (not_lt.1 hpM) hp

/-- The pooled clocks at shift `0` (C16 `R2`, C9 `lemma_7_9_I3`; sketch of Part Z of
`C35b_the_podium_walk.md`): for `I ≠ ∅` and `q < N − 1`, `ŷ_0(q) = k + K + ŷ_{H♯}(q + 1)` with
`H♯ = (I, k, K − 1, 1)`. -/
lemma pool_zero (ds : List Bool) (hne : (Ids ds).Nonempty) {q : ℕ}
    (hq : q < 2 ^ Dance.mCount ds - 1) :
    FamilyGroup.yPool0 ds q =
      (ds.length : ℤ) + 2 ^ ds.length + yhat (Ids ds) ds.length (2 ^ ds.length - 1) 1 (q + 1) := by
  have h2 := (FamilyGroup.R2 ds q hq).1
  have h3 := (CellFloor.lemma_7_9_I3 (DanceSmith.hI_Ids ds) rfl (le_refl (1 : ℤ)) hne).2.2.2.1 q
    (by rw [card_Ids]; exact hq)
  rw [CellFloor.yhatSharp] at h2
  rw [h3] at h2
  rw [FamilyGroup.yPool0, ← h2]

/-- **(Z1)** of `C35b_the_podium_walk.md` (Proposition 9.4), for every digit list: if `1 ≤ s`,
with `v := ŷ_0(0)` (the dancer `{t₁}`), `φ(Y_1) − 2^{t₁} ≤ v`, `φ(Y_l) ≤ v` for `2 ≤ l ≤ s`, and
`v` equals one of these. -/
theorem Z1_ds (ds : List Bool) (hs : 1 ≤ (Ids ds).card) :
    Rulers.phi (Podium.Y ds.length (Ids ds) 1) - 2 ^ Podium.tAt ds.length (Ids ds) 0 ≤
        FamilyGroup.yPool0 ds 0 ∧
      (∀ l, 2 ≤ l → l ≤ (Ids ds).card →
        Rulers.phi (Podium.Y ds.length (Ids ds) l) ≤ FamilyGroup.yPool0 ds 0) ∧
      (FamilyGroup.yPool0 ds 0 =
          Rulers.phi (Podium.Y ds.length (Ids ds) 1) - 2 ^ Podium.tAt ds.length (Ids ds) 0 ∨
        ∃ l, 2 ≤ l ∧ l ≤ (Ids ds).card ∧
          FamilyGroup.yPool0 ds 0 = Rulers.phi (Podium.Y ds.length (Ids ds) l)) := by
  have hI : Ids ds ⊆ range ds.length := fun t ht => mem_range.2 (lt_of_mem_Ids ht)
  have hne : (Ids ds).Nonempty := card_pos.1 (by omega)
  have ht1 : Podium.tAt ds.length (Ids ds) 0 = Rulers.minOr ds.length (Ids ds) := by
    rw [Podium.tAt, Podium.P_zero, sdiff_empty]
  have h1N : 0 < 2 ^ Dance.mCount ds - 1 := by
    rw [← card_Ids]
    have := Nat.one_lt_two_pow (n := #(Ids ds)) (by omega)
    omega
  obtain ⟨A1, A2, A3⟩ := (house_Z _ (Ids ds) ds.length rfl (DanceSmith.hI_Ids ds)).1 hs
  rw [pool_zero ds hne h1N, ht1, ← phi_Y hI]
  refine ⟨by linarith, fun l h2 h3 => ?_, ?_⟩
  · rw [← phi_Y hI]; linarith [A2 l h2 h3]
  · rcases A3 with he | ⟨l, h2, h3, he⟩
    · left; rw [he]; ring
    · right; exact ⟨l, h2, h3, by rw [he, ← phi_Y hI]⟩

/-- **(Z2)** of `C35b_the_podium_walk.md` (Proposition 9.4), for every digit list: for every
`1 ≤ q < N − 1` there is `l` with `2 ≤ l ≤ s` and `ŷ_0(q) ≤ φ(Y_l)`.  The hypothesis `2 ≤ s` of
the file is not needed (it follows from `1 ≤ q < N − 1`). -/
theorem Z2_ds (ds : List Bool) (q : ℕ) (hq1 : 1 ≤ q) (hq : q < 2 ^ Dance.mCount ds - 1) :
    ∃ l, 2 ≤ l ∧ l ≤ (Ids ds).card ∧
      FamilyGroup.yPool0 ds q ≤ Rulers.phi (Podium.Y ds.length (Ids ds) l) := by
  have hI : Ids ds ⊆ range ds.length := fun t ht => mem_range.2 (lt_of_mem_Ids ht)
  have hne : (Ids ds).Nonempty := by
    rw [← card_pos]
    by_contra h0
    have : (Ids ds).card = 0 := by omega
    rw [← card_Ids, this] at hq
    simp at hq
  obtain ⟨l, h2, h3, hle⟩ := (house_Z _ (Ids ds) ds.length rfl (DanceSmith.hI_Ids ds)).2 (q + 1)
    (by omega) (by rw [card_Ids]; omega)
  refine ⟨l, h2, h3, ?_⟩
  rw [pool_zero ds hne hq, ← phi_Y hI]
  linarith

/-- **(Z1)** of `C35b_the_podium_walk.md` (Proposition 9.4, shift `0`): for the family `λ`
(`d = Families.ds lam`) with `1 ≤ s`, and `v := yPool0 d 0` (the dancer `{t₁}`,
`t₁ = Podium.tAt k I 0`): `φ(Y 1) − 2^{t₁} ≤ v`, `φ(Y l) ≤ v` for every `2 ≤ l ≤ s`, and
`v = φ(Y 1) − 2^{t₁} ∨ ∃ l, 2 ≤ l ∧ l ≤ s ∧ v = φ(Y l)`.  The hypothesis `λ ≥ 1` is not needed. -/
theorem Z1 (lam : ℕ) (hs : 1 ≤ (Ids (Families.ds lam)).card) :
    Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) 1) -
        2 ^ Podium.tAt (Families.ds lam).length (Ids (Families.ds lam)) 0 ≤
        FamilyGroup.yPool0 (Families.ds lam) 0 ∧
      (∀ l, 2 ≤ l → l ≤ (Ids (Families.ds lam)).card →
        Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l) ≤
          FamilyGroup.yPool0 (Families.ds lam) 0) ∧
      (FamilyGroup.yPool0 (Families.ds lam) 0 =
          Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) 1) -
            2 ^ Podium.tAt (Families.ds lam).length (Ids (Families.ds lam)) 0 ∨
        ∃ l, 2 ≤ l ∧ l ≤ (Ids (Families.ds lam)).card ∧
          FamilyGroup.yPool0 (Families.ds lam) 0 =
            Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l)) :=
  Z1_ds (Families.ds lam) hs

/-- **(Z2)** of `C35b_the_podium_walk.md` (Proposition 9.4, shift `0`): for the family `λ` and every
`1 ≤ q < N − 1` there is `l` with `2 ≤ l ≤ s` and `yPool0 d q ≤ φ(Y l)`.  The hypotheses `λ ≥ 1`
and `2 ≤ s` are not needed (`2 ≤ s` follows from `1 ≤ q < N − 1`). -/
theorem Z2 (lam q : ℕ) (hq1 : 1 ≤ q) (hq : q < 2 ^ Dance.mCount (Families.ds lam) - 1) :
    ∃ l, 2 ≤ l ∧ l ≤ (Ids (Families.ds lam)).card ∧ FamilyGroup.yPool0 (Families.ds lam) q ≤
      Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l) :=
  Z2_ds (Families.ds lam) q hq1 hq

end PodiumWalk
