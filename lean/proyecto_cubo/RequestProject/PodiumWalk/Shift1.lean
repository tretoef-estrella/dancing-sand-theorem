module

public import RequestProject.PodiumWalk.Steps
public import RequestProject.PodiumWalk.Head

/-!
# Part T of `C35b_the_podium_walk.md` (Proposition 9.3, shift `1`)

Encodings as in `Head.lean`: `ds : List Bool`, `k = ds.length`, `I = Windows.Ids ds`,
`s = I.card`, `N = 2 ^ Dance.mCount ds` (`= 2 ^ s`, C14 `card_Ids`), `Y l = Podium.Y k I l`; the
family `λ` is `ds = Families.ds lam`.  Maxima are written with explicit witnesses: «`v` is the
maximum of `f(l)`, `l ∈ L`» is `(∃ l₀ ∈ L, v = f l₀) ∧ ∀ l ∈ L, f l ≤ v`.

At shift `1` the pooled clocks are `ŷ_1(p) = k + K + ŷ_H(p)` with `H = (I, k, 0, 1)`
(`pool_one`), and `house_T` follows `ŷ_H` along the walk; `phi_Y` turns `k + K − ψ(I ∖ P_l)` into
`φ(Y_l)`.
-/

@[expose] public section

namespace PodiumWalk

open Finset AntitonicFit TheoremF Potential Windows

/-- One step of the walk at the position of a running maximum (sketches of Parts T and Z of
`C35b_the_podium_walk.md`): if `v = max_{a ≤ l ≤ s} T'(l)` then
`max(v − ψ, 0) = max_{a ≤ l ≤ s + 1} T(l)`, where `T(l) = T'(l) − ψ` for `l ≤ s` and
`T(s + 1) = 0`. -/
lemma max_attain {v ψ : ℤ} {T T' : ℕ → ℤ} {a s : ℕ}
    (hT : ∀ l ≤ s, T l = T' l - ψ) (htop : T (s + 1) = 0)
    (hatt : ∃ l, a ≤ l ∧ l ≤ s ∧ v = T' l) (hbd : ∀ l, a ≤ l → l ≤ s → T' l ≤ v) :
    (∃ l, a ≤ l ∧ l ≤ s + 1 ∧ max (v - ψ) 0 = T l) ∧
      ∀ l, a ≤ l → l ≤ s + 1 → T l ≤ max (v - ψ) 0 := by
  obtain ⟨l0, ha, hl0, he⟩ := hatt
  refine ⟨?_, fun l hal hl => ?_⟩
  · by_cases h : 0 ≤ v - ψ
    · exact ⟨l0, ha, by omega, by rw [max_eq_left h, hT l0 hl0, he]⟩
    · exact ⟨s + 1, by omega, le_rfl, by rw [max_eq_right (by omega), htop]⟩
  · rcases Nat.lt_or_ge l (s + 1) with h | h
    · rw [hT l (by omega)]
      exact le_max_of_le_left (by linarith [hbd l hal (by omega)])
    · rw [show l = s + 1 by omega, htop]
      exact le_max_right _ _

/-- One step of the walk below a running bound (sketches of Parts T and Z of
`C35b_the_podium_walk.md`). -/
lemma max_bound {v ψ : ℤ} {T T' : ℕ → ℤ} {a s : ℕ}
    (hT : ∀ l ≤ s, T l = T' l - ψ) (htop : T (s + 1) = 0) (has : a ≤ s + 1)
    (h : ∃ l, a ≤ l ∧ l ≤ s ∧ v ≤ T' l) :
    ∃ l, a ≤ l ∧ l ≤ s + 1 ∧ max (v - ψ) 0 ≤ T l := by
  obtain ⟨l, ha, hl, hv⟩ := h
  by_cases h0 : 0 ≤ T' l - ψ
  · exact ⟨l, ha, by omega, max_le (by rw [hT l hl]; linarith) (by rw [hT l hl]; exact h0)⟩
  · exact ⟨s + 1, has, le_rfl, by rw [htop]; exact max_le (by linarith) le_rfl⟩

/-- **House form of Proposition 9.3** (`C35b_the_podium_walk.md`, Part T, sketch): for the house
`H = (I, k, 0, 1)`, with `tailVal k I l = −ψ(I ∖ P_l)`:
(a) `ŷ_H(0) = max_{0 ≤ l ≤ s} tailVal k I l`;
(b) for `1 ≤ p < N`, `ŷ_H(p) ≤ tailVal k I l` for some `1 ≤ l ≤ s`;
(c) if `0 ∈ I`, `ŷ_H(1) = max_{1 ≤ l ≤ s} tailVal k I l`. -/
theorem house_T : ∀ (n : ℕ) (I : Finset ℕ) (k : ℕ), #I = n → (∀ t ∈ I, t < k) →
    ((∃ l₀, 0 ≤ l₀ ∧ l₀ ≤ #I ∧ yhat I k 0 1 0 = tailVal k I l₀) ∧
      ∀ l, 0 ≤ l → l ≤ #I → tailVal k I l ≤ yhat I k 0 1 0) ∧
    (∀ p, 1 ≤ p → p < 2 ^ #I → ∃ l, 1 ≤ l ∧ l ≤ #I ∧ yhat I k 0 1 p ≤ tailVal k I l) ∧
    (0 ∈ I → (∃ l₁, 1 ≤ l₁ ∧ l₁ ≤ #I ∧ yhat I k 0 1 1 = tailVal k I l₁) ∧
      ∀ l, 1 ≤ l → l ≤ #I → tailVal k I l ≤ yhat I k 0 1 1) := by
  intro n
  induction n with
  | zero =>
    intro I k hn _
    have hI0 : I = ∅ := card_eq_zero.1 hn
    subst hI0
    refine ⟨⟨⟨0, le_rfl, by simp, by rw [yhat_empty rfl, tailVal_empty]⟩,
      fun l _ _ => by rw [yhat_empty rfl, tailVal_empty]⟩,
      fun p h1 h2 => by simp at h2; omega, fun h => by simp at h⟩
  | succ n ih =>
    intro I k hn hI
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    obtain ⟨hcI, hcmax, hI', hck, hcard⟩ := erase_facts hI hne hc
    have hℓ : (0 : ℕ) < 2 ^ k := by positivity
    obtain ⟨hA, hB, hC⟩ := ih (I.erase c) c (by omega) hI'
    set s := #(I.erase c) with hs
    set ψc : ℤ := (Rulers.h k I c : ℤ) - 2 ^ c with hψc
    have hT : ∀ l ≤ s, tailVal k I l = tailVal c (I.erase c) l - ψc := fun l hl =>
      tailVal_step hI hcI hcmax hl
    have htop : tailVal k I (s + 1) = 0 := by rw [hcard]; exact tailVal_top k I
    have hw : ∀ p < 2 ^ s, yhat I k 0 1 p = max (yhat (I.erase c) c 0 1 p - ψc) 0 := by
      intro p hp
      rw [walk_lt hI hℓ le_rfl hne hc hp, dWalk_zero hcmax p, Nat.zero_mod, ← sub_eq_add_neg]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw 0 (by positivity), ← hcard]
      exact max_attain hT htop hA.1 hA.2
    · intro p hp1 hp
      by_cases hpM : p < 2 ^ s
      · rw [hw p hpM, ← hcard]
        refine max_bound hT htop (by omega) (hB p hp1 hpM)
      · refine ⟨s + 1, by omega, by omega, ?_⟩
        rw [htop]
        exact walk_ge_nonpos hI hℓ le_rfl hne hc (not_lt.1 hpM) hp
    · intro h0I
      by_cases hs0 : s = 0
      · have hI'e : I.erase c = ∅ := card_eq_zero.1 hs0
        have hc0 : c = 0 := by
          by_contra hne0
          have : (0 : ℕ) ∈ I.erase c := mem_erase.2 ⟨fun h => hne0 h.symm, h0I⟩
          rw [hI'e] at this
          simp at this
        have hcard1 : #I = 1 := by omega
        have hψ : 0 ≤ ψc := by
          have h1 : (1 : ℤ) ≤ Rulers.h k I c := by exact_mod_cast Rulers.one_le_h hI hcI
          have h2 : (2 : ℤ) ^ c = 1 := by rw [hc0, pow_zero]
          rw [hψc, h2]; linarith
        have hy1 : yhat I k 0 1 1 = 0 := by
          rw [walk_ge hI hℓ le_rfl hne hc (show 2 ^ s ≤ 1 by rw [hs0]; norm_num)
            (by rw [hcard1]; norm_num),
            show 2 ^ #I - 1 - 1 = 0 by rw [hcard1]; norm_num, dWalk_zero hcmax, Nat.zero_mod,
            yhat_empty (I := I.erase c) hs0, max_eq_right (by linarith), neg_zero]
        have ht1 : tailVal k I 1 = 0 := by rw [← hcard1]; exact tailVal_top k I
        refine ⟨⟨1, le_rfl, by omega, by rw [hy1, ht1]⟩, fun l h1 h2 => ?_⟩
        rw [show l = 1 by omega, ht1, hy1]
      · have hne' : (I.erase c).Nonempty := card_pos.1 (by omega)
        obtain ⟨t, ht⟩ := hne'
        have h0I' : 0 ∈ I.erase c := mem_erase.2 ⟨by have := hI' t ht; omega, h0I⟩
        obtain ⟨hC1, hC2⟩ := hC h0I'
        have h1M : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
        rw [hw 1 h1M, ← hcard]
        exact max_attain hT htop hC1 hC2

/-- The pooled clocks at shift `1` (sketch of Part T of `C35b_the_podium_walk.md`):
`ŷ_1(p) = k + K + ŷ_H(p)` with `H = (I, k, 0, 1)` (no carry is born: `J_H ≡ 0`). -/
lemma pool_one (ds : List Bool) {p : ℕ} (hp : p < 2 ^ Dance.mCount ds) :
    FamilyGroup.yPool ds 1 p = (ds.length : ℤ) + 2 ^ ds.length + yhat (Ids ds) ds.length 0 1 p := by
  rw [(pool_facts ds 1 le_rfl).2 p hp]
  have hJ : ∀ q, JHseq (Ids ds) ds.length 0 q = 0 := by
    intro q
    have := Rulers.oE_lt (dancer (Ids ds) q) ds.length
      (fun t ht => lt_of_mem_Ids (lemma_0a _ q ht))
    simp only [JHseq, Houses.JH, zero_add]
    rw [if_neg (by omega)]
  simp [CellFloor.cellShift, hJ, DanceSmith.Cst, Rulers.kappa]

/-- **(T1)** of `C35b_the_podium_walk.md` (Proposition 9.3), for every digit list:
`ŷ_1(0) = max_{0 ≤ l ≤ s} φ(Y_l)`. -/
theorem T1_ds (ds : List Bool) :
    (∃ l₀ ≤ (Ids ds).card,
      FamilyGroup.yPool ds 1 0 = Rulers.phi (Podium.Y ds.length (Ids ds) l₀)) ∧
    ∀ l ≤ (Ids ds).card, Rulers.phi (Podium.Y ds.length (Ids ds) l) ≤ FamilyGroup.yPool ds 1 0 := by
  have hI : Ids ds ⊆ range ds.length := fun t ht => mem_range.2 (lt_of_mem_Ids ht)
  obtain ⟨⟨⟨l₀, -, hl₀, he⟩, hb⟩, -, -⟩ :=
    house_T _ (Ids ds) ds.length rfl (DanceSmith.hI_Ids ds)
  rw [pool_one ds (by positivity)]
  refine ⟨⟨l₀, hl₀, by rw [he, ← phi_Y hI]⟩, fun l hl => ?_⟩
  rw [← phi_Y hI]
  linarith [hb l (Nat.zero_le l) hl]

/-- **(T2)** of `C35b_the_podium_walk.md` (Proposition 9.3), for every digit list: for every
`1 ≤ p < N` there is `l` with `1 ≤ l ≤ s` and `ŷ_1(p) ≤ φ(Y_l)`.  The hypothesis `1 ≤ s` of the
file is not needed (it follows from `1 ≤ p < N = 2^s`). -/
theorem T2_ds (ds : List Bool) (p : ℕ) (hp1 : 1 ≤ p) (hp : p < 2 ^ Dance.mCount ds) :
    ∃ l, 1 ≤ l ∧ l ≤ (Ids ds).card ∧
      FamilyGroup.yPool ds 1 p ≤ Rulers.phi (Podium.Y ds.length (Ids ds) l) := by
  have hI : Ids ds ⊆ range ds.length := fun t ht => mem_range.2 (lt_of_mem_Ids ht)
  obtain ⟨-, hB, -⟩ := house_T _ (Ids ds) ds.length rfl (DanceSmith.hI_Ids ds)
  obtain ⟨l, hl1, hl, hle⟩ := hB p hp1 (by rw [card_Ids]; exact hp)
  refine ⟨l, hl1, hl, ?_⟩
  rw [pool_one ds hp, ← phi_Y hI]
  linarith

/-- **(T3)** of `C35b_the_podium_walk.md` (Proposition 9.3), for every digit list: if `0 ∈ I`,
`ŷ_1(1) = max_{1 ≤ l ≤ s} φ(Y_l)`. -/
theorem T3_ds (ds : List Bool) (h0 : 0 ∈ Ids ds) :
    (∃ l₁, 1 ≤ l₁ ∧ l₁ ≤ (Ids ds).card ∧
      FamilyGroup.yPool ds 1 1 = Rulers.phi (Podium.Y ds.length (Ids ds) l₁)) ∧
    ∀ l, 1 ≤ l → l ≤ (Ids ds).card →
      Rulers.phi (Podium.Y ds.length (Ids ds) l) ≤ FamilyGroup.yPool ds 1 1 := by
  have hI : Ids ds ⊆ range ds.length := fun t ht => mem_range.2 (lt_of_mem_Ids ht)
  obtain ⟨-, -, hC⟩ := house_T _ (Ids ds) ds.length rfl (DanceSmith.hI_Ids ds)
  obtain ⟨⟨l₁, hl1, hl, he⟩, hb⟩ := hC h0
  have h1N : 1 < 2 ^ Dance.mCount ds := by
    rw [← card_Ids]; exact Nat.one_lt_two_pow (card_pos.2 ⟨0, h0⟩).ne'
  rw [pool_one ds h1N]
  refine ⟨⟨l₁, hl1, hl, by rw [he, ← phi_Y hI]⟩, fun l h1 h2 => ?_⟩
  rw [← phi_Y hI]
  linarith [hb l h1 h2]

/-- **(T1)** of `C35b_the_podium_walk.md` (Proposition 9.3, shift `1`): for the family `λ`
(`d = Families.ds lam`), `yPool d 1 0 = φ(Y l₀)` for some `l₀ ≤ s`, and `φ(Y l) ≤ yPool d 1 0`
for every `l ≤ s` (`e(∅) = max_{0 ≤ l ≤ s} φ(Y_l)`).  The hypothesis `λ ≥ 1` is not needed. -/
theorem T1 (lam : ℕ) :
    (∃ l₀ ≤ (Ids (Families.ds lam)).card, FamilyGroup.yPool (Families.ds lam) 1 0 =
      Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l₀)) ∧
    ∀ l ≤ (Ids (Families.ds lam)).card,
      Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l) ≤
        FamilyGroup.yPool (Families.ds lam) 1 0 :=
  T1_ds (Families.ds lam)

/-- **(T2)** of `C35b_the_podium_walk.md` (Proposition 9.3, shift `1`): for the family `λ` and
every `1 ≤ p < N` there is `l` with `1 ≤ l ≤ s` and `yPool d 1 p ≤ φ(Y l)`
(`e(D) ≤ max_{1 ≤ l ≤ s} φ(Y_l)` for `D ≠ ∅`).  The hypotheses `λ ≥ 1` and `1 ≤ s` are not needed
(`1 ≤ s` follows from `1 ≤ p < N`). -/
theorem T2 (lam p : ℕ) (hp1 : 1 ≤ p) (hp : p < 2 ^ Dance.mCount (Families.ds lam)) :
    ∃ l, 1 ≤ l ∧ l ≤ (Ids (Families.ds lam)).card ∧ FamilyGroup.yPool (Families.ds lam) 1 p ≤
      Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l) :=
  T2_ds (Families.ds lam) p hp1 hp

/-- **(T3)** of `C35b_the_podium_walk.md` (Proposition 9.3, shift `1`): for the family `λ`, if
`0 ∈ I`, `yPool d 1 1 = φ(Y l₁)` for some `1 ≤ l₁ ≤ s`, and `φ(Y l) ≤ yPool d 1 1` for every
`1 ≤ l ≤ s` (`e({0}) = max_{1 ≤ l ≤ s} φ(Y_l)`).  The hypothesis `λ ≥ 1` is not needed. -/
theorem T3 (lam : ℕ) (h0 : 0 ∈ Ids (Families.ds lam)) :
    (∃ l₁, 1 ≤ l₁ ∧ l₁ ≤ (Ids (Families.ds lam)).card ∧
      FamilyGroup.yPool (Families.ds lam) 1 1 =
        Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l₁)) ∧
    ∀ l, 1 ≤ l → l ≤ (Ids (Families.ds lam)).card →
      Rulers.phi (Podium.Y (Families.ds lam).length (Ids (Families.ds lam)) l) ≤
        FamilyGroup.yPool (Families.ds lam) 1 1 :=
  T3_ds (Families.ds lam) h0

end PodiumWalk
