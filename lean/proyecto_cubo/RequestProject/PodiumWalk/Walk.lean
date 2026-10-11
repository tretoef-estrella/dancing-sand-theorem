module

public import RequestProject.CellFloor.All
public import RequestProject.Podium.All

/-!
# The walk through the fit of a house (`C35b_the_podium_walk.md`, sketches of Parts H, T, Z)

Auxiliary file of `C35b_the_podium_walk.md`.  Nothing is redefined: a house `H = (I, k, ℓ, α)` is
given by its components as in C6–C9, `ŷ_H` is `Potential.yhat I k ℓ α`
(`= AntitonicFit.ifit (2 ^ #I) (TheoremF.xHseq I k ℓ α)`), the walk increment is
`TheoremF.dWalk`, and the step of the walk is C7 `theorem_F0` (W3).  For `I ≠ ∅`, `c = max I`,
`I' = I.erase c`, `M = 2 ^ #I'`, `H' = (I', c, ℓ mod 2^c, α)` and `X₁ := ŷ_{H'} + d`:

* `walk_lt`: `ŷ_H(p) = max(X₁(p), 0)` for `p < M`;
* `walk_ge`: `ŷ_H(p) = −max(X₁(N − 1 − p), 0)` for `M ≤ p < N` (so `ŷ_H(p) ≤ 0` there).

`house_head` is the house form of step (H) of Proposition 9.6: the first level set of `ŷ_H` is
`[0, 2^l)` for some `l ≤ |I|`.
-/

@[expose] public section

namespace PodiumWalk

open Finset AntitonicFit TheoremF Potential

variable {I : Finset ℕ} {k ℓ : ℕ} {α : ℤ}

/-- The walk, first half (C7 `theorem_F0` (W3); sketch of Part H of `C35b_the_podium_walk.md`):
`ŷ_H(p) = max(ŷ_{H'}(p) + d(p), 0)` for `p < M`. -/
lemma walk_lt (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ}
    (hc : c = I.max' hne) {p : ℕ} (hp : p < 2 ^ #(I.erase c)) :
    yhat I k ℓ α p = max (yhat (I.erase c) c (ℓ % 2 ^ c) α p + dWalk I k ℓ α c p) 0 := by
  have hN := card_erase_max hne hc
  rw [yhat, (theorem_F0_W3 hI hℓ hα hne hc).2 p (by omega)]
  simp only [concat, if_pos hp, Pi.add_apply]
  rfl

/-- The walk, second half (C7 `theorem_F0` (W3); sketch of Part H of `C35b_the_podium_walk.md`):
`ŷ_H(p) = −max(ŷ_{H'}(N − 1 − p) + d(N − 1 − p), 0)` for `M ≤ p < N`. -/
lemma walk_ge (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty) {c : ℕ}
    (hc : c = I.max' hne) {p : ℕ} (hMp : 2 ^ #(I.erase c) ≤ p) (hp : p < 2 ^ #I) :
    yhat I k ℓ α p = -max (yhat (I.erase c) c (ℓ % 2 ^ c) α (2 ^ #I - 1 - p) +
      dWalk I k ℓ α c (2 ^ #I - 1 - p)) 0 := by
  have hN := card_erase_max hne hc
  rw [yhat, (theorem_F0_W3 hI hℓ hα hne hc).2 p hp]
  simp only [concat, if_neg (show ¬ p < 2 ^ #(I.erase c) by omega), mirror, Pi.add_apply]
  rw [min_neg_zero_int, show 2 ^ #(I.erase c) - 1 - (p - 2 ^ #(I.erase c)) = 2 ^ #I - 1 - p by
    omega]
  rfl

lemma walk_ge_nonpos (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) (hne : I.Nonempty)
    {c : ℕ} (hc : c = I.max' hne) {p : ℕ} (hMp : 2 ^ #(I.erase c) ≤ p) (hp : p < 2 ^ #I) :
    yhat I k ℓ α p ≤ 0 := by
  rw [walk_ge hI hℓ hα hne hc hMp hp]
  have := le_max_right (yhat (I.erase c) c (ℓ % 2 ^ c) α (2 ^ #I - 1 - p) +
      dWalk I k ℓ α c (2 ^ #I - 1 - p)) 0
  linarith

/-- The data of the smaller house `H'` (Part 2 of C7). -/
lemma erase_facts (hI : ∀ t ∈ I, t < k) (hne : I.Nonempty) {c : ℕ} (hc : c = I.max' hne) :
    c ∈ I ∧ (∀ t ∈ I, t ≤ c) ∧ (∀ t ∈ I.erase c, t < c) ∧ c < k ∧ #(I.erase c) + 1 = #I := by
  have hcI : c ∈ I := hc ▸ I.max'_mem hne
  have hcmax : ∀ t ∈ I, t ≤ c := fun t ht => hc ▸ I.le_max' t ht
  refine ⟨hcI, hcmax, fun t ht => ?_, hI c hcI, card_erase_add_one hcI⟩
  exact lt_of_le_of_ne (hcmax t (mem_of_mem_erase ht)) (ne_of_mem_erase ht)

/-- `ŷ_H` is non-increasing (Lemma 7.9 (I1), C9). -/
lemma yhat_anti (hI : ∀ t ∈ I, t < k) (hℓ : ℓ < 2 ^ k) (hα : 1 ≤ α) {p q : ℕ} (hpq : p ≤ q)
    (hq : q < 2 ^ #I) : yhat I k ℓ α q ≤ yhat I k ℓ α p :=
  (CellFloor.lemma_7_9_I1 hI hℓ hα).2.anti hpq hq

/-- The walk increment is non-increasing (C7 (W1)). -/
lemma dWalk_anti (c : ℕ) {p q : ℕ} (hpq : p ≤ q) (hq : q < 2 ^ #(I.erase c)) :
    dWalk I k ℓ α c q ≤ dWalk I k ℓ α c p := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_rfl
  | succ q hpq ih => exact (theorem_F0_W1_antitone α c q hq).trans (ih (by omega))

/-- If `f` is constant on `[0, B)` and every change of `δ` on `[0, B)` forces a strict drop of `f`,
then `δ` is constant on `[0, B)`. -/
lemma const_of_change_drop {f δ : ℕ → ℤ} {B : ℕ} (hf : ∀ p < B, f p = f 0)
    (hδ : ∀ b, 0 < b → b < B → δ (b - 1) ≠ δ b → f b < f (b - 1)) : ∀ p < B, δ p = δ 0 := by
  intro p hp
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [← ih (by omega)]
    by_contra hne
    have := hδ (p + 1) (by omega) hp (by simpa using fun h => hne h.symm)
    rw [hf _ hp, Nat.add_sub_cancel, hf p (by omega)] at this
    exact lt_irrefl _ this

/-- **House form of step (H) of Proposition 9.6** (`C35b_the_podium_walk.md`, Part H, sketch): for
every house `H = (I, k, ℓ, α)` there is `l ≤ |I|` such that `ŷ_H` is constant on `[0, 2^l)` and,
if `2^l < N`, `ŷ_H(2^l) < ŷ_H(0)`; i.e. the first level set of the fit of a house is the set of
positions `[0, 2^l)`. -/
theorem house_head : ∀ (n : ℕ) (I : Finset ℕ) (k ℓ : ℕ) (α : ℤ), #I = n → (∀ t ∈ I, t < k) →
    ℓ < 2 ^ k → 1 ≤ α →
    ∃ l ≤ #I, (∀ p < 2 ^ l, yhat I k ℓ α p = yhat I k ℓ α 0) ∧
      (2 ^ l < 2 ^ #I → yhat I k ℓ α (2 ^ l) < yhat I k ℓ α 0) := by
  intro n
  induction n with
  | zero =>
    intro I k ℓ α hn _ _ _
    refine ⟨0, by omega, fun p hp => ?_, fun h => by rw [hn] at h; exact absurd h (lt_irrefl _)⟩
    rw [show p = 0 by simpa using hp]
  | succ n ih =>
    intro I k ℓ α hn hI hℓ hα
    have hne : I.Nonempty := card_pos.1 (by omega)
    set c := I.max' hne with hc
    obtain ⟨hcI, hcmax, hI', hck, hcard⟩ := erase_facts hI hne hc
    have hℓ' : ℓ % 2 ^ c < 2 ^ c := Nat.mod_lt _ (by positivity)
    obtain ⟨l', hl', hconst, hdrop⟩ := ih (I.erase c) c (ℓ % 2 ^ c) α (by omega) hI' hℓ' hα
    set M := 2 ^ #(I.erase c) with hM
    have hN : 2 ^ #I = 2 * M := card_erase_max hne hc
    set y' := yhat (I.erase c) c (ℓ % 2 ^ c) α with hy'
    set d := dWalk I k ℓ α c with hd
    have hlM : 2 ^ l' ≤ M := Nat.pow_le_pow_right (by norm_num) hl'
    -- `d` is constant on the first level set of `ŷ'`
    have hdconst : ∀ p < 2 ^ l', d p = d 0 := by
      apply const_of_change_drop hconst
      intro b hb0 hb hne'
      have hcut := dWalk_change_strictCut (k := k) α c (cut_erase_max hα hne hc) b hb0 (by omega)
        hne'
      have h2 := hcut.2
      rw [(CellFloor.lemma_7_9_I1 hI' hℓ' hα).1 b (by omega),
        (CellFloor.lemma_7_9_I1 hI' hℓ' hα).1 (b - 1) (by omega)] at h2
      exact_mod_cast h2
    have hX : ∀ p, p < M → y' p + d p ≤ y' 0 + d 0 := fun p hp =>
      add_le_add (yhat_anti hI' hℓ' hα (Nat.zero_le p) hp) (dWalk_anti c (Nat.zero_le p) hp)
    by_cases h0 : y' 0 + d 0 ≤ 0
    · -- no positive head: `ŷ_H ≡ 0`
      have hzero : ∀ p < 2 ^ #I, yhat I k ℓ α p = 0 := by
        intro p hp
        by_cases hpM : p < M
        · rw [walk_lt hI hℓ hα hne hc hpM]
          exact max_eq_right ((hX p hpM).trans h0)
        · rw [walk_ge hI hℓ hα hne hc (by omega) hp]
          rw [max_eq_right ((hX _ (by omega)).trans h0), neg_zero]
      refine ⟨#I, le_rfl, fun p hp => by rw [hzero p hp, hzero 0 (by positivity)],
        fun h => absurd h (lt_irrefl _)⟩
    · push_neg at h0
      have h00 : yhat I k ℓ α 0 = y' 0 + d 0 := by
        rw [walk_lt hI hℓ hα hne hc (by positivity)]; exact max_eq_left h0.le
      refine ⟨l', by omega, fun p hp => ?_, fun h => ?_⟩
      · rw [walk_lt hI hℓ hα hne hc (by omega), h00]
        change max (y' p + d p) 0 = _
        rw [hconst p hp, hdconst p hp]
        exact max_eq_left h0.le
      · rw [h00]
        by_cases hlt : 2 ^ l' < M
        · rw [walk_lt hI hℓ hα hne hc hlt]
          change max (y' (2 ^ l') + d (2 ^ l')) 0 < _
          have h1 := hdrop hlt
          have h2 : d (2 ^ l') ≤ d 0 := dWalk_anti c (Nat.zero_le _) hlt
          exact max_lt (by linarith) h0
        · have := walk_ge_nonpos hI hℓ hα hne hc (p := 2 ^ l') (by omega) h
          linarith

end PodiumWalk
