module

public import RequestProject.Cleanliness.Defs

/-!
# `C48_cleanliness_one_move.md`: the recursive inverses used in (W3)

Helpers for (W3) of `C48_cleanliness_one_move.md` (namespace `Cleanliness`). For a system `G`
whose constant coefficient `G ∅ 0 y` is a unit at every position, `rinv k G` is the right inverse
of the proof sketch of (W3) (well-founded recursion on `Δ.card + m`, isolating the term
`(Δ₁, a) = (∅, 0)` of `prodFun`), and `linv k G` is the left inverse by the mirror recursion
(isolating the term `(Δ₁, a) = (Δ, m)`).
-/

@[expose] public section

noncomputable section

namespace Cleanliness

open RingK Finset

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the decrease of the measure in the
recursion of the right inverse. -/
lemma rinv_dec {Δ : Finset ℕ} {m : ℕ} {x : Finset ℕ × ℕ}
    (hx : x ∈ (Δ.powerset ×ˢ range (m + 1)).erase (∅, 0)) :
    (Δ \ x.1).card + (m - x.2) < Δ.card + m := by
  obtain ⟨Δ₁, a⟩ := x
  simp only [mem_erase, mem_product, mem_powerset, mem_range, ne_eq, Prod.mk.injEq] at hx
  obtain ⟨hne, hsub, ha⟩ := hx
  have hc : (Δ \ Δ₁).card + Δ₁.card = Δ.card := card_sdiff_add_card_eq_card hsub
  by_cases h0 : Δ₁ = ∅
  · subst h0
    have : a ≠ 0 := fun h => hne ⟨rfl, h⟩
    simp only [sdiff_empty]
    omega
  · have : 0 < Δ₁.card := card_pos.2 (nonempty_iff_ne_empty.2 h0)
    simp only
    omega

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the right inverse of a system `G` at level
`k`, by well-founded recursion on `Δ.card + m`:
`rinv k G Δ m y = G ∅ 0 y⁻¹ · (Γ₁ Δ m y − Σ_{(Δ₁, a) ≠ (∅, 0)} C(m, a) G Δ₁ a y ·
rinv k G (Δ \ Δ₁) (m − a) (y − a 2^k − o_{Δ₁}))`. -/
def rinv (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    ℤ_[2] :=
  Ring.inverse (G ∅ 0 y) * ((if Δ = ∅ ∧ m = 0 then 1 else 0) -
    ∑ x ∈ ((Δ.powerset ×ˢ range (m + 1)).erase (∅, 0)).attach,
      (m.choose x.1.2 : ℤ_[2]) * G x.1.1 x.1.2 y *
        rinv k G (Δ \ x.1.1) (m - x.1.2) (y - x.1.2 * 2 ^ k - oS x.1.1))
termination_by Δ.card + m
decreasing_by exact rinv_dec x.2

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the decrease of the measure in the
recursion of the left inverse. -/
lemma linv_dec {Δ : Finset ℕ} {m : ℕ} {x : Finset ℕ × ℕ}
    (hx : x ∈ (Δ.powerset ×ˢ range (m + 1)).erase (Δ, m)) :
    x.1.card + x.2 < Δ.card + m := by
  obtain ⟨Δ₁, a⟩ := x
  simp only [mem_erase, mem_product, mem_powerset, mem_range, ne_eq, Prod.mk.injEq] at hx
  obtain ⟨hne, hsub, ha⟩ := hx
  by_cases h0 : Δ₁ = Δ
  · subst h0
    have : a ≠ m := fun h => hne ⟨rfl, h⟩
    simp only
    omega
  · have : Δ₁.card < Δ.card := card_lt_card (ssubset_of_subset_of_ne hsub h0)
    simp only
    omega

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the left inverse of a system `G` at level
`k`, by the mirror recursion:
`linv k G Δ m y = (Γ₁ Δ m y − Σ_{(Δ₁, a) ≠ (Δ, m)} C(m, a) linv k G Δ₁ a y ·
G (Δ \ Δ₁) (m − a) (y − a 2^k − o_{Δ₁})) · G ∅ 0 (y − m 2^k − o_Δ)⁻¹`. -/
def linv (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    ℤ_[2] :=
  ((if Δ = ∅ ∧ m = 0 then 1 else 0) -
    ∑ x ∈ ((Δ.powerset ×ˢ range (m + 1)).erase (Δ, m)).attach,
      (m.choose x.1.2 : ℤ_[2]) * linv k G x.1.1 x.1.2 y *
        G (Δ \ x.1.1) (m - x.1.2) (y - x.1.2 * 2 ^ k - oS x.1.1)) *
    Ring.inverse (G ∅ 0 (y - m * 2 ^ k - oS Δ))
termination_by Δ.card + m
decreasing_by exact linv_dec x.2

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: `prodFun` as a single sum over pairs. -/
lemma prodFun_eq_sum_pairs (k : ℕ) (G G' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ)
    (m : ℕ) (y : ℤ_[2]) :
    prodFun k G G' Δ m y = ∑ x ∈ Δ.powerset ×ˢ range (m + 1),
      (m.choose x.2 : ℤ_[2]) * G x.1 x.2 y * G' (Δ \ x.1) (m - x.2) (y - x.2 * 2 ^ k - oS x.1) := by
  rw [prodFun, sum_product]

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: `oS ∅ = 0`. -/
lemma oS_empty : oS ∅ = 0 := rfl

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the defining equation of `rinv`, with the
sum over pairs `(Δ₁, a) ≠ (∅, 0)`. -/
lemma rinv_eq (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    rinv k G Δ m y = Ring.inverse (G ∅ 0 y) * ((if Δ = ∅ ∧ m = 0 then 1 else 0) -
      ∑ x ∈ (Δ.powerset ×ˢ range (m + 1)).erase (∅, 0),
        (m.choose x.2 : ℤ_[2]) * G x.1 x.2 y *
          rinv k G (Δ \ x.1) (m - x.2) (y - x.2 * 2 ^ k - oS x.1)) := by
  rw [rinv, sum_attach _ (fun x : Finset ℕ × ℕ => (m.choose x.2 : ℤ_[2]) * G x.1 x.2 y *
    rinv k G (Δ \ x.1) (m - x.2) (y - x.2 * 2 ^ k - oS x.1))]

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the defining equation of `linv`, with the
sum over pairs `(Δ₁, a) ≠ (Δ, m)`. -/
lemma linv_eq (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    linv k G Δ m y = ((if Δ = ∅ ∧ m = 0 then 1 else 0) -
      ∑ x ∈ (Δ.powerset ×ˢ range (m + 1)).erase (Δ, m),
        (m.choose x.2 : ℤ_[2]) * linv k G x.1 x.2 y *
          G (Δ \ x.1) (m - x.2) (y - x.2 * 2 ^ k - oS x.1)) *
      Ring.inverse (G ∅ 0 (y - m * 2 ^ k - oS Δ)) := by
  rw [linv, sum_attach _ (fun x : Finset ℕ × ℕ => (m.choose x.2 : ℤ_[2]) * linv k G x.1 x.2 y *
    G (Δ \ x.1) (m - x.2) (y - x.2 * 2 ^ k - oS x.1))]

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: `rinv k G` is a right inverse of `G`. -/
theorem prodFun_rinv (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hG : ∀ y, IsUnit (G ∅ 0 y)) :
    prodFun k G (rinv k G) = fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0 := by
  funext Δ m y
  have hmem : ((∅ : Finset ℕ), 0) ∈ Δ.powerset ×ˢ range (m + 1) := by simp
  rw [prodFun_eq_sum_pairs, ← add_sum_erase _ _ hmem]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, sdiff_empty, Nat.sub_zero,
    Nat.cast_zero, zero_mul, sub_zero, oS_empty]
  rw [rinv_eq k G Δ m y, ← mul_assoc, Ring.mul_inverse_cancel _ (hG y), one_mul, sub_add_cancel]

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: `linv k G` is a left inverse of `G`. -/
theorem prodFun_linv (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hG : ∀ y, IsUnit (G ∅ 0 y)) :
    prodFun k (linv k G) G = fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0 := by
  funext Δ m y
  have hmem : (Δ, m) ∈ Δ.powerset ×ˢ range (m + 1) := by simp
  rw [prodFun_eq_sum_pairs, ← add_sum_erase _ _ hmem]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, sdiff_self, Nat.sub_self, Finset.bot_eq_empty]
  rw [linv_eq k G Δ m y, mul_assoc, Ring.inverse_mul_cancel _ (hG _), mul_one, sub_add_cancel]

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: if every `G Δ m` is in `Kr` and
`y ↦ G ∅ 0 y⁻¹` is in `Kr`, every `rinv k G Δ m` is in `Kr`. -/
theorem rinv_mem (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hG : ∀ Δ m, G Δ m ∈ Kr)
    (hu : (fun y => Ring.inverse (G ∅ 0 y)) ∈ Kr) : ∀ Δ m, rinv k G Δ m ∈ Kr := by
  suffices H : ∀ n, ∀ Δ m, Δ.card + m = n → rinv k G Δ m ∈ Kr from
    fun Δ m => H _ Δ m rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Δ m hn
  have heq : rinv k G Δ m = (fun y => Ring.inverse (G ∅ 0 y)) *
      ((fun _ => if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) -
        ∑ x ∈ ((Δ.powerset ×ˢ range (m + 1)).erase (∅, 0)).attach,
          (fun y => (m.choose x.1.2 : ℤ_[2]) * G x.1.1 x.1.2 y) *
            (fun y => rinv k G (Δ \ x.1.1) (m - x.1.2) (y - (x.1.2 * 2 ^ k + oS x.1.1)))) := by
    funext y
    rw [rinv]
    simp only [Pi.mul_apply, Pi.sub_apply, Finset.sum_apply, sub_sub]
  rw [heq]
  refine K3_mul hu (K3_sub (K3_const _) (Kr_sum _ _ fun x _ => K3_mul (K3_smul _ (hG _ _)) ?_))
  exact K4 (ih _ (hn ▸ rinv_dec x.2) _ _ rfl) _

end Cleanliness
