module

public import RequestProject.ArmsEven.PartH

/-!
# `C50c_the_arms_of_the_even_families.md`: Part C — the halves are congruent

(C1) if `Γ₁ ≡ Γ₀ (mod 2)`, the halves of `Γ₁ (Γ₁ − 2)` and `Γ₀ (Γ₀ + 2)` are congruent modulo `2`.
The computation is done modulo `4` in the commutative ring `RA (ZMod (2 ^ 2))` of C50b:
`(a₀ + 2δ)(a₀ + 2δ − 2) − a₀(a₀ + 2) = 4 (a₀δ + δ² − δ − a₀) = 0`.
-/

@[expose] public section

noncomputable section

namespace ArmsEven

open RingK Cleanliness DanceMod2 Finset

/-- Helper for (C1) of `C50c_the_arms_of_the_even_families.md`: `kap (2 • uSys) = 2`. -/
lemma kap_two_smul_uSys : kap ((2 : ℤ_[2]) • uSys) = 2 := by
  refine RA.ext fun Δ m => ?_
  rw [show (2 : RA (ZMod (2 ^ 2))) = 1 + 1 from one_add_one_eq_two.symm, RA.add_apply,
    RA.one_apply]
  show red4 (2 * uSys Δ m 0) = _
  by_cases hc : Δ = ∅ ∧ m = 0
  · simp only [uSys, hc, and_self, if_true, mul_one, map_ofNat]; norm_num
  · simp only [uSys, hc, if_false, mul_zero, map_zero, add_zero]

/-- Helper for (C1) of `C50c_the_arms_of_the_even_families.md`: `kap ((-2) • uSys) = -2`. -/
lemma kap_neg_two_smul_uSys : kap ((-2 : ℤ_[2]) • uSys) = -2 := by
  refine RA.ext fun Δ m => ?_
  rw [show (-2 : RA (ZMod (2 ^ 2))) = -(1 + 1) by rw [one_add_one_eq_two], RA.neg_apply,
    RA.add_apply, RA.one_apply]
  show red4 (-2 * uSys Δ m 0) = _
  by_cases hc : Δ = ∅ ∧ m = 0
  · simp only [uSys, hc, and_self, if_true, mul_one, map_neg, map_ofNat]; norm_num
  · simp only [uSys, hc, if_false, mul_zero, map_zero, add_zero, neg_zero]

/-- **(C1)** of `C50c_the_arms_of_the_even_families.md`: for `Γ₀ Γ₁` with `InK Γ₀`, `InK Γ₁` and
`Cong2 Γ₁ Γ₀`, every `h`, and `U U'` with
`2 * U Δ m y = prodFun h Γ₁ (Γ₁ + (-2) • uSys) Δ m y` and
`2 * U' Δ m y = prodFun h Γ₀ (Γ₀ + 2 • uSys) Δ m y`: `Cong2 U U'`. -/
theorem C1 (Γ₀ Γ₁ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (h₀ : InK Γ₀) (h₁ : InK Γ₁)
    (hc : Cong2 Γ₁ Γ₀) (h : ℕ) (U U' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hU : ∀ Δ m y, 2 * U Δ m y = prodFun h Γ₁ (Γ₁ + (-2 : ℤ_[2]) • uSys) Δ m y)
    (hU' : ∀ Δ m y, 2 * U' Δ m y = prodFun h Γ₀ (Γ₀ + (2 : ℤ_[2]) • uSys) Δ m y) :
    Cong2 U U' := by
  choose z hz using hc
  let δ : RA (ZMod (2 ^ 2)) := fun Δ m => red4 (z Δ m 0)
  have hkap1 : kap Γ₁ = kap Γ₀ + 2 * δ := RA.ext fun Δ m => by
    rw [RA.add_apply, RA.two_mul_apply]
    show red4 (Γ₁ Δ m 0) = red4 (Γ₀ Δ m 0) + 2 * red4 (z Δ m 0)
    rw [show Γ₁ Δ m 0 = Γ₀ Δ m 0 + 2 * z Δ m 0 by linear_combination hz Δ m 0, map_add,
      map_mul, map_ofNat]
  have hK1 : InK (Γ₁ + (-2 : ℤ_[2]) • uSys) := InK_add_smul_uSys h₁ _
  have hK0 : InK (Γ₀ + (2 : ℤ_[2]) • uSys) := InK_add_smul_uSys h₀ _
  have hkap : kap (prodFun h Γ₁ (Γ₁ + (-2 : ℤ_[2]) • uSys)) =
      kap (prodFun h Γ₀ (Γ₀ + (2 : ℤ_[2]) • uSys)) := by
    rw [K2_mul h _ _ hK1, K2_mul h _ _ hK0, K2_add, K2_add, kap_neg_two_smul_uSys,
      kap_two_smul_uSys, hkap1]
    linear_combination (kap Γ₀ * δ + δ * δ - δ - kap Γ₀) * RA.four_eq_zero
  intro Δ m y
  have hred : red4 (2 * U Δ m y - 2 * U' Δ m y) = 0 := by
    rw [map_sub, hU, hU', K1 ((T2 h _ _ h₁ hK1).1 Δ m), K1 ((T2 h _ _ h₀ hK0).1 Δ m)]
    have := congrArg (fun β : RA (ZMod (2 ^ 2)) => β Δ m) hkap
    exact sub_eq_zero.2 this
  obtain ⟨w, hw⟩ := (red4_eq_zero_iff _).1 hred
  refine ⟨w, mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) ?_⟩
  linear_combination hw

end ArmsEven
