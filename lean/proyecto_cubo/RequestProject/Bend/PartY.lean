module

public import RequestProject.Bend.Defs

/-!
# `C50d_the_bend.md`: Part Y — the inverse of `Ψ + t`

`Ψ = PathSum.XiOp α c η ζ`, `t : ℚ_[2]` with `‖t‖ = 1/2`, `Ψ + t` is `XiOp α c η ζ + t • 1`.

* (Y0) `Y0`: `‖π(f)‖ ≤ (1/2)^α ≤ 1/4 < ‖t‖`, the ultrametric equality, and C45 `I`.
* (Y1) `Y1`: strong induction on `L`, from the recursion `coef_mul_split` of C43, with
  `‖C(L, b)‖·‖(L − b)!‖ = ‖L!‖ / ‖b!‖ ≤ ‖L!‖·2^{b−1}` (C43 `norm_factorial_ge`).
-/

@[expose] public section

noncomputable section

namespace Bend

open FormalOps FormalDance Finset

/-- Auxiliary for (Y0) of `C50d_the_bend.md`: `‖π(f) + t‖ = 1/2` for `α ≥ 2` and `‖t‖ = 1/2`. -/
lemma norm_piF_add {α c : ℕ} (hα : 2 ≤ α) {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (f : ℤ) :
    ‖PathSum.piF α c f + t‖ = 1 / 2 := by
  have h1 : ‖PathSum.piF α c f‖ ≤ (1 / 2 : ℝ) ^ α := PathSum.norm_piF_le α c f
  have h2 : (1 / 2 : ℝ) ^ α ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hα
  have hlt : ‖PathSum.piF α c f‖ < ‖t‖ := by rw [ht]; nlinarith
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le, ht]

/-- Auxiliary for (Y0) of `C50d_the_bend.md`: the coefficients of `Ψ + t`. -/
lemma coef_XiOp_add (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) (t : ℚ_[2]) (m : ℕ) (f : ℤ) :
    (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])).coef m f =
      (PathSum.XiOp α c η ζ).coef m f + if m = 0 then t else 0 := by
  rw [Bf.coef_add, Bf.coef_smul, Bf.coef_one]
  split_ifs <;> simp

/-- **(Y0)** of `C50d_the_bend.md` (the payments): let `α ≥ 2`, `c : ℕ` (any), `η` with
`‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, and `t` with `‖t‖ = 1/2`. Then for every `f : ℤ`,
`‖piF α c f + t‖ = 1/2` and `(XiOp α c η ζ + t • 1).coef 0 f = piF α c f + t`; hence there is
`Y` with `Agree ((XiOp α c η ζ + t • 1) * Y) 1` and `Agree (Y * (XiOp α c η ζ + t • 1)) 1`.
(The hypotheses on `η` and `ζ`, part of the setting of Part Y, are not needed: they are kept as
anonymous hypotheses.) -/
theorem Y0 {α c : ℕ} (hα : 2 ≤ α) {η : ℚ_[2]} (_ : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]}
    (_ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) :
    (∀ f : ℤ, ‖PathSum.piF α c f + t‖ = 1 / 2) ∧
      (∀ f : ℤ, (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])).coef 0 f = PathSum.piF α c f + t) ∧
      ∃ Y : Bf ℚ_[2], Agree ((PathSum.XiOp α c η ζ + t • 1) * Y) 1 ∧
        Agree (Y * (PathSum.XiOp α c η ζ + t • 1)) 1 := by
  have hc0 : ∀ f : ℤ, (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])).coef 0 f =
      PathSum.piF α c f + t := fun f => by rw [coef_XiOp_add]; simp
  refine ⟨norm_piF_add hα ht, hc0, Conjugation.I _ fun f _ => ?_⟩
  rw [hc0]
  intro h
  have := norm_piF_add (c := c) hα ht f
  rw [h, norm_zero] at this
  norm_num at this

/-- Auxiliary for (Y1) of `C50d_the_bend.md`: `‖C(L, b)‖·‖(L − b)!‖ ≤ ‖L!‖·2^{b−1}` for
`1 ≤ b ≤ L`. -/
lemma norm_choose_mul_factorial_le {L b : ℕ} (hb : 1 ≤ b) (hbL : b ≤ L) :
    ‖((L.choose b : ℕ) : ℚ_[2])‖ * ‖(((L - b).factorial : ℕ) : ℚ_[2])‖ ≤
      ‖((L.factorial : ℕ) : ℚ_[2])‖ * 2 ^ (b - 1) := by
  have hid : ‖((L.choose b : ℕ) : ℚ_[2])‖ * ‖(((L - b).factorial : ℕ) : ℚ_[2])‖ *
      ‖((b.factorial : ℕ) : ℚ_[2])‖ = ‖((L.factorial : ℕ) : ℚ_[2])‖ := by
    rw [← norm_mul, ← norm_mul, ← Nat.cast_mul, ← Nat.cast_mul, mul_assoc, mul_comm (L - b).factorial,
      ← mul_assoc, Nat.choose_mul_factorial_mul_factorial hbL]
  have hfb := PathSum.norm_factorial_ge b hb
  have hpos : (0 : ℝ) < (1 / 2) ^ (b - 1) := by positivity
  have h2 : (2 : ℝ) ^ (b - 1) * (1 / 2) ^ (b - 1) = 1 := by
    rw [← mul_pow]; norm_num
  have hA := norm_nonneg ((L.choose b : ℕ) : ℚ_[2])
  have hB := norm_nonneg (((L - b).factorial : ℕ) : ℚ_[2])
  set P := ‖((L.choose b : ℕ) : ℚ_[2])‖ * ‖(((L - b).factorial : ℕ) : ℚ_[2])‖
  have hP : 0 ≤ P := mul_nonneg hA hB
  calc P = P * ((2 : ℝ) ^ (b - 1) * (1 / 2) ^ (b - 1)) := by rw [h2, mul_one]
    _ ≤ P * ((2 : ℝ) ^ (b - 1) * ‖((b.factorial : ℕ) : ℚ_[2])‖) := by gcongr
    _ = ‖((L.factorial : ℕ) : ℚ_[2])‖ * 2 ^ (b - 1) := by rw [← hid]; ring

/-- **(Y1)** of `C50d_the_bend.md` (the bound): let `α ≥ 2`, `c : ℕ` (any, `c = 0` included),
`η` with `‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, and `t` with `‖t‖ = 1/2`. For every `Y`
with `Agree ((XiOp α c η ζ + t • 1) * Y) 1`, all `L : ℕ` and `f : ℤ` with `(L : ℤ) ≤ f`:
`‖Y.coef L f‖ ≤ ‖((L.factorial : ℕ) : ℚ_[2])‖ * 2 ^ (L + 1)`. -/
theorem Y1 {α c : ℕ} (hα : 2 ≤ α) {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]}
    (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y : Bf ℚ_[2])
    (hY : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Y) 1) :
    ∀ L : ℕ, ∀ f : ℤ, (L : ℤ) ≤ f →
      ‖Y.coef L f‖ ≤ ‖((L.factorial : ℕ) : ℚ_[2])‖ * 2 ^ (L + 1) := by
  set x := PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]) with hx
  have hx0 : ∀ f : ℤ, x.coef 0 f = PathSum.piF α c f + t := fun f => by
    rw [hx, coef_XiOp_add]; simp
  have hxa : ∀ a : ℕ, ∀ f : ℤ, ‖x.coef (a + 1) f‖ ≤ 1 := by
    intro a f
    rw [hx, coef_XiOp_add, if_neg (by omega), add_zero]
    rcases a with _ | a
    · rw [PathSum.XiOp_coef_one, hη]
    · rw [PathSum.XiOp_coef_ge_two _ _ _ _ (by omega)]; exact hζ _ (by omega) f
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro f hf
  have e := hY L f hf
  rw [PathSum.coef_mul_split, hx0, Bf.coef_one] at e
  have hp := norm_piF_add (c := c) hα ht f
  set p := PathSum.piF α c f + t
  set S := ∑ a ∈ range L, (L.choose (a + 1) : ℚ_[2]) * x.coef (a + 1) f *
    Y.coef (L - (a + 1)) (f - ((a + 1 : ℕ) : ℤ))
  have hY' : ‖Y.coef L f‖ = 2 * ‖(if L = 0 then (1 : ℚ_[2]) else 0) - S‖ := by
    have : p * Y.coef L f = (if L = 0 then (1 : ℚ_[2]) else 0) - S := by rw [← e]; ring
    have h2 := congrArg norm this
    rw [norm_mul, hp] at h2
    linarith
  rcases L with _ | n
  · rw [hY']
    simp [S]
  · rw [hY', if_neg (by omega), zero_sub, norm_neg]
    have hS : ‖S‖ ≤ ‖(((n + 1).factorial : ℕ) : ℚ_[2])‖ * 2 ^ (n + 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro a ha
      have ha' := mem_range.mp ha
      have hih := ih (n + 1 - (a + 1)) (by omega) (f - ((a + 1 : ℕ) : ℤ))
        (by push_cast [Nat.cast_sub (show a + 1 ≤ n + 1 by omega)] at hf ⊢; omega)
      have hcm := norm_choose_mul_factorial_le (L := n + 1) (b := a + 1) (by omega) (by omega)
      rw [norm_mul, norm_mul]
      have h1 := hxa a f
      have hn1 := norm_nonneg (((n + 1).choose (a + 1) : ℕ) : ℚ_[2])
      have hn2 := norm_nonneg (Y.coef (n + 1 - (a + 1)) (f - ((a + 1 : ℕ) : ℤ)))
      calc ‖(((n + 1).choose (a + 1) : ℕ) : ℚ_[2])‖ * ‖x.coef (a + 1) f‖ *
            ‖Y.coef (n + 1 - (a + 1)) (f - ((a + 1 : ℕ) : ℤ))‖
          ≤ ‖(((n + 1).choose (a + 1) : ℕ) : ℚ_[2])‖ * 1 *
            (‖(((n + 1 - (a + 1)).factorial : ℕ) : ℚ_[2])‖ * 2 ^ (n + 1 - (a + 1) + 1)) := by
            gcongr
        _ = (‖(((n + 1).choose (a + 1) : ℕ) : ℚ_[2])‖ *
            ‖(((n + 1 - (a + 1)).factorial : ℕ) : ℚ_[2])‖) * 2 ^ (n + 1 - (a + 1) + 1) := by
            ring
        _ ≤ (‖(((n + 1).factorial : ℕ) : ℚ_[2])‖ * 2 ^ (a + 1 - 1)) *
            2 ^ (n + 1 - (a + 1) + 1) := by gcongr
        _ = ‖(((n + 1).factorial : ℕ) : ℚ_[2])‖ * 2 ^ (n + 1) := by
            rw [mul_assoc, ← pow_add]
            congr 2
            omega
    calc 2 * ‖S‖ ≤ 2 * (‖(((n + 1).factorial : ℕ) : ℚ_[2])‖ * 2 ^ (n + 1)) := by gcongr
      _ = ‖(((n + 1).factorial : ℕ) : ℚ_[2])‖ * 2 ^ (n + 1 + 1) := by ring

end Bend
