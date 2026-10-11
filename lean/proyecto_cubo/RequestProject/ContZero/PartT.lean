module

public import RequestProject.ContZero.PartK

/-!
# `C49b_congruence_and_the_data_at_zero.md`: Part T — transport along the dance

* (T1) `T1`: induction on `ds`, generalizing `r, M, G, H, Gk, Hk`, as in the sketch; in the split
  clause the reindexing is along `(Dance.splitIso r).symm` followed by `ofLex`.
* (T2) `T2`: `finalM` reads the coefficient `(0, 0)`, covered by `Agree`.
* (T3) `T3`: (T1) with `H := G`, then (T2) and `eq_zero_of_forall_pow_mul`.
-/

@[expose] public section

noncomputable section

namespace ContZero

open FormalOps FormalDance

/-- **(T1)** of `C49b_congruence_and_the_data_at_zero.md`: for every `ds : List Bool`, `r M : ℕ`,
`G H : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` and `Gk Hk`: if `DanceRel ds r G Gk`,
`DanceRel ds r H Hk` and `MCong (M + ds.length) G H`, then `MCong M Gk Hk`. -/
theorem T1 (ds : List Bool) : ∀ (r M : ℕ) (G H : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (Gk Hk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])),
    DanceRel ds r G Gk → DanceRel ds r H Hk → MCong (M + ds.length) G H → MCong M Gk Hk := by
  induction ds with
  | nil =>
    intro r M G H Gk Hk hG hH hGH
    simp only [List.length_nil, Nat.add_zero] at hGH
    exact ((MCong.of_magree hG).symm.trans hGH).trans (MCong.of_magree hH)
  | cons d rest ih =>
    cases d
    · rintro r M G H Gk Hk ⟨G', c1, d1⟩ ⟨H', c2, d2⟩ hGH
      rw [List.length_cons, ← add_assoc] at hGH
      exact ih r M G' H' Gk Hk d1 d2 (K6 c1 c2 hGH)
    · rintro r M G H Gk Hk ⟨G', c1, d1⟩ ⟨H', c2, d2⟩ hGH
      rw [List.length_cons, ← add_assoc] at hGH
      have h := K6 c1 c2 hGH.vsplit
      exact ih (r * 2) M _ _ Gk Hk d1 d2
        (h.reindex ((Dance.splitIso r).symm.toEquiv.trans ofLex))

/-- **(T2)** of `C49b_congruence_and_the_data_at_zero.md` (the final matrices): if
`MCong M Gk Hk` (any index type `m`), then for all `s s'` there is `w : ℤ_[2]` with
`finalM Gk s s' - finalM Hk s s' = 2 ^ M * w`. -/
theorem T2 {m : Type*} {M : ℕ} {Gk Hk : Matrix m m (Bf ℤ_[2])} (h : MCong M Gk Hk) (s s' : m) :
    ∃ w : ℤ_[2], finalM Gk s s' - finalM Hk s s' = 2 ^ M * w := by
  obtain ⟨Z, hZ⟩ := h
  refine ⟨(Z s s').coef 0 0, ?_⟩
  have := hZ s s' 0 0 le_rfl
  simpa [finalM] using this

/-- Proof of (T3) of `C49b_congruence_and_the_data_at_zero.md`: `‖(2 : ℤ_[2])‖ = 2⁻¹`. -/
lemma norm_two_padic : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  have := PadicInt.norm_p (p := 2)
  exact_mod_cast this

/-- Proof of (T3) of `C49b_congruence_and_the_data_at_zero.md`: a multiple of `2 ^ M` has norm at
most `2⁻¹ ^ M`. -/
lemma norm_le_of_eq_pow_mul {x w : ℤ_[2]} {M : ℕ} (h : x = 2 ^ M * w) :
    ‖x‖ ≤ (2⁻¹ : ℝ) ^ M := by
  rw [h, norm_mul, norm_pow, norm_two_padic]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)

/-- Proof of (T3) of `C49b_congruence_and_the_data_at_zero.md`: an element of `ℤ_[2]` divisible
by every power of `2` is `0`. -/
lemma eq_zero_of_forall_pow_mul {x : ℤ_[2]} (h : ∀ M : ℕ, ∃ w, x = 2 ^ M * w) : x = 0 := by
  have hle : ‖x‖ ≤ 0 := by
    refine ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)) fun M => ?_
    obtain ⟨w, hw⟩ := h M
    exact norm_le_of_eq_pow_mul hw
  exact norm_le_zero_iff.1 hle

/-- **(T3)** of `C49b_congruence_and_the_data_at_zero.md` (uniqueness): if `DanceRel ds r G Gk`
and `DanceRel ds r G Hk`, then `finalM Gk = finalM Hk`. -/
theorem T3 {ds : List Bool} {r : ℕ} {G : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    {Gk Hk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])}
    (hG : DanceRel ds r G Gk) (hH : DanceRel ds r G Hk) : finalM Gk = finalM Hk := by
  funext s s'
  refine sub_eq_zero.1 (eq_zero_of_forall_pow_mul fun M => ?_)
  exact T2 (T1 ds r M G G Gk Hk hG hH (MCong.refl _ G)) s s'

end ContZero
