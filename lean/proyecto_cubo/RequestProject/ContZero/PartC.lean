module

public import RequestProject.ContZero.PartT
public import RequestProject.Smith2.All

/-!
# `C49b_congruence_and_the_data_at_zero.md`: Part C — the shift `c` moves the systems by
# multiples of `2^{α+N}`

* (C1) `C1`: the two series differ only in the coefficient `m = 0`; witness
  `Bf.dg (fun _ => −t)`.
* (C2) `C2`: only the diagonal entries differ; witness `Bf.dg (ext0 (fun _ => −t))`.
* (C3) `C3`: C40b (L4) `L4_sigma` at `c` and `c'`, (C2), (T1), (T2), and C14's
  `finalMatrix_eq_map`; divisibility in `ℤ` from the norm (`PadicInt.norm_int_le_pow_iff_dvd`).
-/

@[expose] public section

noncomputable section

namespace ContZero

open FormalOps FormalDance

/-- Proof of Part C of `C49b_congruence_and_the_data_at_zero.md`: the hypothesis
`(2 : ℤ) ^ N ∣ c' − c`, read in `ℤ_[2]`. -/
lemma cast_sub_eq {c c' N : ℕ} {t : ℤ} (ht : (c' : ℤ) - c = 2 ^ N * t) :
    ((c' : ℤ_[2]) - c) = 2 ^ N * t := by
  have := congrArg (Int.cast : ℤ → ℤ_[2]) ht
  push_cast at this
  exact this

/-- **(C1)** of `C49b_congruence_and_the_data_at_zero.md`: for `α c c' N : ℕ` with
`(2 : ℤ) ^ N ∣ (c' : ℤ) - c`, every `η : ℤ_[2]` and every `ζ : ℕ → ℤ → ℤ_[2]`:
`Cong (α + N) (Smith2.XiOpZ α c η ζ) (Smith2.XiOpZ α c' η ζ)`. -/
theorem C1 (α c c' N : ℕ) (hN : (2 : ℤ) ^ N ∣ (c' : ℤ) - c) (η : ℤ_[2])
    (ζ : ℕ → ℤ → ℤ_[2]) :
    Cong (α + N) (Smith2.XiOpZ α c η ζ) (Smith2.XiOpZ α c' η ζ) := by
  obtain ⟨t, ht⟩ := hN
  have hc := cast_sub_eq ht
  refine ⟨Bf.dg (fun _ => -(t : ℤ_[2])), Agree.of_eq ?_⟩
  ext m f
  simp only [Bf.coef_sub, Bf.coef_smul, Bf.coef_dg, Smith2.XiOpZ]
  split_ifs
  · linear_combination (-(2 : ℤ_[2]) ^ α) * hc
  · simp
  · simp

/-- **(C2)** of `C49b_congruence_and_the_data_at_zero.md`: for `α c c' N : ℕ` with
`(2 : ℤ) ^ N ∣ (c' : ℤ) - c` and `1 ≤ α`:
`MCong (α + N) (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ)
(paySys (Dance.pσ (A := ℤ_[2]) α c') Dance.κσ)`. -/
theorem C2 (α c c' N : ℕ) (hN : (2 : ℤ) ^ N ∣ (c' : ℤ) - c) (hα : 1 ≤ α) :
    MCong (α + N) (paySys (Dance.pσ (A := ℤ_[2]) α c) Dance.κσ)
      (paySys (Dance.pσ (A := ℤ_[2]) α c') Dance.κσ) := by
  obtain ⟨t, ht⟩ := hN
  have hc := cast_sub_eq ht
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 1 := ⟨α - 1, by omega⟩
  refine ⟨fun _ _ => Bf.dg (ext0 (fun _ => -(t : ℤ_[2]))), fun s s' => Agree.of_eq ?_⟩
  have hss : s = s' := Subsingleton.elim _ _
  subst hss
  ext m f
  simp only [Matrix.sub_apply, Matrix.smul_apply, paySys, ↓reduceIte]
  rw [Bf.coef_sub, Bf.coef_add, Bf.coef_add]
  simp only [Bf.coef_smul, Bf.coef_dg, Bf.coef_fd, ext0, Dance.pσ, Nat.add_sub_cancel]
  split_ifs
  all_goals first | linear_combination (-(2 : ℤ_[2]) ^ (a + 1)) * hc | simp

/-- Proof of (C3) of `C49b_congruence_and_the_data_at_zero.md`: the entries of the final matrix
of the dance of `paySys (pσ α i) κσ` over `ℤ_[2]` are the integers
`Windows.finalMatrix ℤ ds α i s s'`. -/
lemma mfin_eq_finalMatrix (ds : List Bool) (α i : ℕ) (s s' : Fin (2 ^ Dance.mCount ds)) :
    Dance.Mfin (Dance.dance ds 1 (Dance.pσ (A := ℤ_[2]) α i) Dance.κσ).1
        (Dance.dance ds 1 (Dance.pσ α i) Dance.κσ).2
        (Fin.cast (one_mul (2 ^ Dance.mCount ds)).symm s)
        (Fin.cast (one_mul (2 ^ Dance.mCount ds)).symm s') =
      ((Windows.finalMatrix ℤ ds α i s s' : ℤ) : ℤ_[2]) := by
  have h : Windows.finalMatrix ℤ_[2] ds α i s s' = _ :=
    congrFun (congrFun (Windows.finalMatrix_eq_map ℤ_[2] ds α i) s) s'
  exact h

/-- Proof of (C3) of `C49b_congruence_and_the_data_at_zero.md`: for an integer `n`, `2 ^ M`
divides `n` as soon as it does in `ℤ_[2]`. -/
lemma int_dvd_of_eq_pow_mul {n : ℤ} {M : ℕ} {w : ℤ_[2]} (h : (n : ℤ_[2]) = 2 ^ M * w) :
    (2 : ℤ) ^ M ∣ n := by
  have h1 := norm_le_of_eq_pow_mul h
  have h2 : ‖(n : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact h1
  have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2)).1 (by exact_mod_cast h2)
  exact_mod_cast this

/-- **(C3)** of `C49b_congruence_and_the_data_at_zero.md` (the integer final matrices): for
`1 ≤ α`, every `ds : List Bool`, `c c' N M : ℕ` with `(2 : ℤ) ^ N ∣ (c' : ℤ) - c` and
`M + ds.length = α + N`: for all `s s'`,
`(2 : ℤ) ^ M ∣ Windows.finalMatrix ℤ ds α c s s' - Windows.finalMatrix ℤ ds α c' s s'`. -/
theorem C3 {α : ℕ} (hα : 1 ≤ α) (ds : List Bool) (c c' N M : ℕ)
    (hN : (2 : ℤ) ^ N ∣ (c' : ℤ) - c) (hM : M + ds.length = α + N)
    (s s' : Fin (2 ^ Dance.mCount ds)) :
    (2 : ℤ) ^ M ∣ Windows.finalMatrix ℤ ds α c s s' - Windows.finalMatrix ℤ ds α c' s s' := by
  obtain ⟨hd, hf⟩ := L4_sigma (A := ℤ_[2]) ds α c
  obtain ⟨hd', hf'⟩ := L4_sigma (A := ℤ_[2]) ds α c'
  have hcong := C2 α c c' N hN hα
  rw [← hM] at hcong
  obtain ⟨w, hw⟩ := T2 (T1 ds 1 M _ _ _ _ hd hd' hcong)
    (Fin.cast (Dance.slots_eq ds 1).symm (Fin.cast (one_mul (2 ^ Dance.mCount ds)).symm s))
    (Fin.cast (Dance.slots_eq ds 1).symm (Fin.cast (one_mul (2 ^ Dance.mCount ds)).symm s'))
  rw [hf, hf', mfin_eq_finalMatrix, mfin_eq_finalMatrix, ← Int.cast_sub] at hw
  exact int_dvd_of_eq_pow_mul hw

end ContZero
