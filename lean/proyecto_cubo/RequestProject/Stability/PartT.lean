module

public import RequestProject.Stability.PartF

/-!
# `C44_stability_and_rigidity.md`, Part T — Theorem 10.12, first half (`η = 1`)

Namespace `Stability`. Reused (not redefined): C43 `PathSum.R`, `PathSum.XiOp`,
`PathSum.SigOp`; C42 `InvFloors.C109`; C40b `FormalDance.Agree`, `DanceRel`, `finalM`;
C32 `Families.ds`.

* (T1) `T1`, via C43 (R), C42 (C109), (S2), (A1)–(A3) and (F2), with `s := α − 1 ≥ 1`.
* (T2) `T2`, from (T1) and `‖1 + e‖ = 1` for `‖e‖ < 1`.
-/

@[expose] public section

noncomputable section

namespace Stability

open Matrix Finset FormalOps FormalDance

lemma length_ds_pos {l : ℕ} (hl : 1 ≤ l) : 1 ≤ (Families.ds l).length := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Families.ds]
  split_ifs <;> simp

/-- **(T1) Rigidity** (`C44_stability_and_rigidity.md`, Part T; Theorem 10.12, first half, for
`η = 1`): under the hypotheses of C43 (R) with `η = 1` (`l ≥ 1`, `α ≥ 2`, `c ≥ 1`,
`‖ζ m f‖ ≤ 1` for `m ≥ 2`, `B ≥ l + 1`, two-sided inverses `YΞ`, `YSig` of `XiOp α c 1 ζ` and
`SigOp α c 1` in the sense of `Agree`, and the dance relations for `GΞ`, `GSig`):
`IsUnit (finalM GΞ).det`, `IsUnit (finalM GSig).det`, and there is `E'` with
`finalM GΞ = hadOne (finalM GSig) E'` (that is, `M_w(Ξ) = M_w(Σ) ∘ (1 + E')`) and
`‖E' s s'‖ ≤ 2^{−(α−1)}` for all `s, s'`. -/
theorem T1 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (B : ℕ) (hB : l + 1 ≤ B)
    (YΞ YSig : Bf ℚ_[2])
    (hΞY : Agree (PathSum.XiOp α c 1 ζ * YΞ) 1) (hYΞ : Agree (YΞ * PathSum.XiOp α c 1 ζ) 1)
    (hSigY : Agree (PathSum.SigOp α c 1 * YSig) 1) (hYSig : Agree (YSig * PathSum.SigOp α c 1) 1)
    (GΞ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c 1 ζ) GΞ)
    (hGSig : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GSig) :
    IsUnit (finalM GΞ).det ∧ IsUnit (finalM GSig).det ∧
      ∃ E' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
          ℚ_[2],
        finalM GΞ = hadOne (finalM GSig) E' ∧
        ∀ s s', ‖E' s s'‖ ≤ (2 : ℝ) ^ (-(α - 1 : ℤ)) := by
  classical
  have hR := PathSum.R hα hc (η := 1) norm_one hζ l B hB YΞ YSig hΞY hYΞ hSigY hYSig GΞ GSig
    hGΞ hGSig
  have hdetΞ := (InvFloors.C109 l B hB _ YΞ hΞY hYΞ GΞ hGΞ).1
  have hdetSig := (InvFloors.C109 l B hB _ YSig hSigY hYSig GSig hGSig).1
  have hαs : ((α - 1 : ℕ) : ℤ) = (α : ℤ) - 1 := by omega
  -- the relation of the final inverses, entrywise (C43 (R))
  set E : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      ℚ_[2] := Matrix.of fun i j =>
    if h : (finalM GSig)⁻¹ i j = 0 then 0 else Classical.choose ((hR j i).2 h) with hE_def
  have hEeq : (finalM GΞ)⁻¹ = hadOne (finalM GSig)⁻¹ E := by
    ext i j
    simp only [hadOne, of_apply, hE_def]
    split_ifs with h
    · rw [(hR j i).1 h, h, zero_mul]
    · exact (Classical.choose_spec ((hR j i).2 h)).1
  have hEb : ∀ i j, ‖E i j‖ ≤ (2 : ℝ) ^ (-((α - 1 : ℕ) : ℤ)) := by
    intro i j
    simp only [hE_def, of_apply]
    split_ifs with h
    · rw [norm_zero]; positivity
    · rw [hαs]; exact (Classical.choose_spec ((hR j i).2 h)).2
  -- the factorization of `M_w(Σ)` (F2) and the matrix of the word (A1)–(A3)
  have hk := length_ds_pos hl
  obtain ⟨hF, hd1, hd2⟩ := F2 (l := l) (by omega) hc GSig hGSig
  obtain ⟨hA, B0, hB0, hAB⟩ := A3 hk
  obtain ⟨hu1, hu2, E', hE', hE'b⟩ := S2 (S := nest (Families.ds l)) (ν := nuA (Families.ds l))
    nest_refl (fun _ _ _ => nest_trans) nuA_self (fun _ _ _ => nuA_triangle hk)
    (s := α - 1) (by omega) hA (fun _ _ => norm_Amat hk) hB0 hAB hEb
    (fun s => (F2d1 (Families.ds l) α c s : ℚ_[2]))
    (fun s => (F2d2 (Families.ds l) α c s : ℚ_[2]))
    (fun s => by simpa using hd1 s) (fun s => by simpa using hd2 s)
  rw [← hF, ← hEeq] at hE'
  refine ⟨hdetΞ, hdetSig, E', ?_, fun s s' => hαs ▸ hE'b s s'⟩
  rw [← hE', Matrix.nonsing_inv_nonsing_inv _ hdetΞ]

/-- **(T2) Same support, same valuations** (`C44_stability_and_rigidity.md`, Part T): under the
hypotheses of (T1), for all `s, s'`: `finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0`, and
`‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖`. -/
theorem T2 {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (B : ℕ) (hB : l + 1 ≤ B)
    (YΞ YSig : Bf ℚ_[2])
    (hΞY : Agree (PathSum.XiOp α c 1 ζ * YΞ) 1) (hYΞ : Agree (YΞ * PathSum.XiOp α c 1 ζ) 1)
    (hSigY : Agree (PathSum.SigOp α c 1 * YSig) 1) (hYSig : Agree (YSig * PathSum.SigOp α c 1) 1)
    (GΞ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c 1 ζ) GΞ)
    (hGSig : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GSig) :
    ∀ s s', (finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0) ∧
      ‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖ := by
  obtain ⟨-, -, E', hE', hb⟩ := T1 hl hα hc hζ B hB YΞ YSig hΞY hYΞ hSigY hYSig GΞ GSig hGΞ hGSig
  intro s s'
  have hlt : ‖E' s s'‖ < 1 := by
    calc ‖E' s s'‖ ≤ (2 : ℝ) ^ (-(α - 1 : ℤ)) := hb s s'
      _ ≤ (2 : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      _ < 1 := by norm_num
  have h1 : ‖(1 : ℚ_[2]) + E' s s'‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'),
      norm_one, max_eq_left hlt.le]
  have hn : ‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖ := by
    rw [hE']; simp only [hadOne, of_apply, norm_mul, h1, mul_one]
  refine ⟨?_, hn⟩
  rw [← norm_eq_zero, hn, norm_eq_zero]

end Stability
