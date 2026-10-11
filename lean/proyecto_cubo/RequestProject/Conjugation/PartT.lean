module

public import RequestProject.Conjugation.PartC4
public import RequestProject.Conjugation.PartD
public import RequestProject.Conjugation.PartX
public import RequestProject.Stability.All

/-!
# `C45_conjugation_and_general_eta.md`: Part T — Theorem 10.12, first half, for every unit `η`

Reused (not redefined): C44 `Stability.hadOne`, `Stability.nest`, `Stability.T1`, `Stability.T2`,
`Stability.F1`, `Stability.sigOp_magree_paySys`; C40b `L4_sigma`, `DanceRel`, `finalM`;
C43 `PathSum.XiOp`, `PathSum.SigOp`, `PathSum.piF`; C10 `Deficit.Mc`; C14 `Windows.Dset`,
`Windows.Ids`; C3 `Rulers.oE`; C32 `Families.ds`.

* `T_eta`: the three statements (T1η), (T2η), (F1η) for one `GSig`;
* `T1eta`, `T2eta`, `F1eta`: each separately, in the form of the file;
* `F1eta_gen`: (F1η) for every `GSig`, every digit list, under `α ≥ 1` and `η ≠ 0` only.
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset Matrix

lemma piF_ne_zero {α c : ℕ} (hc : 1 ≤ c) {f : ℤ} (hf : 0 ≤ f) : PathSum.piF α c f ≠ 0 := by
  unfold PathSum.piF
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) ?_
  have h : ((f + c : ℤ) : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  push_cast at h
  exact h

/-- A clean dance of `SigOp α c 1` exists (C40b (L4) and (D0)). -/
lemma sig_one_dance (ds : List Bool) {α : ℕ} (hα : 1 ≤ α) (c : ℕ) :
    ∃ G : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]),
      DanceRel ds 1 (fun _ _ => PathSum.SigOp α c 1) G :=
  ⟨_, D0 ds 1 _ _ _ (L4_sigma (A := ℚ_[2]) ds α c).1 (Stability.sigOp_magree_paySys hα c).symm⟩

lemma scale_zpow {η : ℚ_[2]} (hη : η ≠ 0) (a b k : ℕ) :
    η ^ a * η⁻¹ ^ b * η⁻¹ ^ (2 ^ k - 1) = η ^ ((a : ℤ) - b - (2 ^ k - 1)) := by
  have h : ((2 : ℤ) ^ k - 1) = ((2 ^ k - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [h, zpow_sub₀ hη, zpow_sub₀ hη, zpow_natCast, zpow_natCast, zpow_natCast]
  simp [div_eq_mul_inv, inv_pow]

/-- **Part T** of `C45_conjugation_and_general_eta.md` (Theorem 10.12, first half, for every
unit `η`): let `l ≥ 1`, `α ≥ 2`, `c ≥ 1`, `η : ℚ_[2]` with `‖η‖ = 1`, `ζ` with `‖ζ j f‖ ≤ 1` for
`j ≥ 2`, and `GΞ` with `DanceRel (Families.ds l) 1 (fun _ _ => XiOp α c η ζ) GΞ`. Then there is
`GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GSig` such that
* (T1η) `IsUnit (finalM GΞ).det`, `IsUnit (finalM GSig).det`, and there is `E'` with
  `finalM GΞ = hadOne (finalM GSig) E'` and `‖E' s s'‖ ≤ 2^{−(α−1)}`;
* (T2η) `finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0` and `‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖`;
* (F1η) `finalM GSig s s' = η ^ (o(D_s) − o(D_{s'}) − (K − 1)) · Mc(D_s, D_{s'})` on nested
  pairs (`Stability.nest`, i.e. `D_{s'} ⊆ D_s`) and `0` otherwise (`K = 2^k`,
  `k = (Families.ds l).length`, `D_s = Windows.Dset (Families.ds l) s`, `o = Rulers.oE`,
  `Mc = Deficit.Mc (Windows.Ids ds) k α c` cast from `ℚ`).
All hypotheses are used. -/
theorem T_eta {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∃ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        (Bf ℚ_[2]),
      DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c η) GSig ∧
      (IsUnit (finalM GΞ).det ∧ IsUnit (finalM GSig).det ∧
        ∃ E' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
            ℚ_[2],
          finalM GΞ = Stability.hadOne (finalM GSig) E' ∧
          ∀ s s', ‖E' s s'‖ ≤ (2 : ℝ) ^ (-(α - 1 : ℤ))) ∧
      (∀ s s', (finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0) ∧
        ‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖) ∧
      (∀ s s', finalM GSig s s' = if Stability.nest (Families.ds l) s s' then
        η ^ ((Rulers.oE (Windows.Dset (Families.ds l) s) : ℤ) -
          Rulers.oE (Windows.Dset (Families.ds l) s') - (2 ^ (Families.ds l).length - 1)) *
        ((Deficit.Mc (Windows.Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
          (Windows.Dset (Families.ds l) s) (Windows.Dset (Families.ds l) s') : ℚ) : ℚ_[2])
        else 0) := by
  have hη0 : η ≠ 0 := by rintro rfl; simp at hη
  set U : ℚ_[2]ˣ := Units.mk0 η hη0
  have hUv : (U : ℚ_[2]) = η := rfl
  have hUi : ((U⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) = η⁻¹ := by rw [Units.val_inv_eq_inv_val, hUv]
  set ζ' : ℕ → ℤ → ℚ_[2] := fun j f => η⁻¹ ^ j * ζ j f
  have hζ'b : ∀ j, 2 ≤ j → ∀ f, ‖ζ' j f‖ ≤ 1 := X2 hη hζ
  -- the dance of `Ξ' = XiOp α c 1 ζ'`
  rw [X1_xi α c hη0 ζ] at hGΞ
  obtain ⟨G1, hG1, hfin1⟩ := C5_one U⁻¹ _ hGΞ
  rw [hUi, cj_cj, inv_mul_cancel₀ hη0, cj_one_left] at hG1
  simp only [hUi, inv_inv, hUv] at hfin1
  -- the dance of `Σ' = SigOp α c 1` and of `Σ = SigOp α c η`
  obtain ⟨G2, hG2⟩ := sig_one_dance (Families.ds l) (α := α) (by omega) c
  obtain ⟨GSig, hGSig, hfin2⟩ := C5_one U _ hG2
  rw [hUv, ← X1_sig] at hGSig
  simp only [hUv, hUi] at hfin2
  -- the scaling factor
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin (Dance.slots (Families.ds l) 1) →
      Fin (Dance.slots (Families.ds l) 1) → ℚ_[2], lam = fun (s s' : Fin (Dance.slots (Families.ds l) 1)) =>
    η ^ Rulers.oE (Windows.Dset (Families.ds l) s) * η⁻¹ ^ Rulers.oE (Windows.Dset (Families.ds l) s') *
      η⁻¹ ^ (2 ^ (Families.ds l).length - 1) := ⟨_, rfl⟩
  have hΞ : ∀ s s', finalM GΞ s s' = lam s s' * finalM G1 s s' := by
    intro s s'
    rw [hfin1, ← mul_assoc]
    have : lam s s' * (η⁻¹ ^ Rulers.oE (Windows.Dset (Families.ds l) s) * η ^ Rulers.oE (Windows.Dset (Families.ds l) s') *
        η ^ (2 ^ (Families.ds l).length - 1)) = 1 := by
      simp only [hlam, inv_pow]
      field_simp
    rw [this, one_mul]
  have hnorm : ∀ s s', ‖lam s s'‖ = 1 := by
    intro s s'; simp [hlam, hη]
  have hfin2' : ∀ s s', finalM GSig s s' = lam s s' * finalM G2 s s' := by
    rw [hlam]; exact hfin2
  -- inverses (I)
  have hx0 : ∀ ζ0 : ℕ → ℤ → ℚ_[2], ∀ f : ℤ, 0 ≤ f → (PathSum.XiOp α c 1 ζ0).coef 0 f ≠ 0 :=
    fun ζ0 f hf => by rw [PathSum.XiOp_coef_zero]; exact piF_ne_zero hc hf
  obtain ⟨YΞ, hΞY, hYΞ⟩ := I _ (hx0 ζ')
  obtain ⟨YSig, hSigY, hYSig⟩ := I _ (hx0 (fun _ _ => 0))
  obtain ⟨hu1, hu2, E', hE', hEb⟩ := Stability.T1 hl hα hc hζ'b (l + 1) le_rfl YΞ YSig hΞY hYΞ
    hSigY hYSig G1 G2 hG1 hG2
  have hT2 := Stability.T2 hl hα hc hζ'b (l + 1) le_rfl YΞ YSig hΞY hYΞ hSigY hYSig G1 G2 hG1 hG2
  -- diagonal factorization
  set a : Fin (Dance.slots (Families.ds l) 1) → ℚ_[2] := fun s =>
    η ^ Rulers.oE (Windows.Dset (Families.ds l) s) * η⁻¹ ^ (2 ^ (Families.ds l).length - 1)
  set b : Fin (Dance.slots (Families.ds l) 1) → ℚ_[2] := fun s => η⁻¹ ^ Rulers.oE (Windows.Dset (Families.ds l) s)
  have hdiag : ∀ M N : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2],
      (∀ s s', M s s' = lam s s' * N s s') → M = diagonal a * N * diagonal b := by
    intro M N h
    ext s s'
    rw [h, mul_diagonal, diagonal_mul]
    simp only [hlam, a, b]
    ring
  have hab : IsUnit (∏ s, a s) ∧ IsUnit (∏ s, b s) := by
    constructor <;> refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun s _ => ?_) <;>
      simp [a, b, hη0]
  refine ⟨GSig, hGSig, ⟨?_, ?_, E', ?_, hEb⟩, ?_, ?_⟩
  · rw [hdiag _ _ hΞ, det_mul, det_mul, det_diagonal, det_diagonal]
    exact (hab.1.mul hu1).mul hab.2
  · rw [hdiag _ _ hfin2', det_mul, det_mul, det_diagonal, det_diagonal]
    exact (hab.1.mul hu2).mul hab.2
  · ext s s'
    have h1 := congrFun (congrFun hE' s) s'
    simp only [Stability.hadOne, of_apply] at h1 ⊢
    rw [hΞ, h1, hfin2']
    ring
  · intro s s'
    have hn : ‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖ := by
      rw [hΞ, hfin2', norm_mul, norm_mul, hnorm, (hT2 s s').2]
    refine ⟨?_, hn⟩
    rw [← norm_eq_zero, hn, norm_eq_zero]
  · intro s s'
    rw [hfin2, Stability.F1 (by omega) G2 hG2 s s']
    split_ifs
    · rw [scale_zpow hη0]
    · rw [mul_zero]

/-- **(T1η)** of `C45_conjugation_and_general_eta.md` (Part T): under the hypotheses of Part T
there is `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GSig` such that
`IsUnit (finalM GΞ).det`, `IsUnit (finalM GSig).det`, and there is `E'` with
`finalM GΞ = Stability.hadOne (finalM GSig) E'` and `‖E' s s'‖ ≤ 2^{−(α−1)}` for all `s, s'`.
All hypotheses are used. -/
theorem T1eta {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∃ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        (Bf ℚ_[2]),
      DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c η) GSig ∧
      IsUnit (finalM GΞ).det ∧ IsUnit (finalM GSig).det ∧
        ∃ E' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
            ℚ_[2],
          finalM GΞ = Stability.hadOne (finalM GSig) E' ∧
          ∀ s s', ‖E' s s'‖ ≤ (2 : ℝ) ^ (-(α - 1 : ℤ)) := by
  obtain ⟨GSig, h, h1, -, -⟩ := T_eta hl hα hc hη hζ GΞ hGΞ
  exact ⟨GSig, h, h1⟩

/-- **(T2η)** of `C45_conjugation_and_general_eta.md` (Part T): under the hypotheses of Part T
there is `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GSig` such that for all
`s, s'`: `finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0` and
`‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖`. All hypotheses are used. -/
theorem T2eta {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∃ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        (Bf ℚ_[2]),
      DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c η) GSig ∧
      ∀ s s', (finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0) ∧
        ‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖ := by
  obtain ⟨GSig, h, -, h2, -⟩ := T_eta hl hα hc hη hζ GΞ hGΞ
  exact ⟨GSig, h, h2⟩

/-- **(F1η)** of `C45_conjugation_and_general_eta.md` (Part T): under the hypotheses of Part T
there is `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GSig` such that for all
`s, s'`: `finalM GSig s s' = η ^ (o(D_s) − o(D_{s'}) − (K − 1)) · Mc(D_s, D_{s'})` if
`D_{s'} ⊆ D_s` (`Stability.nest`) and `0` otherwise. (Stated with all the hypotheses of Part T;
`F1eta_gen` proves the same conclusion for every `GSig` under `α ≥ 1`, `η ≠ 0` only.) -/
theorem F1eta {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∃ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        (Bf ℚ_[2]),
      DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c η) GSig ∧
      ∀ s s', finalM GSig s s' = if Stability.nest (Families.ds l) s s' then
        η ^ ((Rulers.oE (Windows.Dset (Families.ds l) s) : ℤ) -
          Rulers.oE (Windows.Dset (Families.ds l) s') - (2 ^ (Families.ds l).length - 1)) *
        ((Deficit.Mc (Windows.Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
          (Windows.Dset (Families.ds l) s) (Windows.Dset (Families.ds l) s') : ℚ) : ℚ_[2])
        else 0 := by
  obtain ⟨GSig, h, -, -, h3⟩ := T_eta hl hα hc hη hζ GΞ hGΞ
  exact ⟨GSig, h, h3⟩

/-- (F1η) of `C45_conjugation_and_general_eta.md`, more general form: for every digit list `ds`,
`α ≥ 1`, `η ≠ 0` and every `GSig` with `DanceRel ds 1 (fun _ _ => SigOp α c η) GSig`,
`finalM GSig s s' = η ^ (o(D_s) − o(D_{s'}) − (K − 1)) · Mc(D_s, D_{s'})` on nested pairs and
`0` otherwise (`K = 2 ^ ds.length`). -/
theorem F1eta_gen (ds : List Bool) {α : ℕ} (hα : 1 ≤ α) (c : ℕ) {η : ℚ_[2]} (hη : η ≠ 0)
    (GSig : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]))
    (hG : DanceRel ds 1 (fun _ _ => PathSum.SigOp α c η) GSig) (s s' : Fin (Dance.slots ds 1)) :
    finalM GSig s s' = if Stability.nest ds s s' then
      η ^ ((Rulers.oE (Windows.Dset ds s) : ℤ) - Rulers.oE (Windows.Dset ds s') -
        (2 ^ ds.length - 1)) *
      ((Deficit.Mc (Windows.Ids ds) ds.length (α : ℤ) c (Windows.Dset ds s)
        (Windows.Dset ds s') : ℚ) : ℚ_[2])
      else 0 := by
  have h2 : ∀ a : ℚ_[2], 2 * a = 0 → a = 0 := fun a h => by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h two_ne_zero
    · exact h
  obtain ⟨G2, hG2⟩ := sig_one_dance ds hα c
  obtain ⟨G3, hG3, hfin⟩ := C5_one (Units.mk0 η hη) _ hG2
  rw [Units.val_mk0, ← X1_sig] at hG3
  have hUi : (((Units.mk0 η hη)⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) = η⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
  rw [(L5 h2 hG hG3).2, hfin, Stability.F1_gen ds hα c G2 hG2 s s', hUi, Units.val_mk0]
  split_ifs
  · rw [scale_zpow hη]
  · rw [mul_zero]

end Conjugation
