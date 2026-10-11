module

public import RequestProject.BendCor.PartF

/-!
# `C50e_corollary_10_21.md`: Part W — the congruence

* `toZMod_eq_zero_iff`, `norm_le_half_of_lt_one`, `norm_sub_one_le_half` (auxiliary): the
  reduction `ℤ_[2] → ZMod 2` and the facts "norm `< 1` means norm `≤ 1/2`" and "a unit is `≡ 1`".
* (W1) `W1`: near the identity (lift to `ℤ_[2]`, reduce to `ZMod 2`, where `E ↦ 0`; then
  `(1 - E)⁻¹ - 1 = (1 - E)⁻¹ * E` and the ultrametric inequality).
* (W2) `W2` (Corollary 10.21), (W3) `W3`, (W4) `W4`.
-/

@[expose] public section

noncomputable section

namespace BendCor

open FormalOps FormalDance

/-- Auxiliary for (W1)–(W3) of `C50e_corollary_10_21.md`: `z : ℤ_[2]` reduces to `0` in
`ZMod 2` iff `‖z‖ < 1`. -/
lemma toZMod_eq_zero_iff (z : ℤ_[2]) : PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]

/-- Auxiliary for (W2) of `C50e_corollary_10_21.md`: in `ℤ_[2]`, `‖z‖ < 1` implies
`‖z‖ ≤ 1/2`. -/
lemma norm_le_half_of_lt_one (z : ℤ_[2]) (h : ‖z‖ < 1) : ‖z‖ ≤ 1 / 2 := by
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).1 h
  rw [norm_mul]
  have h2 : ‖((2 : ℕ) : ℤ_[2])‖ = 1 / 2 := by rw [PadicInt.norm_p]; norm_num
  rw [h2]
  nlinarith [PadicInt.norm_le_one w, norm_nonneg w]

/-- Auxiliary for (W2) of `C50e_corollary_10_21.md`: every `u : ℚ_[2]` with `‖u‖ = 1` is odd,
`‖u - 1‖ ≤ 1/2`. -/
lemma norm_sub_one_le_half (u : ℚ_[2]) (hu : ‖u‖ = 1) : ‖u - 1‖ ≤ 1 / 2 := by
  let v : ℤ_[2] := ⟨u, hu.le⟩
  have hv : ‖v‖ = 1 := hu
  have h0 : PadicInt.toZMod v ≠ 0 := by
    rw [Ne, toZMod_eq_zero_iff, hv]; exact lt_irrefl 1
  have h1 : PadicInt.toZMod v = 1 := by
    revert h0; generalize PadicInt.toZMod v = x; revert x; decide
  have h2 : PadicInt.toZMod (v - 1) = 0 := by rw [map_sub, h1, map_one, sub_self]
  rw [toZMod_eq_zero_iff] at h2
  exact norm_le_half_of_lt_one _ h2

/-- **(W1)** of `C50e_corollary_10_21.md` (near the identity): for a `Fintype` `n` with
`DecidableEq` and `E : Matrix n n ℚ_[2]` with `‖E i j‖ ≤ 1/2` for all `i j`:
`‖(1 - E).det‖ = 1`, `‖(1 - E)⁻¹ i j - 1 i j‖ ≤ 1/2` and `‖(1 - E)⁻¹ i j‖ ≤ 1` for all `i j`. -/
theorem W1 {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℚ_[2])
    (hE : ∀ i j, ‖E i j‖ ≤ 1 / 2) :
    ‖(1 - E).det‖ = 1 ∧ (∀ i j, ‖(1 - E)⁻¹ i j - (1 : Matrix n n ℚ_[2]) i j‖ ≤ 1 / 2) ∧
      ∀ i j, ‖(1 - E)⁻¹ i j‖ ≤ 1 := by
  set f := (PadicInt.Coe.ringHom (p := 2) : ℤ_[2] →+* ℚ_[2])
  let E' : Matrix n n ℤ_[2] := fun i j => ⟨E i j, by linarith [hE i j]⟩
  have hE' : f.mapMatrix E' = E := by ext i j; rfl
  have hA : f.mapMatrix (1 - E') = 1 - E := by rw [map_sub, map_one, hE']
  have hz : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).mapMatrix E' = 0 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply]
    rw [toZMod_eq_zero_iff, PadicInt.norm_def]
    exact lt_of_le_of_lt (hE i j) (by norm_num)
  have hdetz : PadicInt.toZMod (1 - E').det = 1 := by
    rw [RingHom.map_det, map_sub, map_one, hz, sub_zero, Matrix.det_one]
  have hdet1 : ‖(1 - E').det‖ = 1 := by
    by_contra hne
    have hlt : ‖(1 - E').det‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) hne
    rw [← toZMod_eq_zero_iff, hdetz] at hlt
    exact one_ne_zero hlt
  have hdetE : (1 - E).det = f (1 - E').det := by rw [RingHom.map_det, hA]
  have hunit : IsUnit (1 - E').det := PadicInt.isUnit_iff.2 hdet1
  have hinv : (1 - E)⁻¹ = f.mapMatrix (1 - E')⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [← hA, ← map_mul, Matrix.nonsing_inv_mul _ hunit, map_one]
  have hle : ∀ i j, ‖(1 - E)⁻¹ i j‖ ≤ 1 := fun i j => by
    rw [hinv]; exact PadicInt.norm_le_one ((1 - E')⁻¹ i j)
  refine ⟨?_, ?_, hle⟩
  · rw [hdetE]; exact hdet1
  · have hunitE : IsUnit (1 - E).det := by rw [hdetE]; exact hunit.map f
    have key : (1 - E)⁻¹ - 1 = (1 - E)⁻¹ * E := by
      have := Matrix.nonsing_inv_mul _ hunitE
      rw [Matrix.mul_sub, Matrix.mul_one] at this
      calc (1 - E)⁻¹ - 1 = (1 - E)⁻¹ - ((1 - E)⁻¹ - (1 - E)⁻¹ * E) := by rw [this]
        _ = (1 - E)⁻¹ * E := by abel
    intro i j
    rw [← Matrix.sub_apply, key, Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) fun k _ => ?_
    rw [norm_mul]
    nlinarith [hle i k, hE k j, norm_nonneg ((1 - E)⁻¹ i k), norm_nonneg (E k j)]

/-- **(W2) Corollary 10.21** of `C50e_corollary_10_21.md`: let `l : ℕ` (any), `B ≥ l + 1`,
`α ≥ 2`, `c ≥ 1`, `η` with `‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, `t` with
`‖t‖ = 1/2`, `Ψ := PathSum.XiOp α c η ζ`, `Y`, `Y_t` two-sided inverses (in the `Agree` sense)
of `Ψ` and `Ψ + t • 1`, and `GΨ`, `GU` as in Part F. With
`W := (t / 2) • (1 - finalM GΨ * Bend.Nmat l B Y_t)⁻¹`: `finalM GU = W * finalM GΨ`,
`‖W s s' - 1 s s'‖ ≤ 1/2`, `‖W s s'‖ ≤ 1` for all `s s'`, and `‖W.det‖ = 1`. -/
theorem W2 {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y Yt : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c η ζ * Y) 1) (h2 : Agree (Y * PathSum.XiOp α c η ζ) 1)
    (h3 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) t) GU) :
    let W := (t / 2) • (1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹
    finalM GU = W * finalM GΨ ∧
      (∀ s s', ‖W s s' - (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2) ∧
      (∀ s s', ‖W s s'‖ ≤ 1) ∧ ‖W.det‖ = 1 := by
  intro W
  have ht0 : t ≠ 0 := by
    intro h; rw [h, norm_zero] at ht; norm_num at ht
  have ht2 : ‖t / 2‖ = 1 := by
    rw [norm_div, ht, PathSum.norm_two_padic]; norm_num
  obtain ⟨-, hF⟩ := F2 hB _ Y Yt ht0 h1 h2 h3 h4 GΨ GU hGΨ hGU
  obtain ⟨hd, hsub, hle⟩ := W1 _ (Bend.B1 hB hα hc hη hζ ht Yt h3 h4 GΨ hGΨ)
  have hu := norm_sub_one_le_half _ ht2
  refine ⟨hF, fun s s' => ?_, fun s s' => ?_, ?_⟩
  · have : W s s' - (1 : Matrix _ _ ℚ_[2]) s s' =
        t / 2 * ((1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹ s s' - (1 : Matrix _ _ ℚ_[2]) s s') +
          (t / 2 - 1) * (1 : Matrix _ _ ℚ_[2]) s s' := by
      simp only [W, Matrix.smul_apply, smul_eq_mul]; ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, ht2, one_mul]; exact hsub s s'
    · rw [norm_mul]
      have h1n : ‖(1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
          (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 := by
        rw [Matrix.one_apply]; split_ifs <;> simp
      nlinarith [norm_nonneg (t / 2 - 1)]
  · simp only [W, Matrix.smul_apply, smul_eq_mul, norm_mul, ht2, one_mul]
    exact hle s s'
  · simp only [W, Matrix.det_smul, norm_mul, norm_pow, ht2, one_pow, one_mul,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, hd, inv_one]

/-- **(W3)** of `C50e_corollary_10_21.md` (the integral form): in the setting of (W2), there is
`W' : Matrix (Fin ns) (Fin ns) ℤ_[2]` with `W'.map (fun z : ℤ_[2] => (z : ℚ_[2])) = W`,
`IsUnit W'.det`, and `‖((W' s s' : ℤ_[2]) : ℚ_[2]) - 1 s s'‖ ≤ 1/2` for all `s s'`. -/
theorem W3 {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y Yt : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c η ζ * Y) 1) (h2 : Agree (Y * PathSum.XiOp α c η ζ) 1)
    (h3 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) t) GU) :
    let W := (t / 2) • (1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      W'.map (fun z : ℤ_[2] => (z : ℚ_[2])) = W ∧ IsUnit W'.det ∧
        ∀ s s', ‖((W' s s' : ℤ_[2]) : ℚ_[2]) - (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
          (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2 := by
  intro W
  obtain ⟨-, hsub, hle, hdet⟩ := W2 hB hα hc hη hζ ht Y Yt h1 h2 h3 h4 GΨ GU hGΨ hGU
  let W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      ℤ_[2] := fun s s' => ⟨W s s', hle s s'⟩
  have hW' : W'.map (fun z : ℤ_[2] => (z : ℚ_[2])) = W := by ext s s'; rfl
  refine ⟨W', hW', ?_, fun s s' => hsub s s'⟩
  rw [PadicInt.isUnit_iff]
  have : ((W'.det : ℤ_[2]) : ℚ_[2]) = W.det := by
    rw [← hW']
    exact (PadicInt.Coe.ringHom (p := 2)).map_det W'
  rw [PadicInt.norm_def, this, hdet]

/-- **(W4)** of `C50e_corollary_10_21.md` (both signs, as in the paper): in the setting of (W2)
without `t`, let `Y₊`, `Y₋` be two-sided inverses of `Ψ + 2 • 1` and `Ψ + (-2) • 1`, and let
`GU₊`, `GU₋` satisfy `DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ 2) GU₊` and
`DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ (-2)) GU₋`. With
`W₊ := (1 - finalM GΨ * Bend.Nmat l B Y₊)⁻¹` and `W₋ := -(1 - finalM GΨ * Bend.Nmat l B Y₋)⁻¹`:
`finalM GU₊ = W₊ * finalM GΨ`, `finalM GU₋ = W₋ * finalM GΨ`, `‖W₊ s s' - 1 s s'‖ ≤ 1/2` and
`‖W₋ s s' + 1 s s'‖ ≤ 1/2` for all `s s'`. -/
theorem W4 {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    (Y Yp Ym : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c η ζ * Y) 1) (h2 : Agree (Y * PathSum.XiOp α c η ζ) 1)
    (hp1 : Agree ((PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Yp) 1)
    (hp2 : Agree (Yp * (PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (hm1 : Agree ((PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Ym) 1)
    (hm2 : Agree (Ym * (PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (GΨ GUp GUm : Matrix (Fin (Dance.slots (Families.ds l) 1))
      (Fin (Dance.slots (Families.ds l) 1)) (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΨ)
    (hGUp : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) 2) GUp)
    (hGUm : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) (-2)) GUm) :
    let Wp := (1 - finalM GΨ * Bend.Nmat l B Yp)⁻¹
    let Wm := -(1 - finalM GΨ * Bend.Nmat l B Ym)⁻¹
    finalM GUp = Wp * finalM GΨ ∧ finalM GUm = Wm * finalM GΨ ∧
      (∀ s s', ‖Wp s s' - (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2) ∧
      ∀ s s', ‖Wm s s' + (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2 := by
  intro Wp Wm
  have n2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := PathSum.norm_two_padic
  have nm2 : ‖(-2 : ℚ_[2])‖ = 1 / 2 := by rw [norm_neg, PathSum.norm_two_padic]
  obtain ⟨hFp, hsubp, -, -⟩ := W2 hB hα hc hη hζ n2 Y Yp h1 h2 hp1 hp2 GΨ GUp hGΨ hGUp
  obtain ⟨hFm, -, -, -⟩ := W2 hB hα hc hη hζ nm2 Y Ym h1 h2 hm1 hm2 GΨ GUm hGΨ hGUm
  obtain ⟨-, hsubm, -⟩ := W1 _ (Bend.B1 hB hα hc hη hζ nm2 Ym hm1 hm2 GΨ hGΨ)
  have e2 : (2 : ℚ_[2]) / 2 = 1 := by norm_num
  have em2 : (-2 : ℚ_[2]) / 2 = -1 := by norm_num
  simp only [e2, one_smul] at hFp hsubp
  simp only [em2, neg_one_smul] at hFm
  refine ⟨hFp, hFm, hsubp, fun s s' => ?_⟩
  have : Wm s s' + (1 : Matrix _ _ ℚ_[2]) s s' =
      -((1 - finalM GΨ * Bend.Nmat l B Ym)⁻¹ s s' - (1 : Matrix _ _ ℚ_[2]) s s') := by
    simp only [Wm, Matrix.neg_apply]; ring
  rw [this, norm_neg]
  exact hsubm s s'

end BendCor
