module

public import RequestProject.Cleanliness.Inverse

/-!
# `C48_cleanliness_one_move.md`: Part W — the twist move

Namespace `Cleanliness`. (W1)–(W5) of the file, for `P : Finset ℕ`, `h : ℕ`, `c : ℤ_[2]`.
The equalities of (W1) and (W3) are equalities in `Matrix (Dn P) (Dn P) (Bf ℤ_[2])` (resp. of
functions), not only agreement.
-/

@[expose] public section

noncomputable section

namespace Cleanliness

open RingK FormalOps FormalDance Doubling Finset

/-! ### (W1) -/

/-- Helper for (W1) of `C48_cleanliness_one_move.md`: `dfi 1 = 1`. -/
lemma dfi_one : dfi (A := ℤ_[2]) 1 = 1 := by simp [dfi]

/-- Helper for (W1) of `C48_cleanliness_one_move.md`: the position of the even floor `2f`. -/
lemma pos_even (h : ℕ) (f : ℤ) :
    (2 : ℤ_[2]) ^ h * ((2 * f : ℤ) : ℤ_[2]) = 2 ^ (h + 1) * (f : ℤ_[2]) := by
  push_cast; ring

/-- Helper for (W1) of `C48_cleanliness_one_move.md`: the position of the odd floor `2f + 1`. -/
lemma pos_odd (h : ℕ) (f : ℤ) (o c : ℤ_[2]) :
    (2 : ℤ_[2]) ^ h * ((2 * f + 1 : ℤ) : ℤ_[2]) + o + c =
      2 ^ (h + 1) * (f : ℤ_[2]) + o + c + 2 ^ h := by
  push_cast; ring

/-- **(W1)** of `C48_cleanliness_one_move.md`, block `B`:
`twB (covSys P h c Γ) = covSys P (h + 1) c (GB Γ)`. -/
theorem W1_B (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    twB (covSys P h c Γ) = covSys P (h + 1) c (GB Γ) := by
  funext D D'
  ext q f
  simp only [twB, coef_tw00, covSys_coef, GB, pos_even]
  split_ifs <;> simp

/-- **(W1)** of `C48_cleanliness_one_move.md`, block `C`:
`twC (covSys P h c Γ) = covSys P (h + 1) c (GC h Γ)`. -/
theorem W1_C (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    twC (covSys P h c Γ) = covSys P (h + 1) c (GC h Γ) := by
  funext D D'
  ext q f
  simp only [twC, coef_tw11, covSys_coef, GC, pos_odd]
  split_ifs <;> simp

/-- **(W1)** of `C48_cleanliness_one_move.md`, block `P`:
`twP (covSys P h c Γ) = covSys P (h + 1) c (GP h Γ)`. -/
theorem W1_P (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    twP (covSys P h c Γ) = covSys P (h + 1) c (GP h Γ) := by
  funext D D'
  ext q f
  simp only [twP, coef_tw10, covSys_coef, GP, pos_odd]
  split_ifs <;> simp

/-- **(W1)** of `C48_cleanliness_one_move.md`, block `D`:
`twD (covSys P h c Γ) = covSys P (h + 1) c (GD Γ)`. -/
theorem W1_D (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    twD (covSys P h c Γ) = covSys P (h + 1) c (GD Γ) := by
  funext D D'
  ext q f
  cases q with
  | zero => simp [twD, covSys_coef, GD]
  | succ q =>
    simp only [twD, coef_tw01_succ, covSys_coef, GD, pos_even]
    split_ifs <;> simp

/-- **(W1)** of `C48_cleanliness_one_move.md` (the blocks are covariant, one level up), all four
equalities in `Matrix (Dn P) (Dn P) (Bf ℤ_[2])`. -/
theorem W1 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    twB (covSys P h c Γ) = covSys P (h + 1) c (GB Γ) ∧
    twC (covSys P h c Γ) = covSys P (h + 1) c (GC h Γ) ∧
    twP (covSys P h c Γ) = covSys P (h + 1) c (GP h Γ) ∧
    twD (covSys P h c Γ) = covSys P (h + 1) c (GD Γ) :=
  ⟨W1_B P h c Γ, W1_C P h c Γ, W1_P P h c Γ, W1_D P h c Γ⟩

/-! ### (W2) -/

/-- Helper for (W2) of `C48_cleanliness_one_move.md`: `y ↦ ϑ (y + e)` is in `Kr` with `ϑ`. -/
lemma Kr_shift_add {ϑ : ℤ_[2] → ℤ_[2]} (hϑ : ϑ ∈ Kr) (e : ℤ_[2]) : (fun y => ϑ (y + e)) ∈ Kr := by
  have := K4 hϑ (-e)
  simpa [sub_neg_eq_add] using this

/-- **(W2)** of `C48_cleanliness_one_move.md` (the blocks stay in the class): if `InK Γ` then
`InK (GB Γ)`, `InK (GC h Γ)`, `InK (GP h Γ)`, `InK (GD Γ)`; moreover
`thetaSys (GB Γ) = thetaSys (GC h Γ)` and `thetaSys (GD Γ) = 0`. -/
theorem W2 (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hK : InK Γ) :
    InK (GB Γ) ∧ InK (GC h Γ) ∧ InK (GP h Γ) ∧ InK (GD Γ) ∧
      thetaSys (GB Γ) = thetaSys (GC h Γ) ∧ thetaSys (GD Γ) = 0 := by
  have hD : ∀ Δ q, GD Γ Δ q = (fun y => match q with
      | 0 => (0 : ℤ_[2])
      | q + 1 => ((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1) * Γ Δ (2 * q + 1) y) := by
    intro Δ q; funext y; cases q <;> rfl
  refine ⟨fun Δ q => K3_smul _ (hK _ _), fun Δ q => K3_smul _ (Kr_shift_add (hK _ _) _),
    fun Δ q => K3_smul _ (Kr_shift_add (hK _ _) _), fun Δ q => ?_, ?_, ?_⟩
  · rw [hD]
    cases q with
    | zero => exact K3_const 0
    | succ q =>
      simpa only [mul_assoc] using K3_smul (((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1)) (hK Δ (2 * q + 1))
  · refine RS.ext fun Δ q => ?_
    simp only [thetaSys_apply]
    have := S2 (K3_smul (dfi q) (hK Δ (2 * q))) (-(2 : ℤ_[2]) ^ h)
    simp only [sub_neg_eq_add] at this
    exact this.symm
  · refine RS.ext fun Δ q => ?_
    rw [thetaSys_apply, hD, RS.zero_apply]
    cases q with
    | zero => simpa using S1_const 0
    | succ q =>
      simp only
      have := S1_smul (((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1)) (hK Δ (2 * q + 1))
      simp only [mul_assoc] at this ⊢
      rw [this]
      have h2 : red (((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1)) = 0 := by
        rw [map_mul, show ((2 * q + 2 : ℕ) : ℤ_[2]) = 2 * ((q + 1 : ℕ) : ℤ_[2]) by push_cast; ring,
          map_mul, red_two, zero_mul, zero_mul]
      rw [h2]
      simp

/-! ### (W3) -/

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: `GP h Γ ∅ 0 y = Γ ∅ 1 (y + 2^h)`. -/
lemma GP_empty_zero (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (y : ℤ_[2]) :
    GP h Γ ∅ 0 y = Γ ∅ 1 (y + 2 ^ h) := by
  simp [GP]

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: inverses of unit-valued elements of `Kr`
are in `Kr` ((K6) and (K5)). -/
lemma Kr_inverse {ϑ : ℤ_[2] → ℤ_[2]} (hϑ : ϑ ∈ Kr) (hu : ∀ y, IsUnit (ϑ y)) :
    (fun y => Ring.inverse (ϑ y)) ∈ Kr := by
  obtain ⟨r, rfl⟩ := hϑ
  exact (K5 r ((K6 r 0).2.1 (hu 0))).2

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the value of the right inverse at
`(∅, 0)`. -/
lemma rinv_empty_zero (k : ℕ) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (y : ℤ_[2]) :
    rinv k G ∅ 0 y = Ring.inverse (G ∅ 0 y) := by
  rw [rinv_eq]
  have : ((∅ : Finset ℕ).powerset ×ˢ range (0 + 1)).erase (∅, 0) = ∅ := by
    ext x; simp only [powerset_empty, zero_add, range_one, singleton_product_singleton,
      mem_erase, mem_singleton, notMem_empty, iff_false]; tauto
  rw [this]
  simp

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the hypotheses of the recursive inverse
hold for the pivot `GP h Γ`. -/
lemma GP_hyp (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hK : InK Γ) (hB : CoefB Γ) :
    (∀ y, IsUnit (GP h Γ ∅ 0 y)) ∧ InK (rinv (h + 1) (GP h Γ)) := by
  have hu : ∀ y, IsUnit (GP h Γ ∅ 0 y) := fun y => by rw [GP_empty_zero]; exact hB _
  exact ⟨hu, rinv_mem _ _ (W2 h Γ hK).2.2.1 (Kr_inverse ((W2 h Γ hK).2.2.1 ∅ 0) hu)⟩

/-- Helper for (W3) of `C48_cleanliness_one_move.md`: the matrix identities for the right
inverse `rinv (h + 1) (GP h Γ)`. -/
lemma W3_matrix (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hu : ∀ y, IsUnit (G ∅ 0 y)) :
    covSys P (h + 1) c G * covSys P (h + 1) c (rinv (h + 1) G) = 1 ∧
      covSys P (h + 1) c (rinv (h + 1) G) * covSys P (h + 1) c G = 1 := by
  have hR : covSys P (h + 1) c G * covSys P (h + 1) c (rinv (h + 1) G) = 1 := by
    rw [T1_mul, prodFun_rinv _ _ hu, ← T1_one]
  have hL : covSys P (h + 1) c (linv (h + 1) G) * covSys P (h + 1) c G = 1 := by
    rw [T1_mul, prodFun_linv _ _ hu, ← T1_one]
  refine ⟨hR, ?_⟩
  have hLQ : covSys P (h + 1) c (linv (h + 1) G) = covSys P (h + 1) c (rinv (h + 1) G) := by
    calc covSys P (h + 1) c (linv (h + 1) G)
        = covSys P (h + 1) c (linv (h + 1) G) *
            (covSys P (h + 1) c G * covSys P (h + 1) c (rinv (h + 1) G)) := by rw [hR, mul_one]
      _ = covSys P (h + 1) c (rinv (h + 1) G) := by rw [← mul_assoc, hL, one_mul]
  rw [← hLQ, hL]

/-- **(W3)** of `C48_cleanliness_one_move.md` (the pivot is invertible in the class): if `InK Γ`
and `CoefB Γ`, there is `GQ` with `InK GQ`, `prodFun (h + 1) (GP h Γ) GQ = Γ₁` (an equality of
functions), `covSys P (h + 1) c (GP h Γ) * covSys P (h + 1) c GQ = 1`,
`covSys P (h + 1) c GQ * covSys P (h + 1) c (GP h Γ) = 1` (equalities of matrices), and
`GQ ∅ 0 y * Γ ∅ 1 (y + 2 ^ h) = 1` for every `y`. -/
theorem W3 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hK : InK Γ) (hB : CoefB Γ) :
    ∃ GQ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], InK GQ ∧
      prodFun (h + 1) (GP h Γ) GQ = (fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0) ∧
      covSys P (h + 1) c (GP h Γ) * covSys P (h + 1) c GQ = 1 ∧
      covSys P (h + 1) c GQ * covSys P (h + 1) c (GP h Γ) = 1 ∧
      ∀ y, GQ ∅ 0 y * Γ ∅ 1 (y + 2 ^ h) = 1 := by
  obtain ⟨hu, hQ⟩ := GP_hyp h Γ hK hB
  refine ⟨rinv (h + 1) (GP h Γ), hQ, prodFun_rinv _ _ hu, (W3_matrix P h c _ hu).1,
    (W3_matrix P h c _ hu).2, fun y => ?_⟩
  rw [rinv_empty_zero, GP_empty_zero, Ring.inverse_mul_cancel _ (hB _)]

/-! ### (W4) -/

/-- Helper for (W4) of `C48_cleanliness_one_move.md`: differences of covariant systems. -/
lemma covSys_sub (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    covSys P h c Γ - covSys P h c Γ' = covSys P h c (Γ - Γ') := by
  funext D D'
  ext m f
  simp only [Matrix.sub_apply, Bf.coef_sub, covSys_coef, Pi.sub_apply]
  split_ifs <;> simp

/-- Helper for (W4) of `C48_cleanliness_one_move.md`: `thetaSys` of a difference. -/
lemma thetaSys_sub (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : InK Γ) (hΓ' : InK Γ') :
    thetaSys (Γ - Γ') = thetaSys Γ - thetaSys Γ' := by
  have hd : InK (Γ - Γ') := fun Δ m => K3_sub (hΓ Δ m) (hΓ' Δ m)
  have := (T3 0 (Γ - Γ') Γ' hd hΓ').2.1
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/-- Helper for (W4), (W5) of `C48_cleanliness_one_move.md`: the Schur complement system
`ΓS = GD Γ − (GB Γ · GQ) · GC h Γ`, with `GQ` the right inverse of the pivot. -/
def schurG (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] :=
  GD Γ - prodFun (h + 1) (prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ))) (GC h Γ)

/-- Helper for (W4) of `C48_cleanliness_one_move.md`: under the hypotheses of (W4), there is
`Γ'` with `InK Γ'`, `2 Γ' = ΓS` and the clean step. -/
theorem W4_strong (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hK : InK Γ) (hB : CoefB Γ) (hE : ∀ y, ∃ z, Γ ∅ 0 y = 2 * z) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], InK Γ' ∧
      (∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y) ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') := by
  obtain ⟨hu, hQ⟩ := GP_hyp h Γ hK hB
  obtain ⟨hGB, hGC, -, hGD, hθBC, hθD⟩ := W2 h Γ hK
  set GQ := rinv (h + 1) (GP h Γ) with hGQ
  have hX : InK (prodFun (h + 1) (GB Γ) GQ) := (T2 (h + 1) _ _ hGB hQ).1
  have hT : InK (prodFun (h + 1) (prodFun (h + 1) (GB Γ) GQ) (GC h Γ)) :=
    (T2 (h + 1) _ _ hX hGC).1
  have hS : InK (schurG h Γ) := fun Δ m => K3_sub (hGD Δ m) (hT Δ m)
  -- `Θ` of the Schur complement vanishes
  have hθ : thetaSys (schurG h Γ) = 0 := by
    rw [schurG, thetaSys_sub _ _ hGD hT, (T3 _ _ _ hX hGC).1, (T3 _ _ _ hGB hQ).1, hθD, ← hθBC]
    have hββ : thetaSys (GB Γ) * thetaSys (GB Γ) = 0 := by
      refine RS.ext fun Δ q => ?_
      rw [R2, RS.zero_apply]
      split_ifs
      · have h0 : GB Γ ∅ 0 = Γ ∅ 0 := by funext y; simp [GB]
        rw [thetaSys_apply, h0]
        obtain ⟨r, hr⟩ := hK ∅ 0
        rw [← hr]
        refine (S5 r).2 ?_
        obtain ⟨z, hz⟩ := hE 0
        obtain ⟨w, hw⟩ := (K6 r 0).1
        refine ⟨z - 2 * w, ?_⟩
        rw [hr] at hw
        linear_combination hz - hw
      · rfl
    calc (0 : RS) - thetaSys (GB Γ) * thetaSys GQ * thetaSys (GB Γ)
        = -((thetaSys (GB Γ) * thetaSys (GB Γ)) * thetaSys GQ) := by ring
      _ = 0 := by rw [hββ, zero_mul, neg_zero]
  have h0 : ∀ Δ m, theta (schurG h Γ Δ m) = 0 := fun Δ m => by
    rw [← thetaSys_apply, hθ, RS.zero_apply]
  choose Γ' hΓ' using fun Δ m => (S3 (hS Δ m)).1 (h0 Δ m)
  have h2 : ∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y := fun Δ m y =>
    (congrFun (hΓ' Δ m).2 y).symm
  refine ⟨Γ', fun Δ m => (hΓ' Δ m).1, h2, covSys P (h + 1) c GQ, ?_, ?_, ?_⟩
  · rw [W1_P, (W3_matrix P h c _ hu).1]; exact fun _ _ _ _ _ => rfl
  · rw [W1_P, (W3_matrix P h c _ hu).2]; exact fun _ _ _ _ _ => rfl
  · have hS2 : schurG h Γ = (2 : ℤ_[2]) • Γ' := by
      funext Δ m y; rw [← h2]; rfl
    rw [W1_D, W1_B, W1_C, T1_mul, T1_mul, covSys_sub, ← schurG, hS2, ← T1_smul]
    exact fun _ _ _ _ _ => rfl

/-- **(W4)** of `C48_cleanliness_one_move.md` (even payments make one move clean): if `InK Γ`,
`CoefB Γ` and `∀ y, ∃ z, Γ ∅ 0 y = 2 * z`, there is `Γ'` with `InK Γ'` and
`CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`. -/
theorem W4 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hK : InK Γ) (hB : CoefB Γ) (hE : ∀ y, ∃ z, Γ ∅ 0 y = 2 * z) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], InK Γ' ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') := by
  obtain ⟨Γ', h1, -, h3⟩ := W4_strong P h c Γ hK hB hE
  exact ⟨Γ', h1, h3⟩

/-! ### (W5) -/

/-- Helper for (W5) of `C48_cleanliness_one_move.md`: `prodFun` at `(∅, 0)` is a single
product. -/
lemma prodFun_empty_zero (k : ℕ) (G G' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (y : ℤ_[2]) :
    prodFun k G G' ∅ 0 y = G ∅ 0 y * G' ∅ 0 y := by
  simp [prodFun, oS]

/-- Helper for (W5) of `C48_cleanliness_one_move.md`: `prodFun` at `(∅, 1)`. -/
lemma prodFun_empty_one (k : ℕ) (G G' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (y : ℤ_[2]) :
    prodFun k G G' ∅ 1 y = G ∅ 0 y * G' ∅ 1 y + G ∅ 1 y * G' ∅ 0 (y - 2 ^ k) := by
  simp [prodFun, oS, sum_range_succ]

/-- Helper for (W5) of `C48_cleanliness_one_move.md`: `GD Γ Δ 1 y = 2 Γ Δ 1 y`. -/
lemma GD_one (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (y : ℤ_[2]) :
    GD Γ Δ 1 y = 2 * Γ Δ 1 y := by
  show ((2 * 0 + 2 : ℕ) : ℤ_[2]) * dfi (0 + 1) * Γ Δ (2 * 0 + 1) y = _
  simp

/-- **(W5)** of `C48_cleanliness_one_move.md` (Theorem 10.15, the twist move): if `Good Γ`, there
is `Γ'` with `Good Γ'`, `CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`, and for every `y`:
`2 * Γ' ∅ 0 y = -(Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * Γ ∅ 0 (y + 2 ^ h))` and
`∃ z, Γ' ∅ 0 y = 8 * z`. -/
theorem W5 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hG : Good Γ) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') ∧
      ∀ y, 2 * Γ' ∅ 0 y = -(Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * Γ ∅ 0 (y + 2 ^ h)) ∧
        ∃ z, Γ' ∅ 0 y = 8 * z := by
  obtain ⟨hK, hA, hB⟩ := hG
  have hE : ∀ y, ∃ z, Γ ∅ 0 y = 2 * z := fun y => by
    obtain ⟨z, hz⟩ := hA y
    exact ⟨2 * z, by rw [hz]; ring⟩
  obtain ⟨Γ', hK', h2, hC⟩ := W4_strong P h c Γ hK hB hE
  have hQ0 : ∀ y, rinv (h + 1) (GP h Γ) ∅ 0 y = Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) := fun y => by
    rw [rinv_empty_zero, GP_empty_zero]
  have hform : ∀ y, 2 * Γ' ∅ 0 y =
      -(Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * Γ ∅ 0 (y + 2 ^ h)) := fun y => by
    rw [h2, schurG, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, prodFun_empty_zero,
      prodFun_empty_zero, hQ0]
    simp [GD, GB, GC]
  have h8 : ∀ y, ∃ z, Γ' ∅ 0 y = 8 * z := fun y => by
    obtain ⟨a, ha⟩ := hA y
    obtain ⟨b, hb⟩ := hA (y + 2 ^ h)
    refine ⟨-(a * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * b), ?_⟩
    have := hform y
    rw [ha, hb] at this
    exact mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) (by rw [this]; ring)
  refine ⟨Γ', ⟨hK', fun y => ?_, fun y => ?_⟩, hC, fun y => ⟨hform y, h8 y⟩⟩
  · obtain ⟨z, hz⟩ := h8 y
    exact ⟨2 * z, by rw [hz]; ring⟩
  · -- condition (b) one level up
    obtain ⟨a, ha⟩ := hA y
    obtain ⟨b, hb⟩ := hA (y - 2 ^ (h + 1) + 2 ^ h)
    have hX0 : prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ)) ∅ 0 y = Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) := by
      simp only [prodFun_empty_zero, hQ0, GB, dfi_zero, Nat.mul_zero, one_mul]
    set w := a * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * GC h Γ ∅ 1 y +
      prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ)) ∅ 1 y * b
    have hval : 2 * Γ' ∅ 1 y = 2 * (Γ ∅ 1 y - 2 * w) := by
      rw [h2, schurG, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, prodFun_empty_one, GD_one, hX0]
      have hC0 : GC h Γ ∅ 0 (y - 2 ^ (h + 1)) = 4 * b := by
        simp only [GC, dfi_zero, Nat.mul_zero, one_mul]; exact hb
      rw [hC0, ha]
      ring
    have hv := mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) hval
    rw [hv, isUnit_iff_red_ne_zero, map_sub, map_mul, red_two, zero_mul, sub_zero,
      ← isUnit_iff_red_ne_zero]
    exact hB y

end Cleanliness
