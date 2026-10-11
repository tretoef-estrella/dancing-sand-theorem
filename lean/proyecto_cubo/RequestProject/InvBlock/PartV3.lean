module

public import RequestProject.InvBlock.PartV1

/-!
# `C41_inverse_block.md`: (V3) Lemma 10.8 in lift form, (V4), (V5) the inverse form

* (V3) `V3`, from `V3_aux`: strong induction on `l`, following the defining equations of
  `Filt.T` and `Families.ds` (the pattern of C40d `FormalProp.Q1_aux`, for all `r`, `G`, `Gk`,
  `B ≥ l + 1` at once). To keep the types of `Gk` free, `V3_aux` is stated for every list `ds`
  with `Families.ds l = ds`, the slots being reindexed by `ri` along that equality (for
  `ds = Families.ds l` and `rfl` this is the identity, which gives `V3`).
  - `l = 0`: `L = inH 0 r` (through `unitEquiv`), by C40c (A1) and (A4_apply);
  - twist step: `L = lift ∘ L'`, by (V1) and the induction hypothesis on `T A (l / 2)`;
  - split step: `L = vpack ∘ lift ∘ (relabel)⁻¹ ∘ L'`, by (V2), the relabelling C40c (A3_conj)
    and the induction hypothesis with `r * 2` slots.
  The next level is always taken with `B' = l' + 1` (C40c (N2)).
* (V4) `V4`: if `M z = 0` then `sysAct G (L z) = 0`, so `L z = 0`, so `z = outH (L z) = 0`.
* (V5) `V5`: by (V4), `finalM Gk` is injective, hence invertible over a field; then
  `z = M⁻¹ y` gives `L z = 2^k e.symm (inH y)` and `z = outH (L z)`.

All hypotheses of the file are used.
-/

@[expose] public section

noncomputable section

namespace InvBlock

open DPLattice Doubling Filt FormalOps FormalDance FormalAct

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- (V3) of `C41_inverse_block.md`, the induction (auxiliary): the lift form for every list `ds`
with `Families.ds l = ds`, the slots of `Gk` being reindexed along that equality by `ri`. -/
theorem V3_aux (l : ℕ) : ∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A)) (ds : List Bool)
    (hl : Families.ds l = ds) (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A)),
    DanceRel ds r G Gk → ∀ B : ℕ, l + 1 ≤ B →
    ∃ L : (Fin (Dance.slots ds r) → A) →ₗ[A] (Fin r → (T A l).ι → A),
      sysAct (T A l) (l : ℤ) B G ∘ₗ L = (2 : A) ^ ds.length •
        (inH l r ∘ₗ ri (congrArg (Dance.slots · r) hl).symm ∘ₗ Matrix.mulVecLin (finalM Gk)) ∧
      ri (congrArg (Dance.slots · r) hl) ∘ₗ outH l r ∘ₗ L = LinearMap.id := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases l with _ | n
  · intro r G ds hl Gk hG B hB
    obtain rfl : ds = [] := by rw [← hl, Families.ds_zero]
    have hG' : MAgree G Gk := hG
    have htop : ∀ i, (one A).wt i ≤ (0 : ℤ) ∧ Even ((0 : ℤ) - (one A).wt i) :=
      fun _ => ⟨le_refl _, by simp [one]⟩
    refine ⟨(castLat (T_zero (A := A)).symm (Fin r)).toLinearMap ∘ₗ
      (unitEquiv : (Fin r → Unit → A) ≃ₗ[A] (Fin r → A)).symm.toLinearMap, ?_, ?_⟩
    · refine LinearMap.ext fun z => ?_
      rw [inH]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, List.length_nil,
        pow_zero, one_smul, sysAct_castLat, Nat.cast_zero]
      congr 1
      rw [A1 htop hG' B]
      funext s u
      exact (A4_apply (by omega) Gk _ s).trans rfl
    · refine LinearMap.ext fun z => ?_
      rw [outH]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [castLat_symm_apply, LinearEquiv.apply_symm_apply]
      rfl
  · intro r G ds hl Gk hG B hB
    by_cases hn : n % 2 = 0
    · obtain rfl : ds = false :: Families.ds (n / 2) := hl.symm.trans (ds_succ_pos hn)
      obtain ⟨G', ⟨Q, hPQ, -, hS⟩, hG'⟩ := hG
      obtain ⟨htop, hnil⟩ := N2 (A := A) (n / 2)
      obtain ⟨L', h1, h2⟩ := ih (n / 2) (by omega) r G' _ rfl Gk hG' (n / 2 + 1) le_rfl
      refine ⟨(castLat (T_succ_pos A hn).symm (Fin r)).toLinearMap ∘ₗ
        lift (T A (n / 2)) ((n / 2 : ℕ) : ℤ) (n / 2 + 1) Q G ∘ₗ L', ?_, ?_⟩
      · refine LinearMap.ext fun z => ?_
        have e1 := congrArg (fun f => f z) h1
        simp only [LinearMap.comp_apply, LinearMap.smul_apply] at e1
        rw [inH, dif_pos hn]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]
        erw [sysAct_castLat]
        rw [show ((n + 1 : ℕ) : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + 1 by omega]
        erw [(V1 (B := B) htop hnil (by omega) le_rfl (by omega) hPQ hS (L' z)).1]
        rw [e1, smul_smul,
          pack_smul_zero, map_smul, List.length_cons, pow_succ']
        rfl
      · refine LinearMap.ext fun z => ?_
        have e2 := congrArg (fun f => f z) h2
        rw [outH, dif_pos hn]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at e2 ⊢
        erw [castLat_symm_apply, out1_lift]
        exact e2
    · obtain rfl : ds = true :: Families.ds (n / 2) := hl.symm.trans (ds_succ_neg hn)
      obtain ⟨G'', ⟨Q, hPQ, -, hS⟩, hG''⟩ := hG
      obtain ⟨htop, hnil⟩ := N2 (A := A) (n / 2)
      obtain ⟨L', h1, h2⟩ := ih (n / 2) (by omega) (r * 2) _ _ rfl Gk hG'' (n / 2 + 1) le_rfl
      refine ⟨(castLat (T_succ_neg A hn).symm (Fin r)).toLinearMap ∘ₗ
        (vpack : (Fin r × Fin 2 → (phi (T A (n / 2))).ι → A) ≃ₗ[A] _).toLinearMap ∘ₗ
        lift (T A (n / 2)) ((n / 2 : ℕ) : ℤ) (n / 2 + 1) Q (vsplit G) ∘ₗ
        (relab (A := A) r ((T A (n / 2)).ι → A)).symm.toLinearMap ∘ₗ L', ?_, ?_⟩
      · refine LinearMap.ext fun z => ?_
        have e1 := congrArg (fun f => f z) h1
        simp only [LinearMap.comp_apply, LinearMap.smul_apply] at e1
        have e3 := congrArg (fun f : (Fin (r * 2) → (T A (n / 2)).ι → A) →ₗ[A]
            (Fin (r * 2) → (T A (n / 2)).ι → A) => (relab (A := A) r ((T A (n / 2)).ι → A)).symm (f (L' z)))
          (A3_conj (N := T A (n / 2)) (W := ((n / 2 : ℕ) : ℤ)) (n / 2 + 1)
            (FormalProp.splitEquiv r) G'')
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_apply_apply] at e3
        rw [inH, dif_neg hn]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]
        erw [sysAct_castLat]
        rw [show ((n + 1 : ℕ) : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + 2 by omega]
        erw [(V2 (B := B) htop hnil (by omega) le_rfl (by omega) hPQ hS _).1]
        erw [← e3, e1]
        rw [map_smul, smul_smul, pack_smul_zero, map_smul, map_smul, List.length_cons, pow_succ']
        rfl
      · refine LinearMap.ext fun z => ?_
        have e2 := congrArg (fun f => f z) h2
        rw [outH, dif_neg hn]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at e2 ⊢
        erw [castLat_symm_apply, LinearEquiv.symm_apply_apply]
        erw [out1_lift (T A (n / 2)) ((n / 2 : ℕ) : ℤ) (n / 2 + 1) Q (vsplit G)]
        show ri _ (ri _ (outH (n / 2) (r * 2) ((relab (A := A) r ((T A (n / 2)).ι → A))
          ((relab (A := A) r ((T A (n / 2)).ι → A)).symm (L' z))))) = z
        rw [LinearEquiv.apply_symm_apply]
        exact e2

/-- **(V3)** of `C41_inverse_block.md` (Lemma 10.8, lift form): for all `l r : ℕ`,
`G : Matrix (Fin r) (Fin r) (Bf A)`, `Gk : Matrix (Fin ns) (Fin ns) (Bf A)`
(`ns = Dance.slots (Families.ds l) r`) with `DanceRel (Families.ds l) r G Gk`, and every
`B ≥ l + 1`, there is a linear map `L : (Fin ns → A) →ₗ[A] (Fin r → (T A l).ι → A)` with
`sysAct (T A l) (l : ℤ) B G ∘ₗ L = (2 : A) ^ k • (inH l r ∘ₗ Matrix.mulVecLin (finalM Gk))`
(`k = (Families.ds l).length`) and `outH l r ∘ₗ L = LinearMap.id`. -/
theorem V3 (l r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf A))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B) :
    ∃ L : (Fin (Dance.slots (Families.ds l) r) → A) →ₗ[A] (Fin r → (T A l).ι → A),
      sysAct (T A l) (l : ℤ) B G ∘ₗ L =
        (2 : A) ^ (Families.ds l).length • (inH l r ∘ₗ Matrix.mulVecLin (finalM Gk)) ∧
      outH l r ∘ₗ L = LinearMap.id :=
  V3_aux l r G _ rfl Gk hG B hB

/-- **(V4)** of `C41_inverse_block.md` (corollary of (V3), over the same `A`): in the setting of
(V3), if `sysAct (T A l) (l : ℤ) B G` is injective, then `Matrix.mulVecLin (finalM Gk)` is
injective. -/
theorem V4 (l r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf A))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B)
    (hinj : Function.Injective (sysAct (T A l) (l : ℤ) B G)) :
    Function.Injective (Matrix.mulVecLin (finalM Gk)) := by
  obtain ⟨L, h1, h2⟩ := V3 l r G Gk hG B hB
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  have e1 := LinearMap.congr_fun h1 z
  have e2 := LinearMap.congr_fun h2 z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hz, map_zero, smul_zero,
    LinearMap.id_apply] at e1 e2
  have hL : L z = 0 := hinj (by rw [e1, map_zero])
  rw [← e2, hL, map_zero]

/-- **(V5)** of `C41_inverse_block.md` (Lemma 10.8, inverse form, over a field): let `K` be a
field with `[CharZero K] [OddUnits K]`. In the setting of (V3) over `K`, let
`e : (Fin r → (T K l).ι → K) ≃ₗ[K] (Fin r → (T K l).ι → K)` with
`(e : _ →ₗ[K] _) = sysAct (T K l) (l : ℤ) B G`. Then `IsUnit (finalM Gk).det` and
`Matrix.mulVecLin ((finalM Gk)⁻¹) = (2 : K) ^ k • (outH l r ∘ₗ (e.symm : _ →ₗ[K] _) ∘ₗ inH l r)`
(`k = (Families.ds l).length`). -/
theorem V5 {K : Type*} [Field K] [CharZero K] [OddUnits K] (l r : ℕ)
    (G : Matrix (Fin r) (Fin r) (Bf K))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) (Bf K))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B)
    (e : (Fin r → (T K l).ι → K) ≃ₗ[K] (Fin r → (T K l).ι → K))
    (he : (e : (Fin r → (T K l).ι → K) →ₗ[K] (Fin r → (T K l).ι → K)) =
      sysAct (T K l) (l : ℤ) B G) :
    IsUnit (finalM Gk).det ∧
      Matrix.mulVecLin ((finalM Gk)⁻¹) =
        (2 : K) ^ (Families.ds l).length •
          (outH l r ∘ₗ (e.symm : (Fin r → (T K l).ι → K) →ₗ[K] (Fin r → (T K l).ι → K)) ∘ₗ
            inH l r) := by
  have hinj : Function.Injective (sysAct (T K l) (l : ℤ) B G) := by
    rw [← he]; exact e.injective
  have hM := V4 l r G Gk hG B hB hinj
  have hdet : IsUnit (finalM Gk).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 hM)
  refine ⟨hdet, ?_⟩
  obtain ⟨L, h1, h2⟩ := V3 l r G Gk hG B hB
  refine LinearMap.ext fun y => ?_
  set z := Matrix.mulVec (finalM Gk)⁻¹ y with hz
  have hMz : Matrix.mulVec (finalM Gk) z = y := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have e1 := LinearMap.congr_fun h1 z
  have e2 := LinearMap.congr_fun h2 z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Matrix.mulVecLin_apply, hMz,
    LinearMap.id_apply] at e1 e2
  rw [← he, LinearEquiv.coe_coe] at e1
  have hL : L z = (2 : K) ^ (Families.ds l).length • e.symm (inH l r y) := by
    rw [← map_smul, ← e1, LinearEquiv.symm_apply_apply]
  simp only [Matrix.mulVecLin_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [← map_smul, ← hL, e2]

end InvBlock
