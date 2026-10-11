module

public import RequestProject.Stability.PartA
public import RequestProject.PathSum.All

/-!
# `C44_stability_and_rigidity.md`, Part F — the final matrix of `Σ` (`η = 1`)

Namespace `Stability`. Reused (not redefined): C43 `PathSum.SigOp`; C40b `FormalDance.paySys`,
`DanceRel`, `finalM`, `L4_sigma`, `danceRel_unique`; C13 `Dance.pσ`, `Dance.κσ`, `Dance.Mfin`,
`Dance.slots_eq`; C14 `Windows.theorem_4_4`, `Windows.H3_final_matrix`; C10 `Deficit.Mc`,
`Deficit.pi0`; C3 `Rulers.oE`.

* (F1) `F1` (for `ds = Families.ds l`; `F1_gen` for every digit list `ds`).
* (F2) `F2` with the diagonal factors `F2d1`, `F2d2` (`F2_gen` for every `ds`).

The hypothesis `l ≥ 1` of Part F is not needed for (F1) and (F2), and `c ≥ 1` is not needed
for (F1); they are left out of these two statements (more general).
-/

@[expose] public section

noncomputable section

namespace Stability

open Matrix Finset FormalOps FormalDance

/-- `SigOp α c 1` agrees with the payment system `paySys (pσ α c) κσ` (for `α ≥ 1`). -/
lemma sigOp_magree_paySys {α : ℕ} (hα : 1 ≤ α) (c : ℕ) :
    MAgree (fun _ _ => PathSum.SigOp α c 1 : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2]))
      (paySys (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ) := by
  intro s s' m f hmf
  have hss : s = s' := Subsingleton.elim _ _
  subst hss
  have hp : paySys (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ s s =
      Bf.fd 1 + Bf.dg (ext0 (fun f => 2 * Dance.pσ α c s f)) := by simp [paySys]
  show (PathSum.SigOp α c 1).coef m f = _
  rw [hp, Bf.coef_add, Bf.coef_fd, Bf.coef_dg]
  rcases m with _ | _ | m
  · simp only [PathSum.SigOp, PathSum.XiOp_coef_zero, PathSum.piF, ext0, Dance.pσ]
    have hf : 0 ≤ f := by exact_mod_cast hmf
    rw [if_pos hf]
    have hc : ((f.toNat : ℕ) : ℚ_[2]) = (f : ℚ_[2]) := by
      exact_mod_cast Int.toNat_of_nonneg hf
    rw [hc]
    have h2 : (2 : ℚ_[2]) ^ α = 2 * 2 ^ (α - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [if_true, show (0 : ℕ) ≠ 1 by omega, if_false, zero_add, h2]
    ring
  · simp [PathSum.SigOp]
  · rw [PathSum.SigOp, PathSum.XiOp_coef_ge_two _ _ _ _ (by omega)]
    simp

/-- (F1) of `C44_stability_and_rigidity.md`, for an arbitrary digit list `ds` and `α ≥ 1`. -/
theorem F1_gen (ds : List Bool) {α : ℕ} (hα : 1 ≤ α) (c : ℕ)
    (GSig : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]))
    (hG : DanceRel ds 1 (fun _ _ => PathSum.SigOp α c 1) GSig)
    (s s' : Fin (Dance.slots ds 1)) :
    finalM GSig s s' = if nest ds s s' then
      ((Deficit.Mc (Windows.Ids ds) ds.length (α : ℤ) c (Windows.Dset ds s)
        (Windows.Dset ds s') : ℚ) : ℚ_[2]) else 0 := by
  have h2 : ∀ a : ℚ_[2], 2 * a = 0 → a = 0 := fun a h => by
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hL := L4_sigma (A := ℚ_[2]) ds α c
  have hag := danceRel_unique h2 ds 1 _ _ GSig _ (sigOp_magree_paySys hα c) hG hL.1
  set t : Fin (1 * 2 ^ Dance.mCount ds) := Fin.cast (Dance.slots_eq ds 1) s
  set t' : Fin (1 * 2 ^ Dance.mCount ds) := Fin.cast (Dance.slots_eq ds 1) s'
  have hfin : finalM GSig s s' =
      Dance.Mfin (Dance.dance ds 1 (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ).1
        (Dance.dance ds 1 (Dance.pσ (A := ℚ_[2]) α c) Dance.κσ).2 t t' := by
    rw [← hL.2 t t']
    exact hag s s' 0 0 le_rfl
  rw [hfin, Windows.H3_final_matrix ℚ_[2] ds α c, Matrix.map_apply]
  set u : Fin (2 ^ Dance.mCount ds) := Fin.cast (one_mul _) t
  set u' : Fin (2 ^ Dance.mCount ds) := Fin.cast (one_mul _) t'
  have h44 := Windows.theorem_4_4 ds α c hα u u'
  rw [Matrix.submatrix_apply, Windows.H3_final_matrix ℚ ds α c, Matrix.map_apply] at h44
  have hut : Fin.cast (one_mul (2 ^ Dance.mCount ds)).symm u = t := by ext; rfl
  have hut' : Fin.cast (one_mul (2 ^ Dance.mCount ds)).symm u' = t' := by ext; rfl
  rw [hut, hut'] at h44
  have hus : (u : ℕ) = s := rfl
  have hus' : (u' : ℕ) = s' := rfl
  rw [hus, hus'] at h44
  have hcast : ∀ z : ℤ, ((z : ℚ) : ℚ_[2]) = (z : ℚ_[2]) := fun z => Rat.cast_intCast z
  simp only [Int.coe_castRingHom] at h44 ⊢
  rw [← hcast, h44]
  unfold nest
  split_ifs <;> simp

/-- **(F1) `M_w(Σ)` is the closed form** (`C44_stability_and_rigidity.md`, Part F): for
`α ≥ 1` and `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c 1) GSig`, for all
`s s'`: `finalM GSig s s' = Mc (Ids ds) k α c D_s D_{s'}` (cast from `ℚ` to `ℚ_[2]`) if
`nest ds s s'`, and `0` otherwise (`ds = Families.ds l`, `k = ds.length`). The hypotheses
`l ≥ 1` and `c ≥ 1` of the file are not needed here. -/
theorem F1 {l α c : ℕ} (hα : 1 ≤ α)
    (GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GSig)
    (s s' : Fin (Dance.slots (Families.ds l) 1)) :
    finalM GSig s s' = if nest (Families.ds l) s s' then
      ((Deficit.Mc (Windows.Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
        (Windows.Dset (Families.ds l) s) (Windows.Dset (Families.ds l) s') : ℚ) : ℚ_[2])
      else 0 :=
  F1_gen _ hα c GSig hG s s'

/-- (F2) of `C44_stability_and_rigidity.md`: the left diagonal factor
`d₁ s := −2^{1 − K} · 2^{o(D_s)} / ∏_{d ∈ range (o(D_s))} pi0 α c d` (in `ℚ`, `K = 2^k`,
`k = ds.length`, `o = Rulers.oE`). -/
def F2d1 (ds : List Bool) (α c : ℕ) (s : Fin (Dance.slots ds 1)) : ℚ :=
  -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ ds.length) * 2 ^ Rulers.oE (Windows.Dset ds s) /
    ∏ d ∈ range (Rulers.oE (Windows.Dset ds s)), Deficit.pi0 (α : ℤ) c d

/-- (F2) of `C44_stability_and_rigidity.md`: the right diagonal factor
`d₂ s := 2^{−o(D_s)} · ∏_{d ∈ range (o(D_s) + K)} pi0 α c d` (in `ℚ`, `K = 2^k`). -/
def F2d2 (ds : List Bool) (α c : ℕ) (s : Fin (Dance.slots ds 1)) : ℚ :=
  (2 : ℚ) ^ (-(Rulers.oE (Windows.Dset ds s) : ℤ)) *
    ∏ d ∈ range (Rulers.oE (Windows.Dset ds s) + 2 ^ ds.length), Deficit.pi0 (α : ℤ) c d

lemma pi0_ne_zero {α : ℤ} {c : ℕ} (hc : 1 ≤ c) (d : ℕ) : Deficit.pi0 α c d ≠ 0 := by
  unfold Deficit.pi0
  have : (0 : ℚ) < (c : ℚ) + d := by positivity
  positivity

lemma prod_pi0_ne_zero {α : ℤ} {c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    ∏ d ∈ range m, Deficit.pi0 α c d ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun d _ => pi0_ne_zero hc d

lemma F2d1_ne_zero (ds : List Bool) (α : ℕ) {c : ℕ} (hc : 1 ≤ c) (s : Fin (Dance.slots ds 1)) :
    F2d1 ds α c s ≠ 0 := by
  unfold F2d1
  have := prod_pi0_ne_zero (α := (α : ℤ)) hc (Rulers.oE (Windows.Dset ds s))
  have h2 : (2 : ℚ) ^ ((1 : ℤ) - 2 ^ ds.length) ≠ 0 := zpow_ne_zero _ two_ne_zero
  have h3 : (2 : ℚ) ^ Rulers.oE (Windows.Dset ds s) ≠ 0 := pow_ne_zero _ two_ne_zero
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.2 h2) h3) this

lemma F2d2_ne_zero (ds : List Bool) (α : ℕ) {c : ℕ} (hc : 1 ≤ c) (s : Fin (Dance.slots ds 1)) :
    F2d2 ds α c s ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ two_ne_zero) (prod_pi0_ne_zero hc _)

/-- The entry identity of (F2): on nested pairs, `d₁ s · a_k(D_s ∖ D_{s'}) · d₂ s' = Mc`. -/
lemma F2_entry (ds : List Bool) (α : ℕ) {c : ℕ} (hc : 1 ≤ c) {s s' : Fin (Dance.slots ds 1)}
    (h : nest ds s s') :
    F2d1 ds α c s * (Deficit.a (Windows.Ids ds) ds.length
        (Windows.Dset ds s \ Windows.Dset ds s') : ℚ) * F2d2 ds α c s' =
      Deficit.Mc (Windows.Ids ds) ds.length (α : ℤ) c (Windows.Dset ds s)
        (Windows.Dset ds s') := by
  unfold F2d1 F2d2 Deficit.Mc
  set o := Rulers.oE (Windows.Dset ds s)
  set o' := Rulers.oE (Windows.Dset ds s')
  set oΔ := Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s')
  have hsd : oΔ + o' = o := Rulers.oE_sdiff h
  have hlt : o < 2 ^ ds.length :=
    Rulers.oE_lt _ _ (fun t ht => lt_of_mem_Dset ht)
  have hprod : (∏ d ∈ range o, Deficit.pi0 (α : ℤ) c d) *
      ∏ d ∈ Ico o (o' + 2 ^ ds.length), Deficit.pi0 (α : ℤ) c d =
      ∏ d ∈ range (o' + 2 ^ ds.length), Deficit.pi0 (α : ℤ) c d :=
    Finset.prod_range_mul_prod_Ico _ (by omega)
  have hP := prod_pi0_ne_zero (α := (α : ℤ)) hc o
  have h2o : (2 : ℚ) ^ o = 2 ^ oΔ * 2 ^ o' := by rw [← pow_add, hsd]
  rw [← hprod, zpow_add₀ two_ne_zero, _root_.zpow_neg, zpow_natCast, zpow_natCast, h2o]
  field_simp

/-- (F2) of `C44_stability_and_rigidity.md`, for an arbitrary digit list `ds`. -/
theorem F2_gen (ds : List Bool) {α c : ℕ} (hα : 1 ≤ α) (hc : 1 ≤ c)
    (GSig : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]))
    (hG : DanceRel ds 1 (fun _ _ => PathSum.SigOp α c 1) GSig) :
    finalM GSig = diagonal (fun s => (F2d1 ds α c s : ℚ_[2])) * Amat ds *
        diagonal (fun s => (F2d2 ds α c s : ℚ_[2])) ∧
      (∀ s, F2d1 ds α c s ≠ 0) ∧ (∀ s, F2d2 ds α c s ≠ 0) := by
  refine ⟨?_, F2d1_ne_zero ds α hc, F2d2_ne_zero ds α hc⟩
  ext s s'
  rw [F1_gen ds hα c GSig hG s s', mul_diagonal, diagonal_mul]
  simp only [Amat, of_apply]
  split_ifs with h
  · rw [← F2_entry ds α hc h]
    push_cast
    ring
  · simp

/-- **(F2) The factorization `M_w(Σ) = 𝔡₁ 𝒜 𝔡₂`** (`C44_stability_and_rigidity.md`, Part F):
for `α ≥ 1`, `c ≥ 1` and `GSig` with `DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c 1) GSig`,
`finalM GSig = diagonal d₁ * Amat ds * diagonal d₂` with `d₁ = F2d1 ds α c`, `d₂ = F2d2 ds α c`
(in `ℚ`, cast to `ℚ_[2]`), and `d₁ s ≠ 0`, `d₂ s ≠ 0` for every `s` (`ds = Families.ds l`).
The hypothesis `l ≥ 1` of the file is not needed here. -/
theorem F2 {l α c : ℕ} (hα : 1 ≤ α) (hc : 1 ≤ c)
    (GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GSig) :
    finalM GSig = diagonal (fun s => (F2d1 (Families.ds l) α c s : ℚ_[2])) *
        Amat (Families.ds l) * diagonal (fun s => (F2d2 (Families.ds l) α c s : ℚ_[2])) ∧
      (∀ s, F2d1 (Families.ds l) α c s ≠ 0) ∧ (∀ s, F2d2 (Families.ds l) α c s ≠ 0) :=
  F2_gen _ hα hc GSig hG

end Stability
