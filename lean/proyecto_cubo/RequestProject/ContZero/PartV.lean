module

public import RequestProject.ContZero.PartC
public import RequestProject.DanceXi.All
public import RequestProject.DanceSmith.All

/-!
# `C49b_congruence_and_the_data_at_zero.md`: Part V — the data of `Ξ` at `c = 0`

Hypotheses (H0) of the file: `1 ≤ l`, `2 ≤ α`, `η : ℤ_[2]` with `IsUnit η`, `z : ℕ → ℤ_[2]`, and
`GkZ` with `DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ`.
The reindexing `cs` of the file is written out as
`Fin.cast (Smith2.slots_cast (Families.ds l))`.

* (V1) `V1`: for every `N` the dance at `c = 2 ^ (N + k)` (`k = ds.length`, C48b (T3)) has entries
  within `2^{−(α+N)}` of those at `c = 0`, by (C1), (T1), (T2); the integer final matrices are as
  close, by (C3); at `c = 2 ^ (N + k) ≥ 1` the norms agree (C46 (V1), C14 `theorem_D_ii`). Hence
  `|‖a‖ − ‖b‖| ≤ 2 · 2^{−N}` for every `N` (triangle inequality), so `‖a‖ = ‖b‖`.
* (V2) `V2`: from (V1) and injectivity of `ℤ → ℤ_[2]`.
* (V3) `V3`: C15 `final_row_zero` and (V2); a matrix with a zero row has determinant `0`.
-/

@[expose] public section

noncomputable section

namespace ContZero

open FormalOps FormalDance

/-- Proof of (V1) of `C49b_congruence_and_the_data_at_zero.md`: two reals within `2 · 2⁻¹ ^ N` of
each other for every `N` are equal. -/
lemma eq_of_forall_abs_le {x y : ℝ} (h : ∀ N : ℕ, |x - y| ≤ 2 * (2⁻¹ : ℝ) ^ N) : x = y := by
  have hlim : Filter.Tendsto (fun N : ℕ => 2 * (2⁻¹ : ℝ) ^ N) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul 2
  have : |x - y| ≤ 0 := ge_of_tendsto' hlim h
  have := abs_nonpos_iff.1 this
  linarith

/-- **(V1)** of `C49b_congruence_and_the_data_at_zero.md` (norms): under (H0), for all
`s s' : Fin (2 ^ Dance.mCount (Families.ds l))`,
`‖finalM GkZ (cs s) (cs s')‖ = ‖((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])‖`,
with `cs = Fin.cast (Smith2.slots_cast (Families.ds l))`. -/
theorem V1 {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ)
    (s s' : Fin (2 ^ Dance.mCount (Families.ds l))) :
    ‖finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l)) s)
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s')‖ =
      ‖((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])‖ := by
  set k := (Families.ds l).length
  set t := Fin.cast (Smith2.slots_cast (Families.ds l)) s
  set t' := Fin.cast (Smith2.slots_cast (Families.ds l)) s'
  refine eq_of_forall_abs_le fun N => ?_
  obtain ⟨GkN, hGN⟩ := DanceXi.T3 (Families.ds l) α (2 ^ (N + k)) hα η hη z
  have hdvd : (2 : ℤ) ^ (N + k) ∣ ((2 ^ (N + k) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) := by
    push_cast; simp
  -- the systems at `c = 0` and at `c = 2 ^ (N + k)`
  have hcong : MCong (α + N + k) (fun _ _ : Fin 1 => Smith2.XiOpZ α 0 η (fun m _ => z m))
      (fun _ _ : Fin 1 => Smith2.XiOpZ α (2 ^ (N + k)) η (fun m _ => z m)) := by
    have h1 := C1 α 0 (2 ^ (N + k)) (N + k) hdvd η (fun m _ => z m)
    rw [← add_assoc] at h1
    exact mcong_iff.2 fun _ _ => h1
  obtain ⟨w, hw⟩ := T2 (T1 (Families.ds l) 1 (α + N) _ _ GkZ GkN hG hGN hcong) t t'
  -- the integer final matrices
  obtain ⟨v, hv⟩ := C3 (by omega : 1 ≤ α) (Families.ds l) 0 (2 ^ (N + k)) (N + k) (α + N) hdvd
    (by omega) s s'
  have hv' : ((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2]) -
      ((Windows.finalMatrix ℤ (Families.ds l) α (2 ^ (N + k)) s s' : ℤ) : ℤ_[2]) =
      2 ^ (α + N) * (v : ℤ_[2]) := by
    rw [← Int.cast_sub, hv]; push_cast; ring
  -- the norms at `c = 2 ^ (N + k)`
  have hnorm : ‖finalM GkN t t'‖ =
      ‖((Windows.finalMatrix ℤ (Families.ds l) α (2 ^ (N + k)) s s' : ℤ) : ℤ_[2])‖ := by
    have hV := Smith2.V1 hl hα (Nat.one_le_two_pow) hη (fun m _ => z m) GkN hGN s s'
    by_cases hD : Windows.Dset (Families.ds l) s' ⊆ Windows.Dset (Families.ds l) s
    · exact hV.2 hD
    · rw [hV.1.2 hD, (Windows.theorem_D_ii (Families.ds l) α (2 ^ (N + k)) (by omega) s s').2 hD]
      simp
  -- the estimate
  have ea := norm_le_of_eq_pow_mul hw
  have eb := norm_le_of_eq_pow_mul hv'
  have hp : (2⁻¹ : ℝ) ^ (α + N) ≤ (2⁻¹ : ℝ) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have t1 := norm_sub_norm_le (finalM GkZ t t') (finalM GkN t t')
  have t2 := norm_sub_norm_le (finalM GkN t t') (finalM GkZ t t')
  have t3 := norm_sub_norm_le ((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])
    ((Windows.finalMatrix ℤ (Families.ds l) α (2 ^ (N + k)) s s' : ℤ) : ℤ_[2])
  have t4 := norm_sub_norm_le ((Windows.finalMatrix ℤ (Families.ds l) α (2 ^ (N + k)) s s' : ℤ) : ℤ_[2])
    ((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])
  rw [norm_sub_rev] at t2 t4
  rw [abs_le]
  constructor <;> linarith

/-- **(V2)** of `C49b_congruence_and_the_data_at_zero.md` (zeros): under (H0),
`finalM GkZ (cs s) (cs s') = 0 ↔ Windows.finalMatrix ℤ (Families.ds l) α 0 s s' = 0`. -/
theorem V2 {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ)
    (s s' : Fin (2 ^ Dance.mCount (Families.ds l))) :
    finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l)) s)
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s') = 0 ↔
      Windows.finalMatrix ℤ (Families.ds l) α 0 s s' = 0 := by
  rw [← norm_eq_zero, V1 hl hα hη z GkZ hG s s', norm_eq_zero, Int.cast_eq_zero]

/-- **(V3)** of `C49b_congruence_and_the_data_at_zero.md` (the row of `∅`): under (H0), for every
`s'`, `finalM GkZ (cs (DanceSmith.sl (Families.ds l) (DanceSmith.zeroPos (Families.ds l)))) (cs s')
= 0`; hence the matrix `X s s' := finalM GkZ (cs s) (cs s')` on
`Fin (2 ^ Dance.mCount (Families.ds l))` has `X.det = 0`. -/
theorem V3 {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ) :
    (∀ s' : Fin (2 ^ Dance.mCount (Families.ds l)),
      finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l))
          (DanceSmith.sl (Families.ds l) (DanceSmith.zeroPos (Families.ds l))))
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s') = 0) ∧
    Matrix.det (fun s s' : Fin (2 ^ Dance.mCount (Families.ds l)) =>
      finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l)) s)
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s')) = 0 := by
  have hrow : ∀ s' : Fin (2 ^ Dance.mCount (Families.ds l)),
      finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l))
          (DanceSmith.sl (Families.ds l) (DanceSmith.zeroPos (Families.ds l))))
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s') = 0 := fun s' =>
    (V2 hl hα hη z GkZ hG _ s').2 (DanceSmith.final_row_zero _ α (by omega) s')
  exact ⟨hrow, Matrix.det_eq_zero_of_row_eq_zero _ hrow⟩

end ContZero
