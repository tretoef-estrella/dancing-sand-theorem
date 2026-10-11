module

public import RequestProject.ZeroSmith.Defs

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`, Part G — the Smith form at `i = 0` is decided by
# the data

(G1) `G1`; (G2) `G2`.

The proof of C15 (Z3) uses the matrix only through its support, its zero row (the dancer `∅`) and
its entry valuations; it is re-run here for any integer matrix `M'` with `Data0 ds α M'`:
`Mo' := M'.submatrix sl sl` (C15 `DanceSmith.P1`: `Dset ds (sl p) = dancer I p`), the floor
`DanceSmith.floor_minor`, the ceiling `DanceSmith.golden_ceiling`, the conclusion
`DanceSmith.smith_of_bounds`, and the transfer back along `DanceSmith.slPerm`.
-/

@[expose] public section

namespace ZeroSmith

open Finset Matrix TheoremF Windows DanceSmith

section Rerun

variable {ds : List Bool} {α : ℕ}
  {Mo' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ}

/-- Proof of (G1) of `C49c_smith_form_and_cokernel_at_zero.md`: the floor for `i = 0`, for `Mo'`
(re-run of `DanceSmith.Z_floor`). -/
lemma ZG_floor (hα : 1 ≤ α)
    (hS : (∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) p = ∅ → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → dancer (Ids ds) p ≠ ∅ → Mo' p q ≠ 0 ∧ ∃ n : ℕ,
        (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
          (α : ℤ) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
        2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q)))
    {r : ℕ} (B D : Finset (Fin (2 ^ Dance.mCount ds))) (hB : B.card = r) (hD : D.card = r) :
    (2 : ℤ) ^ ((r : ℤ) * ((α : ℤ) * 2 ^ ds.length) +
      ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds),
        AntitonicFit.ifit (2 ^ Dance.mCount ds) (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j
        ).toNat ∣ Divisors.minor Mo' r B D := by
  refine floor_minor Mo' (CellFloor.IsCellArrow (Ids ds))
    (fun p q => Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α p q)
    ((α : ℤ) * 2 ^ ds.length) _ (fun p q h => ?_) (fun p q h => ?_) (fun Rows β hm => ?_) B D hB hD
  · apply (hS p q).1
    intro hsub
    exact h ⟨by rw [two_pow_card_Ids]; exact p.2, by rw [two_pow_card_Ids]; exact q.2, hsub⟩
  · by_cases hp : dancer (Ids ds) p = ∅
    · have hq : (q : ℕ) = p := by
        have h2 := h.2.2
        rw [hp] at h2
        have h3 : dancer (Ids ds) q = dancer (Ids ds) p := by
          rw [hp]; exact subset_empty.1 h2
        exact CellFloor.dancer_inj (by rw [two_pow_card_Ids]; exact q.2)
          (by rw [two_pow_card_Ids]; exact p.2) h3
      simp only [hq, CellFloor.cHat_self, add_zero]
      rw [(hS p q).2.1 hp]
      exact ⟨by positivity, dvd_zero _⟩
    · obtain ⟨-, n, hn, h1, -⟩ := (hS p q).2.2 h.2.2 hp
      simp only [Potential.cHat]
      rw [← hn, Int.toNat_natCast]
      exact ⟨by positivity, h1⟩
  · rw [← two_pow_card_Ids] at hm
    have hfl := CellFloor.theorem_B_floor (hI_Ids ds) (ℓ := 2 ^ ds.length - 1)
      (by have := Nat.two_pow_pos ds.length; omega) (α := (α : ℤ)) (by exact_mod_cast hα) 0 0 hm
    have hcl : CellFloor.cellClock (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) 0 0 =
        xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α := by
      funext p; simp [CellFloor.cellClock]
    have hco : ∀ a b, CellFloor.cellCost (Ids ds) ds.length (2 ^ ds.length - 1) (α : ℤ) 0 0 a b =
        Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α a b := by
      intro a b; simp [CellFloor.cellCost]
    rw [hcl] at hfl
    simp only [hco] at hfl
    unfold SmithBounds.tailSum at hfl
    have h : ((∑ j ∈ Ico (2 ^ #(Ids ds) - r) (2 ^ #(Ids ds)),
        AntitonicFit.ifit (2 ^ #(Ids ds)) (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j : ℤ) :
          ℝ) ≤ ((∑ a ∈ Rows, Potential.cHat (Ids ds) ds.length (2 ^ ds.length - 1) α a (β a) :
            ℤ) : ℝ) := by
      push_cast; exact hfl
    have h' := (Int.cast_le (R := ℝ)).1 h
    rw [two_pow_card_Ids] at h'
    exact h'

/-- Proof of (G1) of `C49c_smith_form_and_cokernel_at_zero.md`: the ceiling for `i = 0`, for
`Mo'` (re-run of `DanceSmith.Z_ceil`, through `DanceSmith.golden_ceiling` with `μ = K − 1`). -/
lemma ZG_ceil
    (hS : (∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) p = ∅ → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → dancer (Ids ds) p ≠ ∅ → Mo' p q ≠ 0 ∧ ∃ n : ℕ,
        (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
          (α : ℤ) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
        2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q))) {r : ℕ} (hr : r ≤ 2 ^ Dance.mCount ds - 1) :
    Divisors.minor Mo' r (lastSet _ r) (firstSet _ r) ≠ 0 ∧
      (padicValInt 2 (Divisors.minor Mo' r (lastSet _ r) (firstSet _ r)) : ℤ) =
        r * ((α : ℤ) * 2 ^ ds.length) +
          ∑ j ∈ Ico (2 ^ Dance.mCount ds - 1 - r) (2 ^ Dance.mCount ds - 1),
            CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α j := by
  have hS' : ∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) p = ∅ → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → dancer (Ids ds) p ≠ ∅ → Mo' p q ≠ 0 ∧ ∃ n : ℕ,
        (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
          (α : ℤ) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
        2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q) := hS
  clear hS
  have hN1 : 1 ≤ (2 ^ Dance.mCount ds) := Nat.one_le_two_pow
  have hNI : 2 ^ #(Ids ds) = (2 ^ Dance.mCount ds) := two_pow_card_Ids ds
  set Mz : ℕ → ℕ → ℤ := fun p q => if h : p < (2 ^ Dance.mCount ds) ∧ q < (2 ^ Dance.mCount ds) then Mo' ⟨p, h.1⟩ ⟨q, h.2⟩ else 0
  have hMz : ∀ p q : Fin (2 ^ Dance.mCount ds), Mz p q = Mo' p q := fun p q => by simp [Mz, p.2, q.2]
  set M' : Finset ℕ → Finset ℕ → ℤ := fun a b =>
    if a = ∅ then (if b = ∅ then (2 : ℤ) ^ (α * 2 ^ ds.length) else 0)
    else Mz (GoldenMatching.rank (Ids ds) a) (GoldenMatching.rank (Ids ds) b) *
      (if b = ∅ then 1 else 2)
  have hrk : ∀ {a}, a ⊆ Ids ds → GoldenMatching.rank (Ids ds) a < (2 ^ Dance.mCount ds) := fun ha => by
    rw [← hNI]; exact GoldenMatching.rank_lt ha
  have hM' : ∀ {a b} (ha : a ⊆ Ids ds) (hb : b ⊆ Ids ds), a ≠ ∅ →
      M' a b = Mo' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ * (if b = ∅ then 1 else 2) := fun ha hb ha0 => by
    simp only [M', if_neg ha0]
    rw [hMz ⟨_, hrk ha⟩ ⟨_, hrk hb⟩]
  have hpow : ∀ n : ℕ, ¬ (2 : ℤ) ^ (n + 1) ∣ 2 ^ n := fun n h => by
    have h1 := Int.le_of_dvd (by positivity) h
    have h2 : (2 : ℤ) ^ n < 2 ^ (n + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨n, hn, h1, h2⟩ := golden_ceiling ds.length (hI_Ids ds) (α : ℤ) (2 ^ ds.length - 1)
    ((α : ℤ) * 2 ^ ds.length) M'
    (fun a b ha hb hab => by
      by_cases ha0 : a = ∅
      · have hb0 : b ≠ ∅ := by rintro rfl; exact hab (empty_subset _)
        simp [M', ha0, hb0]
      · have hab' : ¬ dancer (Ids ds) (GoldenMatching.rank (Ids ds) b) ⊆
            dancer (Ids ds) (GoldenMatching.rank (Ids ds) a) := by
          rw [dancer_rank ha, dancer_rank hb]; exact hab
        rw [hM' ha hb ha0, (hS' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩).1 hab', zero_mul])
    (fun a b hba ha => by
      have hb := hba.trans ha
      rw [cHat_sharp _ (hI_Ids ds) _ ha hb]
      by_cases ha0 : a = ∅
      · subst ha0
        obtain rfl := subset_empty.1 hba
        refine ⟨α * 2 ^ ds.length, by simp [Houses.cHatH, Rulers.gamma], ?_, ?_⟩
        · simp [M']
        · simp only [M', if_pos rfl]; exact hpow _
      · obtain ⟨h0, n, hn, g1, g2⟩ := (hS' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩).2.2
          (by simp only; rw [dancer_rank ha, dancer_rank hb]; exact hba)
          (by simp only; rw [dancer_rank ha]; exact ha0)
        simp only [dancer_rank ha, dancer_rank hb] at hn
        rw [hM' ha hb ha0]
        by_cases hb0 : b = ∅
        · refine ⟨n, by rw [hn, if_pos hb0]; ring, ?_, ?_⟩
          · rw [if_pos hb0, mul_one]; exact g1
          · rw [if_pos hb0, mul_one]; exact g2
        · refine ⟨n + 1, by rw [if_neg hb0]; push_cast; rw [hn]; ring, ?_, ?_⟩
          · rw [if_neg hb0, pow_succ]; exact mul_dvd_mul_right g1 _
          · rw [if_neg hb0, pow_succ]
            intro hd
            exact g2 ((mul_dvd_mul_iff_right two_ne_zero).1 hd))
    (r := r) (by rw [hNI]; omega)
  rw [hNI] at hn h1 h2
  have hmat : (Matrix.of fun i' j : Fin r => M' (dancer (Ids ds) ((2 ^ Dance.mCount ds) - r + i')) (dancer (Ids ds) j)) =
      (Matrix.of fun i' j : Fin r => Mo' ⟨(2 ^ Dance.mCount ds) - r + i', by omega⟩ ⟨j, by omega⟩) *
        diagonal (fun j : Fin r => if (j : ℕ) = 0 then (1 : ℤ) else 2) := by
    ext i' j
    have hi' := i'.2
    have hj' := j.2
    have hp : (2 ^ Dance.mCount ds) - r + i' < 2 ^ #(Ids ds) := by rw [hNI]; omega
    have hq : (j : ℕ) < 2 ^ #(Ids ds) := by rw [hNI]; omega
    rw [mul_diagonal, Matrix.of_apply, Matrix.of_apply,
      hM' (lemma_0a _ _) (lemma_0a _ _) (by rw [Ne, dancer_eq_empty_iff hp]; omega)]
    simp only [lemma_0c_rank hp, lemma_0c_rank hq, dancer_eq_empty_iff hq]
  rw [hmat, det_mul, det_diagonal, prod_scale] at h1 h2
  obtain ⟨hX0, hXv⟩ := padicValInt_eq_of_exact h1 h2
  have hX : (Matrix.of fun i' j : Fin r => Mo' ⟨(2 ^ Dance.mCount ds) - r + i', by omega⟩ ⟨j, by omega⟩).det ≠ 0 :=
    left_ne_zero_of_mul hX0
  rw [padicValInt.mul hX (pow_ne_zero _ two_ne_zero), padicValInt_two_pow] at hXv
  rw [minor_last_first _ (by omega)]
  refine ⟨hX, ?_⟩
  have hsum : ∑ j ∈ Ico ((2 ^ Dance.mCount ds) - r) (2 ^ Dance.mCount ds), GoldenMatching.xVal ds.length (Ids ds) (α : ℤ)
      (2 ^ ds.length - 1) (dancer (Ids ds) j) =
      ∑ j ∈ Ico ((2 ^ Dance.mCount ds) - r) (2 ^ Dance.mCount ds), xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α j + ((r - 1 : ℕ) : ℤ) := by
    rw [← sum_ne_last (by omega) hN1, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_Ico] at hj
    have hj' : j < 2 ^ #(Ids ds) := by rw [hNI]; omega
    rw [xVal_sharp _ (hI_Ids ds) _ (lemma_0a _ _), ← lemma_0d hj']
    have hiff : dancer (Ids ds) (2 ^ #(Ids ds) - 1 - j) = ∅ ↔ j = (2 ^ Dance.mCount ds) - 1 := by
      rw [dancer_eq_empty_iff (by omega), hNI]; omega
    simp only [xHseq, hiff]
  have hsh : ∑ j ∈ Ico ((2 ^ Dance.mCount ds) - 1 - r) ((2 ^ Dance.mCount ds) - 1), CellFloor.xSharp (Ids ds) ds.length
      (2 ^ ds.length - 1) α j = ∑ j ∈ Ico ((2 ^ Dance.mCount ds) - r) (2 ^ Dance.mCount ds), xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α j := by
    simp only [CellFloor.xSharp]
    rw [sum_Ico_add' (fun j => xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α j),
      show (2 ^ Dance.mCount ds) - 1 - r + 1 = (2 ^ Dance.mCount ds) - r by omega, show (2 ^ Dance.mCount ds) - 1 + 1 = (2 ^ Dance.mCount ds) by omega]
  rw [hsh]
  have : ((padicValInt 2 (Matrix.of fun i' j : Fin r =>
      Mo' ⟨(2 ^ Dance.mCount ds) - r + i', by omega⟩ ⟨j, by omega⟩).det : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) = n := by
    exact_mod_cast hXv
  rw [hn, hsum] at this
  linarith

/-- Proof of (G1) of `C49c_smith_form_and_cokernel_at_zero.md`: the conclusion for `i = 0`, for
`Mo'` (re-run of `DanceSmith.Z_main`, through `DanceSmith.smith_of_bounds`). -/
lemma ZG_main (hα : 1 ≤ α) (hne : Ids ds ≠ ∅)
    (hS : (∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) p = ∅ → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → dancer (Ids ds) p ≠ ∅ → Mo' p q ≠ 0 ∧ ∃ n : ℕ,
        (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
          (α : ℤ) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
        2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q))) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
          (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 1 - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧ P * Mo' * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then u j * 2 ^ E j else 0) := by
  have hN1 : 1 ≤ (2 ^ Dance.mCount ds) := Nat.one_le_two_pow
  rw [yHatS_eq]
  refine (smith_of_bounds Mo' (N' := (2 ^ Dance.mCount ds) - 1) (by omega)
    (CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α) ((α : ℤ) * 2 ^ ds.length)
    (fun r hr B D hB hD => ?_)
    (fun r hr => ⟨lastSet _ r, firstSet _ r, card_lastSet (by omega), card_firstSet (by omega),
      (ZG_ceil hS hr).1, (ZG_ceil hS hr).2.le⟩)
    (fun _ B D hB hD => ?_)).2
  · have hsum : ∑ j ∈ Ico ((2 ^ Dance.mCount ds) - 1 - r) ((2 ^ Dance.mCount ds) - 1), AntitonicFit.ifit ((2 ^ Dance.mCount ds) - 1)
        (CellFloor.xSharp (Ids ds) ds.length (2 ^ ds.length - 1) α) j =
        ∑ j ∈ Ico ((2 ^ Dance.mCount ds) - r) (2 ^ Dance.mCount ds), AntitonicFit.ifit (2 ^ Dance.mCount ds)
          (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j := by
      rw [← yHatS_eq]
      rw [sum_congr rfl fun j hj => yHatS_succ ds α hα hne (by simp only [mem_Ico] at hj; omega)]
      rw [sum_Ico_add' (fun j => AntitonicFit.ifit (2 ^ Dance.mCount ds)
          (xHseq (Ids ds) ds.length (2 ^ ds.length - 1) α) j),
        show (2 ^ Dance.mCount ds) - 1 - r + 1 = (2 ^ Dance.mCount ds) - r by omega, show (2 ^ Dance.mCount ds) - 1 + 1 = (2 ^ Dance.mCount ds) by omega]
    rw [hsum]
    exact ZG_floor hα hS B D hB hD
  · have e : (2 ^ Dance.mCount ds) - 1 + 1 = (2 ^ Dance.mCount ds) := by omega
    rw [e] at hB hD ⊢
    rw [eq_univ_of_card B (by simpa using hB), eq_univ_of_card D (by simpa using hD),
      Divisors.minor_univ]
    exact det_eq_zero_of_row_eq_zero (zeroPos ds) fun q => (hS _ q).2.1 (dancer_zero _)

end Rerun

/-- `Data0` transported to the o-order along `DanceSmith.P1` (proof of (G1) of
`C49c_smith_form_and_cokernel_at_zero.md`). -/
lemma dataO_of_data0 {ds : List Bool} {α : ℕ}
    {M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ}
    (hM : Data0 ds α M') :
    (∀ p q : Fin (2 ^ Dance.mCount ds),
        (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → M'.submatrix (sl ds) (sl ds) p q = 0) ∧
        (dancer (Ids ds) p = ∅ → M'.submatrix (sl ds) (sl ds) p q = 0) ∧
        (dancer (Ids ds) q ⊆ dancer (Ids ds) p → dancer (Ids ds) p ≠ ∅ → M'.submatrix (sl ds) (sl ds) p q ≠ 0 ∧ ∃ n : ℕ,
          (n : ℤ) = (α : ℤ) * 2 ^ ds.length + Houses.cHatH (Ids ds) ds.length (2 ^ ds.length - 1)
            (α : ℤ) (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
          2 ^ n ∣ M'.submatrix (sl ds) (sl ds) p q ∧ ¬ 2 ^ (n + 1) ∣ M'.submatrix (sl ds) (sl ds) p q)) := by
  intro p q
  have h := hM (sl ds p) (sl ds q)
  rw [(P1 ds).2.2 p, (P1 ds).2.2 q] at h
  exact h

/-- **(G1)** of `C49c_smith_form_and_cokernel_at_zero.md` (C15 (Z3), general form): for `ds` with
`1 ≤ ds.length`, `1 ≤ α`, `Ids ds ≠ ∅` and `M'` with `Data0 ds α M'`, there are
`P Q : Matrix (Fin N) (Fin N) ℤ` with `Odd P.det`, `Odd Q.det`, `u : ℕ → ℤ` with every `u j` odd,
and `E : ℕ → ℕ` with `(E j : ℤ) = α 2^k + yHatS ds α (N − 2 − j)` for `j < N − 1`, such that
`P * M' * Q = diagonal (fun j => if j < N − 1 then u j * 2 ^ E j else 0)`. (The hypothesis
`1 ≤ ds.length` turns out not to be needed by this re-run, since the entry valuations are given;
it is kept, as in the file.) -/
theorem G1 (ds : List Bool) (_hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅)
    (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ)
    (hM : Data0 ds α M') :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
            (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 2 - j)) ∧
          P * M' * Q = diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then u j * 2 ^ E j else 0) := by
  obtain ⟨P, Q, hP, hQ, E, hE, u, hu, hD⟩ := ZG_main hα hne (dataO_of_data0 hM)
  refine ⟨P * (slPerm ds).permMatrix ℤ, Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ * Q, ?_, ?_, u, hu,
    E, fun j hj => ?_, ?_⟩
  · rw [det_mul]; exact hP.mul (odd_det_permMatrix _)
  · rw [det_mul]; exact (odd_det_permMatrix _).mul hQ
  · rw [hE j hj, show 2 ^ Dance.mCount ds - 1 - 1 - j = 2 ^ Dance.mCount ds - 2 - j by omega]
  · have hsub : M'.submatrix (sl ds) (sl ds) =
        (slPerm ds).permMatrix ℤ * M' * Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ :=
      submatrix_perm_eq (slPerm ds) M'
    rw [hsub] at hD
    rw [← hD]
    simp only [Matrix.mul_assoc]

/-- **(G2)** of `C49c_smith_form_and_cokernel_at_zero.md`: for `1 ≤ ds.length` and `1 ≤ α`,
`Data0 ds α (Windows.finalMatrix ℤ ds α 0)` (C15 `Mo_off`/`theorem_D_ii`, `final_row_zero` and
`Z_val`, read in the slot order through `P1` and `sl_sl`). -/
theorem G2 (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) :
    Data0 ds α (finalMatrix ℤ ds α 0) := by
  intro s s'
  have hP1 := (P1 ds).2.2
  have hDs : Dset ds s = dancer (Ids ds) (sl ds s) := by rw [← hP1, sl_sl]
  have hDs' : Dset ds s' = dancer (Ids ds) (sl ds s') := by rw [← hP1, sl_sl]
  refine ⟨fun h => (theorem_D_ii ds α 0 hα s s').2 h, fun h => ?_, fun hsub hne => ?_⟩
  · have h0 : ((sl ds s : Fin _) : ℕ) = 0 := by
      rw [hDs] at h
      exact (dancer_eq_empty_iff (by rw [two_pow_card_Ids]; exact (sl ds s).2)).1 h
    have hs : s = sl ds (zeroPos ds) := by
      rw [← sl_sl ds s]; congr 1; exact Fin.ext h0
    rw [hs]
    exact final_row_zero ds α hα s'
  · have hp : ((sl ds s : Fin _) : ℕ) ≠ 0 := by
      intro h0
      apply hne
      rw [hDs, h0]
      exact dancer_zero _
    rw [hDs, hDs'] at hsub
    obtain ⟨h0, hv⟩ := Z_val ds hk α hα (sl ds s) (sl ds s') hp hsub
    have hMo : Mo ds α 0 (sl ds s) (sl ds s') = finalMatrix ℤ ds α 0 s s' := by
      simp only [Mo, submatrix_apply, sl_sl]
    rw [hMo] at h0 hv
    refine ⟨h0, padicValInt 2 (finalMatrix ℤ ds α 0 s s'), ?_, two_pow_padicValInt_dvd _,
      not_two_pow_succ_dvd h0⟩
    rw [hv, hDs, hDs']
    rfl

end ZeroSmith
