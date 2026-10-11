module

public import RequestProject.DanceSmith.All

/-!
# `C46_smith_form_and_cokernel_over_Z2.md`, Part G — the Smith form is decided by the support and
# the entry valuations (C15 (S3), general form)

(G1) `G1`; (G2) `G2`.

The proof of C15 (S3) uses the matrix only through its entries; it is re-run here for any integer
matrix `M'` with the support and the entry valuations of (G1): `Mo' := M'.submatrix sl sl`
(C15 `DanceSmith.P1`: `Dset ds (sl p) = dancer I p`), the floor `DanceSmith.floor_minor`, the
ceiling `DanceSmith.golden_ceiling`, the conclusion `DanceSmith.smith_of_bounds`, and the transfer
back along `DanceSmith.slPerm`.
-/

@[expose] public section

namespace Smith2

open Finset Matrix TheoremF Windows DanceSmith

section Rerun

variable (ds : List Bool) (α i : ℕ)
  (Mo' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ)

variable {ds α i Mo'}

/-- Proof of (G1) of `C46_smith_form_and_cokernel_over_Z2.md`: the floor of C15 for `Mo'`
(re-run of `DanceSmith.S_floor`). -/
lemma G_floor (hα : 1 ≤ α) (hS : ∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q ≠ 0 ∧
        ∃ n : ℕ, (n : ℤ) = Cst ds α i + GoldenMatching.cHat ds.length (Ids ds) α (i - 1)
            (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
          2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q))
    {r : ℕ} (B D : Finset (Fin (2 ^ Dance.mCount ds))) (hB : B.card = r) (hD : D.card = r) :
    (2 : ℤ) ^ ((r : ℤ) * Cst ds α i + ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds),
      AntitonicFit.ifit (2 ^ Dance.mCount ds) (xClk ds α i) j).toNat ∣
      Divisors.minor Mo' r B D := by
  refine floor_minor Mo' (CellFloor.IsCellArrow (Ids ds))
    (fun p q => GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (dancer (Ids ds) p)
      (dancer (Ids ds) q)) (Cst ds α i) _ (fun p q h => ?_) (fun p q h => ?_)
    (fun Rows β hm => ?_) B D hB hD
  · apply (hS p q).1
    intro hsub
    exact h ⟨by rw [two_pow_card_Ids]; exact p.2, by rw [two_pow_card_Ids]; exact q.2, hsub⟩
  · obtain ⟨-, n, hn, h1, -⟩ := (hS p q).2 h.2.2
    simp only
    rw [← hn, Int.toNat_natCast]
    exact ⟨by positivity, h1⟩
  · rw [← two_pow_card_Ids] at hm
    have hfl := CellFloor.theorem_B_floor (hI_Ids ds) (Nat.mod_lt (i - 1) (by positivity))
      (α := (α : ℤ)) (by exact_mod_cast hα) (Houses.r ds.length (i - 1))
      (Houses.r ds.length (i - 1 + 2 ^ ds.length)) hm
    unfold SmithBounds.tailSum at hfl
    have hfl' : ∑ j ∈ Ico (2 ^ #(Ids ds) - r) (2 ^ #(Ids ds)),
        AntitonicFit.ifit (2 ^ #(Ids ds)) (CellFloor.cellClock (Ids ds) ds.length
          ((i - 1) % 2 ^ ds.length) (α : ℤ) (Houses.r ds.length (i - 1))
          (Houses.r ds.length (i - 1 + 2 ^ ds.length))) j ≤
        ∑ a ∈ Rows, CellFloor.cellCost (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
          (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) a (β a) := by
      have h : ((∑ j ∈ Ico (2 ^ #(Ids ds) - r) (2 ^ #(Ids ds)),
          AntitonicFit.ifit (2 ^ #(Ids ds)) (CellFloor.cellClock (Ids ds) ds.length
            ((i - 1) % 2 ^ ds.length) (α : ℤ) (Houses.r ds.length (i - 1))
            (Houses.r ds.length (i - 1 + 2 ^ ds.length))) j : ℤ) : ℝ) ≤
          ((∑ a ∈ Rows, CellFloor.cellCost (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) (α : ℤ)
            (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) a (β a) : ℤ) :
              ℝ) := by
        push_cast; exact hfl
      exact_mod_cast h
    rw [two_pow_card_Ids, ifit_cellClock] at hfl'
    simp only [cellCost_eq_cHat] at hfl'
    exact hfl'

/-- Proof of (G1) of `C46_smith_form_and_cokernel_over_Z2.md`: the ceiling of C15 for `Mo'`
(re-run of `DanceSmith.S_ceil`, through `DanceSmith.golden_ceiling`). -/
lemma G_ceil (hS : ∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q ≠ 0 ∧
        ∃ n : ℕ, (n : ℤ) = Cst ds α i + GoldenMatching.cHat ds.length (Ids ds) α (i - 1)
            (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
          2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q)) {r : ℕ} (hr : r ≤ 2 ^ Dance.mCount ds) :
    Divisors.minor Mo' r (lastSet _ r) (firstSet _ r) ≠ 0 ∧
      (padicValInt 2 (Divisors.minor Mo' r (lastSet _ r) (firstSet _ r)) : ℤ) =
        r * Cst ds α i +
          ∑ j ∈ Ico (2 ^ Dance.mCount ds - r) (2 ^ Dance.mCount ds), xClk ds α i j := by
  set Mz : ℕ → ℕ → ℤ := fun p q =>
    if h : p < 2 ^ Dance.mCount ds ∧ q < 2 ^ Dance.mCount ds then Mo' ⟨p, h.1⟩ ⟨q, h.2⟩ else 0
  have hMz : ∀ p q : Fin (2 ^ Dance.mCount ds), Mz p q = Mo' p q := fun p q => by
    simp [Mz, p.2, q.2]
  set Mf : Finset ℕ → Finset ℕ → ℤ := fun a b =>
    Mz (GoldenMatching.rank (Ids ds) a) (GoldenMatching.rank (Ids ds) b)
  have hrk : ∀ {a}, a ⊆ Ids ds → GoldenMatching.rank (Ids ds) a < 2 ^ Dance.mCount ds :=
      fun ha => by
    rw [← two_pow_card_Ids]; exact GoldenMatching.rank_lt ha
  have hMf : ∀ {a b} (ha : a ⊆ Ids ds) (hb : b ⊆ Ids ds),
      Mf a b = Mo' ⟨_, hrk ha⟩ ⟨_, hrk hb⟩ := fun ha hb =>
    hMz ⟨_, hrk ha⟩ ⟨_, hrk hb⟩
  obtain ⟨n, hn, h1, h2⟩ := golden_ceiling ds.length (hI_Ids ds) (α : ℤ) (i - 1) (Cst ds α i) Mf
    (fun a b ha hb hab => by
      rw [hMf ha hb]
      exact (hS _ _).1 (by rw [dancer_rank ha, dancer_rank hb]; exact hab))
    (fun a b hba ha => by
      have hb := hba.trans ha
      rw [hMf ha hb]
      obtain ⟨-, n, hn, h⟩ := (hS ⟨_, hrk ha⟩ ⟨_, hrk hb⟩).2
        (by simp only; rw [dancer_rank ha, dancer_rank hb]; exact hba)
      simp only [dancer_rank ha, dancer_rank hb] at hn
      exact ⟨n, hn, h⟩)
    (r := r) (by rw [two_pow_card_Ids]; exact hr)
  rw [two_pow_card_Ids] at hn h1 h2
  have hmat : (Matrix.of fun i' j : Fin r =>
        Mf (dancer (Ids ds) (2 ^ Dance.mCount ds - r + i')) (dancer (Ids ds) j)) =
      Matrix.of fun i' j : Fin r => Mo' ⟨2 ^ Dance.mCount ds - r + i', by omega⟩ ⟨j, by omega⟩ := by
    ext i' j
    simp only [Matrix.of_apply, Mf]
    have hi' := i'.2
    have hj' := j.2
    have hp : (2 ^ Dance.mCount ds) - r + i' < 2 ^ #(Ids ds) := by rw [two_pow_card_Ids]; omega
    have hq : (j : ℕ) < 2 ^ #(Ids ds) := by rw [two_pow_card_Ids]; omega
    rw [lemma_0c_rank hp, lemma_0c_rank hq]
    exact hMz ⟨(2 ^ Dance.mCount ds) - r + i', by omega⟩ ⟨j, by omega⟩
  rw [hmat] at h1 h2
  rw [minor_last_first _ hr]
  obtain ⟨h0, hv⟩ := padicValInt_eq_of_exact h1 h2
  refine ⟨h0, ?_⟩
  rw [hv, hn]
  rfl

/-- Proof of (G1) of `C46_smith_form_and_cokernel_over_Z2.md`: the conclusion of C15 for
`Mo'` (re-run of `DanceSmith.S_main`, through `DanceSmith.smith_of_bounds`). -/
lemma G_main (hα : 1 ≤ α) (hS : ∀ p q : Fin (2 ^ Dance.mCount ds),
      (¬ dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q = 0) ∧
      (dancer (Ids ds) q ⊆ dancer (Ids ds) p → Mo' p q ≠ 0 ∧
        ∃ n : ℕ, (n : ℤ) = Cst ds α i + GoldenMatching.cHat ds.length (Ids ds) α (i - 1)
            (dancer (Ids ds) p) (dancer (Ids ds) q) ∧
          2 ^ n ∣ Mo' p q ∧ ¬ 2 ^ (n + 1) ∣ Mo' p q)) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds,
          (E j : ℤ) = Cst ds α i + yHat ds α i (2 ^ Dance.mCount ds - 1 - j)) ∧
        ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧ P * Mo' * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds then u j * 2 ^ E j else 0) :=
  (smith_of_bounds Mo' le_rfl (xClk ds α i) (Cst ds α i)
    (fun _ _ B D hB hD => G_floor hα hS B D hB hD)
    (fun r hr => ⟨lastSet _ r, firstSet _ r, card_lastSet hr, card_firstSet hr,
      (G_ceil hS hr).1, (G_ceil hS hr).2.le⟩)
    (fun h => absurd h (lt_irrefl _))).2

end Rerun

/-- **(G1)** of `C46_smith_form_and_cokernel_over_Z2.md` (C15 (S3), general form): let `ds` with
`1 ≤ ds.length`, `1 ≤ α`, `1 ≤ i`, and `M'` an integer matrix on `Fin (2 ^ m)` such that for all
`s, s'`: if `¬ Dset ds s' ⊆ Dset ds s` then `M' s s' = 0`; if `Dset ds s' ⊆ Dset ds s` then
`M' s s' ≠ 0` and there is `n : ℕ` with
`(n : ℤ) = Cst ds α i + cHat k I α (i − 1) (Dset ds s) (Dset ds s')`, `2^n ∣ M' s s'` and
`¬ 2^(n+1) ∣ M' s s'`. Then the conclusion of `DanceSmith.S3` holds for `M'`: there are `P, Q`
over `ℤ` with odd determinants, odd integers `u j` and `E : ℕ → ℕ` with
`(E j : ℤ) = Cst ds α i + yHat ds α i (N − 1 − j)` for `j < N`, and
`P * M' * Q = diagonal (fun j => u j * 2 ^ E j)`. (The hypotheses `1 ≤ ds.length` and `1 ≤ i`
turn out not to be needed by this re-run, since the entry valuations are given; they are kept, as
in the file.) -/
theorem G1 (ds : List Bool) (_hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (_hi : 1 ≤ i)
    (M' : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ)
    (hM : ∀ s s' : Fin (2 ^ Dance.mCount ds),
      (¬ Dset ds s' ⊆ Dset ds s → M' s s' = 0) ∧
      (Dset ds s' ⊆ Dset ds s → M' s s' ≠ 0 ∧
        ∃ n : ℕ, (n : ℤ) = Cst ds α i +
            GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (Dset ds s) (Dset ds s') ∧
          2 ^ n ∣ M' s s' ∧ ¬ 2 ^ (n + 1) ∣ M' s s')) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ,
      Odd P.det ∧ Odd Q.det ∧ ∃ u : ℕ → ℤ, (∀ j, Odd (u j)) ∧
        ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds,
            (E j : ℤ) = Cst ds α i + yHat ds α i (2 ^ Dance.mCount ds - 1 - j)) ∧
          P * M' * Q = diagonal (fun j : Fin (2 ^ Dance.mCount ds) => u j * 2 ^ E j) := by
  have hP1 := (P1 ds).2.2
  have hS := fun p q : Fin (2 ^ Dance.mCount ds) => by
    have h := hM (sl ds p) (sl ds q)
    rw [hP1 p, hP1 q] at h
    exact h
  obtain ⟨P, Q, hP, hQ, E, hE, u, hu, hD⟩ :=
    G_main (Mo' := M'.submatrix (sl ds) (sl ds)) hα hS
  refine ⟨P * (slPerm ds).permMatrix ℤ, Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ * Q, ?_, ?_, u, hu,
    E, hE, ?_⟩
  · rw [det_mul]; exact hP.mul (odd_det_permMatrix _)
  · rw [det_mul]; exact (odd_det_permMatrix _).mul hQ
  · have hsub : M'.submatrix (sl ds) (sl ds) =
        (slPerm ds).permMatrix ℤ * M' * Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ :=
      submatrix_perm_eq (slPerm ds) M'
    rw [hsub] at hD
    rw [show P * (slPerm ds).permMatrix ℤ * M' * (Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹ * Q) =
        P * ((slPerm ds).permMatrix ℤ * M' * Equiv.Perm.permMatrix ℤ (slPerm ds)⁻¹) * Q by
      simp only [Matrix.mul_assoc], hD]
    congr 1
    funext j
    exact if_pos j.2

/-- **(G2)** of `C46_smith_form_and_cokernel_over_Z2.md`: for `1 ≤ ds.length`, `1 ≤ α`, `1 ≤ i`,
`Windows.finalMatrix ℤ ds α i` satisfies the hypothesis of (G1) (by C15 (S1) and (P1)). -/
theorem G2 (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∀ s s' : Fin (2 ^ Dance.mCount ds),
      (¬ Dset ds s' ⊆ Dset ds s → finalMatrix ℤ ds α i s s' = 0) ∧
      (Dset ds s' ⊆ Dset ds s → finalMatrix ℤ ds α i s s' ≠ 0 ∧
        ∃ n : ℕ, (n : ℤ) = Cst ds α i +
            GoldenMatching.cHat ds.length (Ids ds) α (i - 1) (Dset ds s) (Dset ds s') ∧
          2 ^ n ∣ finalMatrix ℤ ds α i s s' ∧ ¬ 2 ^ (n + 1) ∣ finalMatrix ℤ ds α i s s') := by
  intro s s'
  have h := S1 ds hk α i hα hi (sl ds s) (sl ds s')
  have hP1 := (P1 ds).2.2
  rw [← hP1, ← hP1, sl_sl, sl_sl] at h
  have hMo : Mo ds α i (sl ds s) (sl ds s') = finalMatrix ℤ ds α i s s' := by
    simp only [Mo, submatrix_apply, sl_sl]
  rw [hMo] at h
  exact h

end Smith2
