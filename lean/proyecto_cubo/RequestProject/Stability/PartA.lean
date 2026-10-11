module

public import RequestProject.Stability.Defs
public import RequestProject.Stability.PartS

/-!
# `C44_stability_and_rigidity.md`, Part A — the matrix `𝒜` of the word

Namespace `Stability`. For `ds : List Bool` with `k := ds.length ≥ 1`, on
`Fin (Dance.slots ds 1)`, with `D_s := Windows.Dset ds s`:

* (A1) `A1` (and its pieces `Dset_injective`, `nest_refl`, `nest_trans`, `nuA_self`,
  `nuA_triangle`, `delta_nonneg`);
* (A2) `A2` (`norm_Amat`, `Amat_self`);
* (A3) `A3`.
-/

@[expose] public section

noncomputable section

namespace Stability

open Matrix Finset

variable {ds : List Bool}

lemma Dset_subset_Ids (ds : List Bool) (s : ℕ) : Windows.Dset ds s ⊆ Windows.Ids ds :=
  Finset.filter_subset _ _

lemma lt_of_mem_Dset {ds : List Bool} {s t : ℕ} (h : t ∈ Windows.Dset ds s) : t < ds.length :=
  Windows.lt_of_mem_Ids (Dset_subset_Ids ds s h)

/-- (A1) of `C44_stability_and_rigidity.md`: `s ↦ D_s` is injective on
`Fin (Dance.slots ds 1)` (C14: the dancers are injective on `{0, …, 2^m − 1}`). -/
theorem Dset_injective (ds : List Bool) :
    Function.Injective (fun s : Fin (Dance.slots ds 1) => Windows.Dset ds s) := by
  intro a b hab
  have hs : Dance.slots ds 1 = 2 ^ (Windows.Ids ds).card := by
    rw [Dance.slots_eq, Windows.card_Ids, one_mul]
  have ha : (a : ℕ) < 2 ^ (Windows.Ids ds).card := hs ▸ a.isLt
  have hb : (b : ℕ) < 2 ^ (Windows.Ids ds).card := hs ▸ b.isLt
  simp only [Windows.Dset_eq_Dlab] at hab
  exact Fin.ext (Windows.Dlab_inj _ ha hb hab)

/-- (A1) of `C44_stability_and_rigidity.md`: `nest ds` is reflexive. -/
theorem nest_refl (s : Fin (Dance.slots ds 1)) : nest ds s s := subset_refl _

/-- (A1) of `C44_stability_and_rigidity.md`: `nest ds` is transitive. -/
theorem nest_trans {s u t : Fin (Dance.slots ds 1)} (h1 : nest ds s u) (h2 : nest ds u t) :
    nest ds s t := Finset.Subset.trans h2 h1

/-- (A1) of `C44_stability_and_rigidity.md`: `nuA ds s s = 0`. -/
theorem nuA_self (s : Fin (Dance.slots ds 1)) : nuA ds s s = 0 := by
  simp [nuA, Rulers.delta]

/-- (A1) of `C44_stability_and_rigidity.md`: `Rulers.delta k Δ ≥ 0` for `Δ ⊆ Ids ds`
(`k = ds.length ≥ 1`), so `toNat` loses nothing. -/
theorem delta_nonneg (hk : 1 ≤ ds.length) {Δ : Finset ℕ} (hΔ : Δ ⊆ Windows.Ids ds) :
    0 ≤ Rulers.delta ds.length Δ := by
  rw [← (Deficit.lemma_4_5 hk (fun t ht => Windows.lt_of_mem_Ids ht) hΔ).2]
  exact Int.natCast_nonneg _

lemma nuA_cast (hk : 1 ≤ ds.length) (s s' : Fin (Dance.slots ds 1)) :
    (nuA ds s s' : ℤ) = Rulers.delta ds.length (Windows.Dset ds s \ Windows.Dset ds s') :=
  Int.toNat_of_nonneg (delta_nonneg hk (sdiff_subset.trans (Dset_subset_Ids ds s)))

/-- (A1) of `C44_stability_and_rigidity.md`: `nuA ds s t ≤ nuA ds s u + nuA ds u t` whenever
`nest ds s u` and `nest ds u t` (from C10 `Deficit.A4_subadditivity`). -/
theorem nuA_triangle (hk : 1 ≤ ds.length) {s u t : Fin (Dance.slots ds 1)} (h1 : nest ds s u)
    (h2 : nest ds u t) : nuA ds s t ≤ nuA ds s u + nuA ds u t := by
  have hu : (Windows.Dset ds s \ Windows.Dset ds u) ∪ (Windows.Dset ds u \ Windows.Dset ds t) =
      Windows.Dset ds s \ Windows.Dset ds t := sdiff_union_sdiff_cancel h1 h2
  have hd : Disjoint (Windows.Dset ds s \ Windows.Dset ds u)
      (Windows.Dset ds u \ Windows.Dset ds t) :=
    Finset.disjoint_of_subset_right sdiff_subset disjoint_sdiff_self_left
  have c1 := nuA_cast hk s u
  have c2 := nuA_cast hk u t
  have c3 := nuA_cast hk s t
  rcases (Windows.Dset ds s \ Windows.Dset ds u).eq_empty_or_nonempty with e1 | n1
  · rw [e1, empty_union] at hu
    rw [← hu] at c3
    omega
  rcases (Windows.Dset ds u \ Windows.Dset ds t).eq_empty_or_nonempty with e2 | n2
  · rw [e2, union_empty] at hu
    rw [← hu] at c3
    omega
  have h := (Deficit.A4_subadditivity n1 n2 hd (fun x hx => lt_of_mem_Dset (sdiff_subset hx))
    (fun x hx => lt_of_mem_Dset (sdiff_subset hx))).2
  have h' := (Deficit.A4_subadditivity n1 n2 hd (fun x hx => lt_of_mem_Dset (sdiff_subset hx))
    (fun x hx => lt_of_mem_Dset (sdiff_subset hx))).1
  rw [hu] at h'
  omega

/-- **(A1)** of `C44_stability_and_rigidity.md`, Part A, collected: for `k = ds.length ≥ 1`,
`s ↦ D_s` is injective on `Fin (Dance.slots ds 1)`; `nest ds` is reflexive and transitive;
`nuA ds s s = 0`; `nuA ds s t ≤ nuA ds s u + nuA ds u t` whenever `nest ds s u` and
`nest ds u t`; and `Rulers.delta k Δ ≥ 0` for `Δ ⊆ Ids ds`. -/
theorem A1 (hk : 1 ≤ ds.length) :
    Function.Injective (fun s : Fin (Dance.slots ds 1) => Windows.Dset ds s) ∧
    (∀ s, nest ds s s) ∧ (∀ s u t, nest ds s u → nest ds u t → nest ds s t) ∧
    (∀ s, nuA ds s s = 0) ∧
    (∀ s u t, nest ds s u → nest ds u t → nuA ds s t ≤ nuA ds s u + nuA ds u t) ∧
    (∀ Δ ⊆ Windows.Ids ds, 0 ≤ Rulers.delta ds.length Δ) :=
  ⟨Dset_injective ds, nest_refl, fun _ _ _ => nest_trans, nuA_self,
    fun _ _ _ => nuA_triangle hk, fun _ => delta_nonneg hk⟩

/-- (A2) of `C44_stability_and_rigidity.md`: `nest ds s s' → ‖Amat ds s s'‖ = 2^{−nuA ds s s'}`
(from C10 `Deficit.lemma_4_5`). -/
theorem norm_Amat (hk : 1 ≤ ds.length) {s s' : Fin (Dance.slots ds 1)} (h : nest ds s s') :
    ‖Amat ds s s'‖ = (2 : ℝ) ^ (-(nuA ds s s' : ℤ)) := by
  have hΔ : Windows.Dset ds s \ Windows.Dset ds s' ⊆ Windows.Ids ds :=
    sdiff_subset.trans (Dset_subset_Ids ds s)
  obtain ⟨hne, hv⟩ := Deficit.lemma_4_5 hk (fun t ht => Windows.lt_of_mem_Ids ht) hΔ
  simp only [Amat, of_apply, if_pos h]
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hne), Padic.valuation_intCast,
    nuA_cast hk, ← hv]
  norm_num

/-- (A2) of `C44_stability_and_rigidity.md`: `Amat ds s s = 1` (C10 `Deficit.lemma_4_5_empty`). -/
theorem Amat_self (hk : 1 ≤ ds.length) (s : Fin (Dance.slots ds 1)) : Amat ds s s = 1 := by
  simp only [Amat, of_apply, if_pos (nest_refl s), sdiff_self, bot_eq_empty,
    Deficit.lemma_4_5_empty hk, Int.cast_one]

/-- **(A2)** of `C44_stability_and_rigidity.md`, Part A, collected: for `k = ds.length ≥ 1`,
`nest ds s s' → ‖Amat ds s s'‖ = 2 ^ (−nuA ds s s')`, and `Amat ds s s = 1`. -/
theorem A2 (hk : 1 ≤ ds.length) :
    (∀ s s', nest ds s s' → ‖Amat ds s s'‖ = (2 : ℝ) ^ (-(nuA ds s s' : ℤ))) ∧
    (∀ s, Amat ds s s = 1) :=
  ⟨fun _ _ => norm_Amat hk, Amat_self hk⟩

lemma Amat_mem_Wt (hk : 1 ≤ ds.length) : Amat ds ∈ Wt (nest ds) (nuA ds) 0 := by
  intro s s'
  refine ⟨fun h => by simp [Amat, h], ?_⟩
  by_cases h : nest ds s s'
  · rw [norm_Amat hk h, add_zero]
  · simp only [Amat, of_apply, if_neg h, norm_zero]; positivity

/-- The strictly nested part `N = 1 − 𝒜`: its powers decrease the cardinality. -/
lemma pow_one_sub_Amat_eq_zero (hk : 1 ≤ ds.length) (j : ℕ) (s s' : Fin (Dance.slots ds 1))
    (h : ((1 - Amat ds) ^ j) s s' ≠ 0) :
    (Windows.Dset ds s').card + j ≤ (Windows.Dset ds s).card := by
  induction j generalizing s' with
  | zero =>
    rw [pow_zero] at h
    by_cases hs : s = s'
    · subst hs; omega
    · exact absurd (one_apply_ne hs) h
  | succ j ih =>
    rw [pow_succ, mul_apply] at h
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : ((1 - Amat ds) ^ j) s u ≠ 0 := left_ne_zero_of_mul hu
    have h2 : (1 - Amat ds) u s' ≠ 0 := right_ne_zero_of_mul hu
    have hne : u ≠ s' := by
      rintro rfl; apply h2; rw [sub_apply, one_apply_eq, Amat_self hk, sub_self]
    have hn : nest ds u s' := by
      by_contra hn; apply h2
      rw [sub_apply, one_apply_ne hne]; simp [Amat, hn]
    have hlt : (Windows.Dset ds s').card < (Windows.Dset ds u).card := by
      apply Finset.card_lt_card
      refine Finset.ssubset_iff_subset_ne.2 ⟨hn, fun he => hne ?_⟩
      exact (Dset_injective ds he.symm)
    have := ih u h1
    omega

/-- **(A3)** of `C44_stability_and_rigidity.md`, Part A: for `k = ds.length ≥ 1`,
`Amat ds ∈ Wt (nest ds) (nuA ds) 0`, and there is `B ∈ Wt (nest ds) (nuA ds) 0` with
`Amat ds * B = 1`. -/
theorem A3 (hk : 1 ≤ ds.length) :
    Amat ds ∈ Wt (nest ds) (nuA ds) 0 ∧
      ∃ B ∈ Wt (nest ds) (nuA ds) 0, Amat ds * B = 1 := by
  refine ⟨Amat_mem_Wt hk, ?_⟩
  set N := 1 - Amat ds
  have hrefl : ∀ s, nest ds s s := nest_refl
  have htrans : ∀ s u t, nest ds s u → nest ds u t → nest ds s t := fun _ _ _ => nest_trans
  have hN : N ∈ Wt (nest ds) (nuA ds) 0 :=
    sub_mem_Wt (one_mem_Wt hrefl nuA_self) (Amat_mem_Wt hk)
  have hnil : N ^ (ds.length + 1) = 0 := by
    ext s s'
    by_contra h
    have h1 := pow_one_sub_Amat_eq_zero hk _ s s' h
    have h2 : (Windows.Dset ds s).card ≤ ds.length := by
      calc (Windows.Dset ds s).card ≤ (range ds.length).card :=
            card_le_card (fun t ht => mem_range.2 (lt_of_mem_Dset ht))
        _ = ds.length := card_range _
    rw [zero_apply] at h
    omega
  refine ⟨∑ j ∈ range (ds.length + 1), N ^ j,
    sum_mem_Wt _ _ (fun j _ => pow_mem_Wt hrefl htrans nuA_self
      (fun _ _ _ => nuA_triangle hk) hN j), ?_⟩
  have hA : Amat ds = 1 - N := by simp [N]
  rw [hA, mul_neg_geom_sum, hnil, sub_zero]

end Stability
