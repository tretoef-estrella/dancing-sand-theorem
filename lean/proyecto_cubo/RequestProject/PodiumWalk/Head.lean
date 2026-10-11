module

public import RequestProject.PodiumWalk.Walk
public import RequestProject.FamilyGroup.All
public import RequestProject.MainTheorem.All

/-!
# Part H and Part C of `C35b_the_podium_walk.md` (step (H) and Proposition 9.6)

Encodings (namespace `PodiumWalk`).  Nothing is redefined.  For a digit list `ds`,
`k = ds.length`, `I = Windows.Ids ds`, `s = I.card = Dance.mCount ds`, `N = 2 ^ Dance.mCount ds`;
the pooled clocks are C16 `FamilyGroup.yPool ds i`, the raw clocks are C3
`Rulers.clock k I i (TheoremF.dancer I q)`, the family `λ` is `ds = Families.ds lam` (C32), and
`λ = Rulers.lam k I` by C33 `S1_lam`.  A sum over `q < 2 ^ l` is a sum over `Finset.range (2 ^ l)`;
the subsets `D ⊆ P_l` are the elements of `(Podium.P I l).powerset` (C35).

The general statements (`*_ds`) hold for every digit list; the statements of the file, for the
family `λ`, are `H1`, `H2`, `C1`.  The hypothesis `λ ≥ 1` of the file is not used.
-/

@[expose] public section

namespace PodiumWalk

open Finset AntitonicFit TheoremF Potential Windows

/-- The raw clocks are the clocks `x` of C15 plus a constant (C3 `proposition_5_3`; proof of
Part H of `C35b_the_podium_walk.md`). -/
lemma clock_eq_xClk (ds : List Bool) (i : ℕ) (hi : 1 ≤ i) (j : ℕ) :
    Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j) =
      DanceSmith.xClk ds 1 i j + ((ds.length : ℤ) + DanceSmith.Cst ds 1 i) := by
  rw [Rulers.proposition_5_3 (fun t ht => lt_of_mem_Ids ht) (lemma_0a _ j) i hi]
  simp only [DanceSmith.xClk, DanceSmith.Cst, Rulers.xD, GoldenMatching.xVal, Nat.cast_one]
  ring

/-- The pooled clocks at a shift `i ≥ 1` (proof of Part H of `C35b_the_podium_walk.md`):
the real fit of the raw clocks is `ŷ_i` (an integer sequence), and
`ŷ_i(p) = k + C + ŷ_H(p) + δ(p)` with `H = (I, k, (i − 1) mod K, 1)` and `δ` the shift of the
penalty cell (C9 `lemma_7_9_I2`, C15 `cellClock_eq_xClk`, C16 `R1`). -/
lemma pool_facts (ds : List Bool) (i : ℕ) (hi : 1 ≤ i) :
    (∀ p < 2 ^ Dance.mCount ds,
      fit (2 ^ Dance.mCount ds)
        (toR (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j))) p =
        (FamilyGroup.yPool ds i p : ℝ)) ∧
    (∀ p < 2 ^ Dance.mCount ds, FamilyGroup.yPool ds i p =
      (ds.length : ℤ) + DanceSmith.Cst ds 1 i +
        (yhat (Ids ds) ds.length ((i - 1) % 2 ^ ds.length) 1 p +
          CellFloor.cellShift (Ids ds) ds.length ((i - 1) % 2 ^ ds.length)
            (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length)) p)) := by
  set N := 2 ^ Dance.mCount ds with hN
  have hNI : 2 ^ #(Ids ds) = N := DanceSmith.two_pow_card_Ids ds
  set C : ℤ := (ds.length : ℤ) + DanceSmith.Cst ds 1 i with hC
  have hI2 := CellFloor.lemma_7_9_I2 (DanceSmith.hI_Ids ds)
    (Nat.mod_lt (i - 1) (by positivity : 0 < 2 ^ ds.length)) (α := (((1 : ℕ) : ℤ)))
    (by norm_num) (Houses.r ds.length (i - 1)) (Houses.r ds.length (i - 1 + 2 ^ ds.length))
  rw [hNI] at hI2
  have hyHat : ∀ p < N, DanceSmith.yHat ds 1 i p =
      AntitonicFit.ifit N (CellFloor.cellClock (Ids ds) ds.length ((i - 1) % 2 ^ ds.length)
        (((1 : ℕ) : ℤ)) (Houses.r ds.length (i - 1))
        (Houses.r ds.length (i - 1 + 2 ^ ds.length))) p := fun p _ => by
    rw [DanceSmith.ifit_cellClock]
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have e1 : toR (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j)) =
        fun j => toR (DanceSmith.xClk ds 1 i) j + (C : ℝ) := by
      funext j; simp [toR, clock_eq_xClk ds i hi j, hC]
    have e2 : fit N (toR (DanceSmith.xClk ds 1 i)) =
        fit N (toR (CellFloor.cellClock (Ids ds) ds.length ((i - 1) % 2 ^ ds.length)
          (((1 : ℕ) : ℤ)) (Houses.r ds.length (i - 1))
          (Houses.r ds.length (i - 1 + 2 ^ ds.length)))) :=
      fit_congr fun j hj => by simp only [toR]; rw [DanceSmith.cellClock_eq_xClk ds 1 i hj]
    rw [e1, FamilyGroup.fit_add_const N _ _ p hp, e2, hI2.2.1 p hp, ← hyHat p hp,
      ← (FamilyGroup.R1 ds i hi p hp).2, hC]
    push_cast
    ring
  · rw [← (FamilyGroup.R1 ds i hi p hp).2, hyHat p hp, hI2.1 p hp]
    simp only [CellFloor.cellShift, Nat.cast_one, hNI]
    ring

/-- The dancer of rank `q < 2^l` is a subset of `P_l` (Notes of `C35b_the_podium_walk.md`). -/
lemma dancer_subset_P (I : Finset ℕ) {l q : ℕ} (hq : q < 2 ^ l) : dancer I q ⊆ Podium.P I l := by
  intro t ht
  simp only [dancer, mem_filter] at ht
  refine mem_filter.2 ⟨ht.1, ?_⟩
  by_contra hc
  push_neg at hc
  have : q / 2 ^ #(I.filter (· < t)) = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) hc))
  have h2 := ht.2
  simp [Houses.bit, this] at h2

/-- Positions `0, …, 2^l − 1` and subsets `D ⊆ P_l` are the same (C7 `lemma_0c`; Notes of
`C35b_the_podium_walk.md`): `Σ_{q < 2^l} f(dancer I q) = Σ_{D ⊆ P_l} f(D)` for `l ≤ |I|`. -/
lemma sum_range_dancer {M : Type*} [AddCommMonoid M] (I : Finset ℕ) {l : ℕ} (hl : l ≤ #I)
    (f : Finset ℕ → M) :
    ∑ q ∈ range (2 ^ l), f (dancer I q) = ∑ D ∈ (Podium.P I l).powerset, f D := by
  have hpow : 2 ^ l ≤ 2 ^ #I := Nat.pow_le_pow_right (by norm_num) hl
  have hinj : Set.InjOn (dancer I) (range (2 ^ l)) := fun p hp q hq h =>
    CellFloor.dancer_inj (lt_of_lt_of_le (mem_range.1 hp) hpow)
      (lt_of_lt_of_le (mem_range.1 hq) hpow) h
  rw [← sum_image hinj]
  congr 1
  apply eq_of_subset_of_card_le
  · intro D hD
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hD
    exact mem_powerset.2 (dancer_subset_P I (mem_range.1 hq))
  · rw [card_image_of_injOn hinj, card_powerset, Podium.card_P hl, card_range]

/-- **(H2)** of `C35b_the_podium_walk.md` (Part H), for every digit list: for `i ≥ 1` and
`p < N`, `ŷ_i(p) ≤ ŷ_i(0)` (indeed `ŷ_i` is the real fit, so it is non-increasing). -/
theorem H2_ds (ds : List Bool) (i : ℕ) (hi : 1 ≤ i) (p : ℕ) (hp : p < 2 ^ Dance.mCount ds) :
    FamilyGroup.yPool ds i p ≤ FamilyGroup.yPool ds i 0 := by
  have hfit := (pool_facts ds i hi).1
  have := (fit_nonIncr _ (toR (fun j => Rulers.clock ds.length (Ids ds) i
    (dancer (Ids ds) j)))).anti (Nat.zero_le p) hp
  rw [hfit p hp, hfit 0 (by positivity)] at this
  exact_mod_cast this

/-- **(H1)** of `C35b_the_podium_walk.md` (Part H), for every digit list: for `i ≥ 1` there is
`l ≤ s` such that for every `p < 2^l`,
`2^l · ŷ_i(p) = Σ_{q < 2^l} u_i(dancer I q)` (`u_i = Rulers.clock k I i`).  The proof shows that the
first level set of the real fit of the raw clocks is exactly the set of positions `[0, 2^l)`. -/
theorem H1_ds (ds : List Bool) (i : ℕ) (hi : 1 ≤ i) :
    ∃ l ≤ (Ids ds).card, ∀ p < 2 ^ l,
      2 ^ l * FamilyGroup.yPool ds i p =
        ∑ q ∈ range (2 ^ l), Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) q) := by
  set N := 2 ^ Dance.mCount ds with hN
  have hNI : 2 ^ #(Ids ds) = N := DanceSmith.two_pow_card_Ids ds
  set I := Ids ds with hIdef
  set k := ds.length with hk
  set ℓ := (i - 1) % 2 ^ k with hℓdef
  have hI : ∀ t ∈ I, t < k := DanceSmith.hI_Ids ds
  have hℓ : ℓ < 2 ^ k := Nat.mod_lt _ (by positivity)
  set Pr := Houses.r k (i - 1)
  set Pc := Houses.r k (i - 1 + 2 ^ k)
  obtain ⟨hfit, hpool⟩ := pool_facts ds i hi
  obtain ⟨l, hl, hconst, hdrop⟩ := house_head #I I k ℓ 1 rfl hI hℓ le_rfl
  have hpow : 2 ^ l ≤ N := hNI ▸ Nat.pow_le_pow_right (by norm_num) hl
  set δ := CellFloor.cellShift I k ℓ Pr Pc with hδ
  have hδconst : ∀ p < 2 ^ l, δ p = δ 0 := by
    apply const_of_change_drop hconst
    intro b hb0 hb hne
    have hcut := (CellFloor.cellShift_change_strictCut hI hℓ (α := 1) le_rfl Pr Pc b hb0
      (by rw [hNI]; omega) hne).2
    rw [(CellFloor.lemma_7_9_I1 hI hℓ le_rfl).1 b (by rw [hNI]; omega),
      (CellFloor.lemma_7_9_I1 hI hℓ le_rfl).1 (b - 1) (by rw [hNI]; omega)] at hcut
    exact_mod_cast hcut
  set F := FamilyGroup.yPool ds i with hF
  have hFconst : ∀ p < 2 ^ l, F p = F 0 := by
    intro p hp
    rw [hpool p (by omega), hpool 0 (by positivity), hconst p hp, hδconst p hp]
  have hFdrop : 2 ^ l < N → F (2 ^ l) < F 0 := by
    intro h
    rw [hpool _ h, hpool 0 (by positivity)]
    have h1 := hdrop (by rw [hNI]; exact h)
    have h2 : δ (2 ^ l) ≤ δ 0 := by
      have := (CellFloor.cellShift_nonIncr I k ℓ Pr Pc).anti (Nat.zero_le (2 ^ l))
        (by rw [hNI]; exact h)
      simp only [toR] at this
      exact_mod_cast this
    linarith
  set x : ℕ → ℤ := fun j => Rulers.clock k I i (dancer I j) with hx
  have hlev : levelSet N (fit N (toR x)) 0 = range (2 ^ l) := by
    ext q
    simp only [levelSet, mem_filter, mem_range]
    constructor
    · rintro ⟨hq, he⟩
      by_contra hlq
      push_neg at hlq
      rw [hfit q hq, hfit 0 (by positivity)] at he
      have he' : F q = F 0 := by exact_mod_cast he
      have h1 : F q ≤ F (2 ^ l) := by
        have := (fit_nonIncr N (toR x)).anti hlq hq
        rw [hfit q hq, hfit _ (by omega)] at this
        exact_mod_cast this
      have := hFdrop (by omega)
      omega
    · intro hq
      refine ⟨by omega, ?_⟩
      rw [hfit q (by omega), hfit 0 (by positivity), hFconst q hq]
  have hsum := sum_levelSet_fit (x := toR x) (N := N) (j := 0) (by positivity)
  rw [hlev, card_range, hfit 0 (by positivity)] at hsum
  have hsumZ : ∑ q ∈ range (2 ^ l), x q = 2 ^ l * F 0 := by
    have : ((∑ q ∈ range (2 ^ l), x q : ℤ) : ℝ) = ((2 ^ l * F 0 : ℤ) : ℝ) := by
      push_cast; simpa [toR] using hsum
    exact_mod_cast this
  refine ⟨l, hl, fun p hp => ?_⟩
  rw [hFconst p hp, ← hsumZ]

/-- **(H1)** of `C35b_the_podium_walk.md` (Part H, the head of the fit is dyadic): for the family
`λ` (`d = Families.ds lam`, `k = d.length`, `I = Windows.Ids d`, `s = I.card`) and `i ≥ 1`, there
is `l ≤ s` such that for every `p < 2^l`,
`2^l · yPool d i p = Σ_{q < 2^l} Rulers.clock k I i (dancer I q)`.  (The hypothesis `λ ≥ 1` is not
needed; this is `H1_ds` for `d = ds λ`.) -/
theorem H1 (lam i : ℕ) (hi : 1 ≤ i) :
    ∃ l ≤ (Ids (Families.ds lam)).card, ∀ p < 2 ^ l,
      2 ^ l * FamilyGroup.yPool (Families.ds lam) i p =
        ∑ q ∈ range (2 ^ l), Rulers.clock (Families.ds lam).length (Ids (Families.ds lam)) i
          (dancer (Ids (Families.ds lam)) q) :=
  H1_ds (Families.ds lam) i hi

/-- **(H2)** of `C35b_the_podium_walk.md` (Part H): for the family `λ`, `i ≥ 1` and `p < N`,
`yPool d i p ≤ yPool d i 0`.  (The hypothesis `λ ≥ 1` is not needed; this is `H2_ds`.) -/
theorem H2 (lam i : ℕ) (hi : 1 ≤ i) (p : ℕ) (hp : p < 2 ^ Dance.mCount (Families.ds lam)) :
    FamilyGroup.yPool (Families.ds lam) i p ≤ FamilyGroup.yPool (Families.ds lam) i 0 :=
  H2_ds (Families.ds lam) i hi p hp

/-- **(C1)** of `C35b_the_podium_walk.md` (Proposition 9.6), for every digit list, with
`λ = Rulers.lam k I`: for `i ≥ 1` and `p < N` there is `y` with `1 ≤ y ≤ λ + i` and
`ŷ_i(p) ≤ φ(y)`. -/
theorem C1_ds (ds : List Bool) (i : ℕ) (hi : 1 ≤ i) (p : ℕ) (hp : p < 2 ^ Dance.mCount ds) :
    ∃ y, 1 ≤ y ∧ y ≤ Rulers.lam ds.length (Ids ds) + i ∧
      FamilyGroup.yPool ds i p ≤ Rulers.phi y := by
  obtain ⟨l, hl, hsum⟩ := H1_ds ds i hi
  have h0 := hsum 0 (by positivity)
  rw [sum_range_dancer (Ids ds) hl (fun D => Rulers.clock ds.length (Ids ds) i D)] at h0
  obtain ⟨y, hy, hmax⟩ := (Icc 1 (Rulers.lam ds.length (Ids ds) + i)).exists_max_image
    Rulers.phi ⟨1, by simp; omega⟩
  have hI : Ids ds ⊆ range ds.length := fun t ht => mem_range.2 (lt_of_mem_Ids ht)
  have hM5 := Podium.M5 hI l hl i hi (Rulers.phi y)
    (fun y' h1 h2 => hmax y' (by simp only [mem_Icc]; omega))
  rw [← h0] at hM5
  have hF0 : FamilyGroup.yPool ds i 0 ≤ Rulers.phi y :=
    le_of_mul_le_mul_left hM5 (by positivity)
  simp only [mem_Icc] at hy
  exact ⟨y, hy.1, hy.2, (H2_ds ds i hi p hp).trans hF0⟩

/-- **(C1)** of `C35b_the_podium_walk.md` (Proposition 9.6, the ceiling): for the family `λ`,
`i ≥ 1` and `p < N` there is `y` with `1 ≤ y ≤ λ + i` and `yPool d i p ≤ φ(y)`.  (The hypothesis
`λ ≥ 1` is not needed; `λ = Rulers.lam k I` by C33 `S1_lam`.) -/
theorem C1 (lam i : ℕ) (hi : 1 ≤ i) (p : ℕ) (hp : p < 2 ^ Dance.mCount (Families.ds lam)) :
    ∃ y, 1 ≤ y ∧ y ≤ lam + i ∧ FamilyGroup.yPool (Families.ds lam) i p ≤ Rulers.phi y := by
  have := C1_ds (Families.ds lam) i hi p hp
  rwa [MainTheorem.S1_lam] at this

end PodiumWalk
