module

public import RequestProject.MainTheorem.All
public import RequestProject.BaiCounts.Layers

/-!
# `C34_bais_counts.md`: Part A — Lemma 9.1 (clocks are at least 2)

Encodings (namespace `BaiCounts`):

* The raw clock `u_i(D)` is C3's `Rulers.clock k I i D`
  (`= φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`, an integer, with `ξ_D = Rulers.xi k I D`).
* The integer fit is C1's `AntitonicFit.ifit N x` for `x : ℕ → ℤ` (entries at positions `< N`).
* The pooled clocks are C16's `FamilyGroup.yPool (ds λ) i` and `FamilyGroup.yPool0 (ds λ)`;
  `λ` is written `lam`, `N λ = 2 ^ Dance.mCount (ds λ)`, `k λ = (ds λ).length`,
  `I λ = Windows.Ids (ds λ)`.
-/

@[expose] public section

namespace BaiCounts

open Finset Families

/-! ### Carries are non-negative -/

/-- `s_2(n + 1) ≤ s_2(n) + 1` (auxiliary for (A1) of `C34_bais_counts.md`). -/
lemma s2_succ_le (n : ℕ) : Rulers.s2 (n + 1) ≤ Rulers.s2 n + 1 := by
  have h := Rulers.s2_succ n
  have : (0 : ℤ) ≤ Rulers.v2 (n + 1) := Int.natCast_nonneg _
  omega

/-- `s_2(a + b) ≤ s_2(a) + s_2(b)` (auxiliary for (A1) of `C34_bais_counts.md`). -/
lemma s2_add_le (a : ℕ) : ∀ b : ℕ, Rulers.s2 (a + b) ≤ Rulers.s2 a + Rulers.s2 b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    have ea : a = a % 2 + 2 * (a / 2) := (Nat.mod_add_div a 2).symm
    have eb : b = b % 2 + 2 * (b / 2) := (Nat.mod_add_div b 2).symm
    have sa : Rulers.s2 a = a % 2 + Rulers.s2 (a / 2) := by
      conv_lhs => rw [ea]
      exact Rulers.s2_bit _ _ (Nat.mod_lt _ (by norm_num))
    have sb : Rulers.s2 b = b % 2 + Rulers.s2 (b / 2) := by
      conv_lhs => rw [eb]
      exact Rulers.s2_bit _ _ (Nat.mod_lt _ (by norm_num))
    have hih := ih (a / 2) (by omega)
    by_cases hc : a % 2 + b % 2 < 2
    · have e : a + b = (a % 2 + b % 2) + 2 * (a / 2 + b / 2) := by omega
      rw [e, Rulers.s2_bit _ _ hc, sa, sb]
      have := hih (b / 2)
      omega
    · have e : a + b = 0 + 2 * (a / 2 + b / 2 + 1) := by omega
      rw [e, Rulers.s2_bit _ _ (by norm_num), sa, sb]
      have h1 := s2_succ_le (a / 2 + b / 2)
      have := hih (b / 2)
      omega

/-- `κ(a, b) ≥ 0`: the number of carries is non-negative (auxiliary for (A1) of
`C34_bais_counts.md`). -/
lemma kappa_nonneg (a b : ℕ) : 0 ≤ Rulers.kappa a b := by
  have := s2_add_le a b
  unfold Rulers.kappa
  omega

/-! ### (A1) -/

/-- **(A1)** of `C34_bais_counts.md` (Lemma 9.1), general form: for `k ≥ 1`, `I ⊆ range k`,
`D ⊆ I` and every `i`, `2 ≤ Rulers.clock k I i D`.  (This is more general than (A1): the
hypothesis `1 ≤ i ∨ D ≠ ∅` is not needed, since for `D = ∅` already `ξ_∅ = 2^k + o_I ≥ 2`.) -/
theorem A1_general (k : ℕ) (hk : 1 ≤ k) (I : Finset ℕ) (hI : I ⊆ range k) (D : Finset ℕ)
    (hD : D ⊆ I) (i : ℕ) : 2 ≤ Rulers.clock k I i D := by
  have hI' : ∀ t ∈ I, t < k := fun t ht => mem_range.1 (hI ht)
  obtain ⟨hx, hx1⟩ := Rulers.lemma_5_0_xi hI' hD
  have hκ := kappa_nonneg (i + Rulers.oE D - 1) (Rulers.xi k I D)
  have hv : (0 : ℤ) ≤ Rulers.v2 (Rulers.xi k I D) := Int.natCast_nonneg _
  have hphi : Rulers.phi (Rulers.xi k I D) = (Rulers.xi k I D : ℤ) + Rulers.v2 (Rulers.xi k I D) :=
    rfl
  unfold Rulers.clock
  rw [hphi]
  by_cases hDe : D = ∅
  · subst hDe
    have hK : (2 : ℤ) ≤ 2 ^ k := by
      have : (2 : ℤ) ^ 1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      simpa using this
    rw [Rulers.oE_empty] at hx
    push_cast at hx
    have : (0 : ℤ) ≤ (Rulers.oE I : ℤ) := Int.natCast_nonneg _
    have : (0 : ℤ) ≤ (Rulers.hSum k I ∅ : ℤ) := Int.natCast_nonneg _
    linarith
  · obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.2 hDe
    have h1 : 1 ≤ Rulers.hSum k I D :=
      le_trans (Rulers.one_le_h hI' (hD ht))
        (single_le_sum (f := fun t => Rulers.h k I t) (fun _ _ => Nat.zero_le _) ht)
    have : (1 : ℤ) ≤ (Rulers.hSum k I D : ℤ) := by exact_mod_cast h1
    have : (1 : ℤ) ≤ (Rulers.xi k I D : ℤ) := by exact_mod_cast hx1
    linarith

/-- **(A1)** of `C34_bais_counts.md` (Lemma 9.1): for `k ≥ 1`, `I ⊆ Finset.range k`, `D ⊆ I` and
`i : ℕ` with `1 ≤ i ∨ D ≠ ∅`, `2 ≤ Rulers.clock k I i D`.  The hypothesis `1 ≤ i ∨ D ≠ ∅` is kept
as in the file but is not used (see `A1_general`). -/
theorem A1 (k : ℕ) (hk : 1 ≤ k) (I : Finset ℕ) (hI : I ⊆ range k) (D : Finset ℕ) (hD : D ⊆ I)
    (i : ℕ) (_hiD : 1 ≤ i ∨ D ≠ ∅) : 2 ≤ Rulers.clock k I i D :=
  A1_general k hk I hI D hD i

/-- The hypothesis `1 ≤ k` of (A1) of `C34_bais_counts.md` is needed: for `k = 0`, `I = D = ∅`
and `i = 1`, the clock is `1`. -/
theorem A1_k_zero : Rulers.clock 0 ∅ 1 ∅ = 1 := by
  simp [Rulers.clock, Rulers.xi, Rulers.lam, Rulers.oE, Rulers.phi, Rulers.v2, Rulers.kappa,
    Rulers.s2, Rulers.hSum]

/-! ### (A2) -/

/-- **(A2)** of `C34_bais_counts.md` (pooled clocks): if every entry of `x : ℕ → ℤ` on `[0, N)` is
`≥ c`, then `AntitonicFit.ifit N x j ≥ c` for every `j < N`. -/
theorem A2 (N : ℕ) (x : ℕ → ℤ) (c : ℤ) (hx : ∀ j < N, c ≤ x j) (j : ℕ) (hj : j < N) :
    c ≤ AntitonicFit.ifit N x j := by
  rw [AntitonicFit.ifit_of_lt hj]
  set L := AntitonicFit.levelSet N (AntitonicFit.fit N (AntitonicFit.toR x)) j
  have hjL : j ∈ L := by simp [L, AntitonicFit.levelSet, hj]
  have hP : 0 < L.card := card_pos.2 ⟨j, hjL⟩
  have hS : (L.card : ℤ) * c ≤ ∑ i ∈ L, x i := by
    have := card_nsmul_le_sum L x c (fun i hi => by
      simp only [L, AntitonicFit.levelSet, mem_filter, mem_range] at hi
      exact hx i hi.1)
    simpa [nsmul_eq_mul] using this
  have e : ∑ i ∈ L, x i = (∑ i ∈ L, x i - L.card * c) + L.card * c := by ring
  rw [e, AntitonicFit.blockF_add_mul _ _ hP]
  have := AntitonicFit.blockF_nonneg (S := ∑ i ∈ L, x i - L.card * c) (by linarith) L.card
    (L.filter (· < j)).card
  linarith

/-! ### (A3) -/

/-- **(A3)** of `C34_bais_counts.md`, shifts `i ≥ 1`: for `λ ≥ 1`, `i ≥ 1` and `p < N λ`,
`2 ≤ FamilyGroup.yPool (ds λ) i p`.  From (A1), (A2), C33 (S2), (S3) and C7 `lemma_0a`. -/
theorem A3_pos (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) (p : ℕ)
    (hp : p < 2 ^ Dance.mCount (ds lam)) : 2 ≤ FamilyGroup.yPool (ds lam) i p :=
  A2 _ _ 2 (fun _ _ => A1 _ (MainTheorem.S2_length lam hlam) _ (MainTheorem.S3_subset lam) _
    (TheoremF.lemma_0a _ _) i (Or.inl hi)) p hp

/-- **(A3)** of `C34_bais_counts.md`, shift `0`: for `λ ≥ 1` and `q < N λ − 1`,
`2 ≤ FamilyGroup.yPool0 (ds λ) q`.  From (A1) (in its general form `A1_general`, so that the fact
`dancer (I λ) (j + 1) ≠ ∅` of the sketch is not needed), (A2), C33 (S2), (S3) and C7 `lemma_0a`. -/
theorem A3_zero (lam : ℕ) (hlam : 1 ≤ lam) (q : ℕ) (hq : q < 2 ^ Dance.mCount (ds lam) - 1) :
    2 ≤ FamilyGroup.yPool0 (ds lam) q :=
  A2 _ _ 2 (fun _ _ => A1_general _ (MainTheorem.S2_length lam hlam) _
    (MainTheorem.S3_subset lam) _ (TheoremF.lemma_0a _ _) 0) q hq

end BaiCounts
