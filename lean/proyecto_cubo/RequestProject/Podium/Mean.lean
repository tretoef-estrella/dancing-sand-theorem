module

public import RequestProject.Podium.Clearings
public import RequestProject.Podium.Carries

/-!
# Steps (M) and (K) of the proof of Proposition 9.6 (`C35_the_podium_arithmetic.md`, *Part M*)

Encodings as in `Podium/Defs.lean` and C3: the raw clock `u_i(D)` is `Rulers.clock k I i D`,
`m = i − 1` is the natural number `i - 1`, the subsets `D ⊆ P_l` are the elements of
`(P I l).powerset`, and all clocks, `φ`, `κ`, `ψ` are integers.  The hypothesis
`I ⊆ {0, …, k − 1}` is `hI : I ⊆ Finset.range k`.
-/

@[expose] public section

namespace Podium

open Finset Rulers

variable {k : ℕ} {I : Finset ℕ}

/-- **(M1)** of `C35_the_podium_arithmetic.md`: for `D ⊆ I` and `i ≥ 1`,
`u_i(D) = φ(λ + 1) + 2 ψ(D) + κ(i − 1, K + o_{I ∖ D}) − κ(i − 1, o_D)`. -/
theorem M1 (hI : I ⊆ range k) {D : Finset ℕ} (hD : D ⊆ I) (i : ℕ) (hi : 1 ≤ i) :
    clock k I i D = phi (lam k I + 1) + 2 * psi k I D +
      kappa (i - 1) (2 ^ k + oE (I \ D)) - kappa (i - 1) (oE D) := by
  have hI' := lt_of_subset_range hI
  rw [proposition_5_3 hI' hD i hi]
  set m := i - 1
  simp only [xD, ruler, sum_h_sub]
  have hE : oE (I \ D) < 2 ^ k := oE_lt _ _ fun t ht => hI' t (mem_sdiff.1 ht).1
  have hs2 : s2 (2 ^ k + oE (I \ D)) = s2 (oE (I \ D)) + 1 := by
    rw [add_comm, show oE (I \ D) + 2 ^ k = oE (I \ D) + 2 ^ k * 1 by ring,
      s2_add_two_pow_mul k _ 1 hE, s2_one]
  have hkap : kappa m (2 ^ k) + kappa (m + 2 ^ k) (oE (I \ D)) =
      kappa m (2 ^ k + oE (I \ D)) := by
    simp only [kappa]
    rw [hs2, s2_two_pow, show m + 2 ^ k + oE (I \ D) = m + (2 ^ k + oE (I \ D)) by ring]
    push_cast; ring
  have hk := k_eq_t1_add_sum_h hI'
  rw [t1, ← sum_sdiff hD] at hk
  have hoE := oE_sdiff hD
  have hoE' : ((oE (I \ D) : ℕ) : ℤ) + oE D = oE I := by exact_mod_cast hoE
  rw [phi, lam_add_one, v2_K_add_oE hI', psi_eq, hSum, hSum]
  push_cast
  linarith

/-- Complementation `D ↦ S ∖ D` permutes the subsets of `S`. -/
lemma sum_powerset_compl {M : Type*} [AddCommMonoid M] (S : Finset ℕ) (f : Finset ℕ → M) :
    ∑ D ∈ S.powerset, f (S \ D) = ∑ D ∈ S.powerset, f D := by
  apply sum_nbij' (fun D => S \ D) (fun D => S \ D)
  · intro D _; exact mem_powerset.2 sdiff_subset
  · intro D _; exact mem_powerset.2 sdiff_subset
  · intro D hD; exact Finset.sdiff_sdiff_eq_self (mem_powerset.1 hD)
  · intro D hD; exact Finset.sdiff_sdiff_eq_self (mem_powerset.1 hD)
  · intro D _; rfl

/-- For `D ⊆ P_l`: `K + o_{I ∖ D} = Y_l + o_{P_l ∖ D}`. -/
lemma K_add_oE_sdiff {l : ℕ} {D : Finset ℕ} (hD : D ⊆ P I l) :
    2 ^ k + oE (I \ D) = Y k I l + oE (P I l \ D) := by
  have h1 := oE_sdiff (hD.trans (P_subset I l))
  have h2 := oE_sdiff hD
  have h3 := oE_sdiff (P_subset I l)
  unfold Y
  omega

lemma psi_add_psi_sdiff {S D : Finset ℕ} (hD : D ⊆ S) :
    psi k I D + psi k I (S \ D) = psi k I S := by
  unfold psi; rw [add_comm, sum_sdiff hD]

/-- **(M2)** of `C35_the_podium_arithmetic.md`: for `i ≥ 1`,
`Σ_{D ⊆ P_l} u_i(D) = Σ_{D ⊆ P_l} (φ(Y_l) + κ(i − 1, Y_l + o_D) − κ(i − 1, o_D))`.
The file assumes `l ≤ s`; this holds for every `l`. -/
theorem M2 (hI : I ⊆ range k) (l i : ℕ) (hi : 1 ≤ i) :
    ∑ D ∈ (P I l).powerset, clock k I i D =
      ∑ D ∈ (P I l).powerset, (phi (Y k I l) + kappa (i - 1) (Y k I l + oE D) -
        kappa (i - 1) (oE D)) := by
  set m := i - 1
  set S := P I l
  have hL : ∀ D ∈ S.powerset, clock k I i D = phi (lam k I + 1) + 2 * psi k I D +
      kappa m (Y k I l + oE (S \ D)) - kappa m (oE D) := by
    intro D hD
    have hD' := mem_powerset.1 hD
    rw [M1 hI (hD'.trans (P_subset I l)) i hi, K_add_oE_sdiff hD']
  have hR : ∀ D ∈ S.powerset, phi (Y k I l) + kappa m (Y k I l + oE D) - kappa m (oE D) =
      phi (lam k I + 1) + psi k I S + kappa m (Y k I l + oE D) - kappa m (oE D) := by
    intro D _
    rw [(La hI l).1]
  have r1 := sum_powerset_compl S (fun D => psi k I D)
  have r2 := sum_powerset_compl S (fun D => kappa m (Y k I l + oE D))
  have r3 : ∑ D ∈ S.powerset, (psi k I D + psi k I (S \ D)) = ∑ D ∈ S.powerset, psi k I S :=
    sum_congr rfl fun D hD => psi_add_psi_sdiff (mem_powerset.1 hD)
  rw [sum_congr rfl hL, sum_congr rfl hR]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at r3 ⊢
  simp only at r1 r2
  linarith

/-- **(M4)** of `C35_the_podium_arithmetic.md` (step (K) of Proposition 9.6): for `D ⊆ P_l` and
`m : ℕ` there is `y` with `1 ≤ y ≤ λ + 1 + m` and
`φ(Y_l) + κ(m, Y_l + o_D) − κ(m, o_D) ≤ φ(y)`.  The file assumes `l ≤ s`; this holds for every
`l`. -/
theorem M4 (hI : I ⊆ range k) (l : ℕ) {D : Finset ℕ} (hD : D ⊆ P I l) (m : ℕ) :
    ∃ y, 1 ≤ y ∧ y ≤ lam k I + 1 + m ∧
      phi (Y k I l) + kappa m (Y k I l + oE D) - kappa m (oE D) ≤ phi y := by
  have hI' := lt_of_subset_range hI
  set q := tAt k I l
  have hqk : q ≤ k := tAt_le hI' l
  have hYdvd : 2 ^ q ∣ Y k I l := by
    rw [Y_eq_oE hI']
    apply two_pow_dvd_oE
    intro t ht
    rcases mem_insert.1 ht with rfl | ht
    · exact hqk
    · exact minOr_le ht
  have ho : oE D < 2 ^ q := oE_lt D q fun t ht => P_lt_tAt hI' l (hD ht)
  have hpos : 0 < 2 ^ q := by positivity
  have hYge : 2 ^ q ≤ Y k I l :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hqk) (by unfold Y; omega)
  set B := Y k I l / 2 ^ q
  have hB : 1 ≤ B := (Nat.one_le_div_iff hpos).2 hYge
  have hYB : 2 ^ q * B = Y k I l := Nat.mul_div_cancel' hYdvd
  set c := if 2 ^ q ≤ m % 2 ^ q + oE D then 1 else 0
  have hc : 2 ^ q * c ≤ m % 2 ^ q + oE D := by
    simp only [c]; split_ifs with h <;> omega
  obtain ⟨y, hy1, hyle, hy⟩ := K (m / 2 ^ q + c) B q hB
  have hM3 := M3 (Y k I l) (oE D) m q hYdvd ho
  refine ⟨y, hy1, ?_, ?_⟩
  · have hmd := Nat.mod_add_div m (2 ^ q)
    have hDP : oE D ≤ oE (P I l) := sum_le_sum_of_subset hD
    have hYP := Y_add_oE_P k I l
    have : 2 ^ q * (m / 2 ^ q + c + B) = 2 ^ q * (m / 2 ^ q) + 2 ^ q * c + 2 ^ q * B := by ring
    omega
  · rw [hYB] at hy
    linarith

/-- **(M5)** of `C35_the_podium_arithmetic.md`: for `l ≤ s`, `i ≥ 1` and `G : ℤ` with
`φ(y) ≤ G` for every `1 ≤ y ≤ λ + 1 + (i − 1)`, `Σ_{D ⊆ P_l} u_i(D) ≤ 2^l G`. -/
theorem M5 (hI : I ⊆ range k) (l : ℕ) (hl : l ≤ I.card) (i : ℕ) (hi : 1 ≤ i) (G : ℤ)
    (hG : ∀ y : ℕ, 1 ≤ y → y ≤ lam k I + 1 + (i - 1) → phi y ≤ G) :
    ∑ D ∈ (P I l).powerset, clock k I i D ≤ 2 ^ l * G := by
  rw [M2 hI l i hi]
  calc ∑ D ∈ (P I l).powerset, (phi (Y k I l) + kappa (i - 1) (Y k I l + oE D) -
        kappa (i - 1) (oE D))
      ≤ ∑ D ∈ (P I l).powerset, G := by
        apply sum_le_sum
        intro D hD
        obtain ⟨y, hy1, hyle, hy⟩ := M4 hI l (mem_powerset.1 hD) (i - 1)
        exact le_trans hy (hG y hy1 hyle)
    _ = 2 ^ l * G := by
        rw [sum_const, card_powerset, card_P hl, nsmul_eq_mul]
        push_cast; ring

end Podium
