module

public import RequestProject.PodiumCor.Counting

/-!
# `C36_the_podium_corollary.md`: Part P — Corollary 1.6 (the podium)

Encodings: `c r` is `cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℕ`, compared with integers
through the cast `(c r : ℤ)`; `G = gmax (n − 1)`, `φ = Rulers.phi` (both integer valued).
-/

@[expose] public section

namespace PodiumCor

open Finset Families

/-- `m (n − 2) n` and the value of `yPool (ds (n − 2)) 1 0` used in Part P (auxiliary). -/
lemma m_n2_even (n : ℕ) (hn : 4 ≤ n) (hev : n % 2 = 0) : FamDec.m (n - 2) n = n - 2 := by
  rw [L2 n (by omega), if_pos hev]; omega

/-- `m (n − 2) n = n − 1` for odd `n` (auxiliary). -/
lemma m_n2_odd (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) : FamDec.m (n - 2) n = n - 1 := by
  rw [L2 n (by omega), if_neg (by omega)]; omega

/-- For odd `n ≥ 4`, `X := max G (φ(n − 1) − 2)` bounds `yPool0 (ds n) 0` when `s ≥ 1` (from (B5),
(B6); auxiliary). -/
lemma v0_le_odd (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) :
    1 ≤ (Windows.Ids (ds n)).card →
      FamilyGroup.yPool0 (ds n) 0 ≤ max (gmax (n - 1)) (Rulers.phi (n - 1) - 2) := fun hs => by
  rcases (show n % 4 = 1 ∨ n % 4 = 3 by omega) with h | h
  · exact (B5 n hn h).2
  · exact (B6 n hn h hs).trans (le_max_left _ _)

/-- **(P1)** of `C36_the_podium_corollary.md` (Corollary 1.6, `n` even): for even `n ≥ 4`,
`(c 1 : ℤ) = max G (φ n − 1)` and `(c r : ℤ) = G` for `2 ≤ r ≤ n + 1`, where
`c r = cExp (Syl2 (K n)) r` and `G = gmax (n − 1)`. -/
theorem P1 (n : ℕ) (hn : 4 ≤ n) (hev : n % 2 = 0) :
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (gmax (n - 1)) (Rulers.phi n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n + 1 →
        (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = gmax (n - 1) := by
  have hG2 := gmax_ge (n - 1) (by omega)
  obtain ⟨hB, -, -⟩ := B7 n hn hev
  have hm2 := m_n2_even n hn hev
  obtain ⟨hv0l, hv0u⟩ := B4 n hn hev
  obtain ⟨l, hl⟩ : ∃ l, n = 2 * l + 2 := ⟨n / 2 - 1, by omega⟩
  have hs : 1 ≤ (Windows.Ids (ds n)).card := card_pos.2 ⟨0, hl ▸ zero_mem_even l⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = max (gmax (n - 1)) (Rulers.phi n - 1) := ⟨_, rfl⟩
  have hXl : gmax (n - 1) ≤ X := hXdef ▸ le_max_left _ _
  have hXr : Rulers.phi n - 1 ≤ X := hXdef ▸ le_max_right _ _
  have hXc : X = gmax (n - 1) ∨ X = Rulers.phi n - 1 := hXdef ▸ max_choice _ _
  rw [← hXdef] at hv0u ⊢
  have hphin := phi_even n (by omega) hev
  refine ⟨?_, fun r hr2 hr => ?_⟩
  · apply cExp_eq_of_counts n 1 X (by omega) le_rfl (by omega)
    · have hl := lower_count n X.toNat hn
      rcases hXc with hc | hc
      · have := famCount_n2_ge_one n X.toNat hn (by rw [hB]; omega)
        have := Nat.mul_le_mul_left (FamDec.m (n - 2) n) this
        omega
      · have := famCount_n_ge_one n X.toNat hs (by omega)
        omega
    · have hu := upper_count n (X.toNat + 1) X hn (by omega) (fun _ => hv0u)
      rw [if_neg (by rw [hB]; omega), if_neg (by omega)] at hu
      omega
  · apply cExp_eq_of_counts n r (gmax (n - 1)) (by omega) (by omega) (by omega)
    · have hl := lower_count n (gmax (n - 1)).toNat hn
      have h2 := famCount_n2_ge_two n (gmax (n - 1)).toNat hn hev (by omega)
      have hmul := Nat.mul_le_mul_left (FamDec.m (n - 2) n) h2
      by_cases h6 : 6 ≤ n
      · omega
      · have hG3 : gmax (n - 1) ≤ 3 := by
          rw [show n - 1 = 3 by omega]
          exact gmax_le_of 3 (by norm_num) 3 fun y h1 h2 => by have := phi_le y h1; omega
        have := famCount_n_ge_one n (gmax (n - 1)).toNat hs (by omega)
        omega
    · have hu := upper_count n ((gmax (n - 1)).toNat + 1) X hn (by omega) (fun _ => hv0u)
      rw [if_neg (by rw [hB]; omega)] at hu
      split_ifs at hu <;> omega

/-- **(P2)** of `C36_the_podium_corollary.md` (Corollary 1.6, `n` odd, `φ(n − 1) ≤ G`): for odd
`n ≥ 4` with `φ(n − 1) ≤ G`, `(c r : ℤ) = G` for `1 ≤ r ≤ n + 1`. -/
theorem P2 (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) (hphi : Rulers.phi (n - 1) ≤ gmax (n - 1)) :
    ∀ r, 1 ≤ r → r ≤ n + 1 →
      (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = gmax (n - 1) := by
  intro r hr1 hr
  have hG2 := gmax_ge (n - 1) (by omega)
  have hB : FamilyGroup.yPool (ds (n - 2)) 1 0 = gmax (n - 1) := by
    rw [(B2 n hn).1, max_eq_left hphi]
  have hY2 := B8 n hn ho
  have hm2 := m_n2_odd n hn ho
  have hm4 := (L3 n (by omega) ho).2
  have hX : 1 ≤ (Windows.Ids (ds n)).card → FamilyGroup.yPool0 (ds n) 0 ≤ gmax (n - 1) :=
    fun hs => (v0_le_odd n hn ho hs).trans (max_le le_rfl (by linarith))
  apply cExp_eq_of_counts n r (gmax (n - 1)) (by omega) hr1 (by omega)
  · have hl := lower_count n (gmax (n - 1)).toNat hn
    have h2 := famCount_n2_ge_one n (gmax (n - 1)).toNat hn (by rw [hB]; omega)
    have h4 := famCount_n4_ge_one n (gmax (n - 1)).toNat hn (by rw [hY2]; omega)
    have := Nat.mul_le_mul_left (FamDec.m (n - 2) n) h2
    have := Nat.mul_le_mul hm4 h4
    omega
  · have hu := upper_count n ((gmax (n - 1)).toNat + 1) (gmax (n - 1)) hn (by omega) hX
    rw [if_neg (by rw [hB]; omega), if_neg (by omega)] at hu
    omega

/-- **(P3)** of `C36_the_podium_corollary.md` (Corollary 1.6, `n` odd, `φ(n − 1) > G`): for odd
`n ≥ 4` with `φ(n − 1) > G`, `(c r : ℤ) = φ(n − 1)` for `1 ≤ r ≤ n − 1`,
`(c n : ℤ) = max G (φ(n − 1) − 2)` and `(c (n + 1) : ℤ) = G`. -/
theorem P3 (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) (hphi : gmax (n - 1) < Rulers.phi (n - 1)) :
    (∀ r, 1 ≤ r → r ≤ n - 1 →
      (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = Rulers.phi (n - 1)) ∧
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) n : ℤ) =
      max (gmax (n - 1)) (Rulers.phi (n - 1) - 2) ∧
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) (n + 1) : ℤ) = gmax (n - 1) := by
  have hG2 := gmax_ge (n - 1) (by omega)
  have hB : FamilyGroup.yPool (ds (n - 2)) 1 0 = Rulers.phi (n - 1) := by
    rw [(B2 n hn).1, max_eq_right hphi.le]
  have hY2 := B8 n hn ho
  have hm2 := m_n2_odd n hn ho
  have hm4 := (L3 n (by omega) ho).2
  obtain ⟨X, hXdef⟩ : ∃ X, X = max (gmax (n - 1)) (Rulers.phi (n - 1) - 2) := ⟨_, rfl⟩
  have hXl : gmax (n - 1) ≤ X := hXdef ▸ le_max_left _ _
  have hXr : Rulers.phi (n - 1) - 2 ≤ X := hXdef ▸ le_max_right _ _
  have hXc : X = gmax (n - 1) ∨ X = Rulers.phi (n - 1) - 2 := hXdef ▸ max_choice _ _
  have hX := v0_le_odd n hn ho
  rw [← hXdef] at hX ⊢
  -- at least `n + 3` exponents `≥ G`
  have hlowG : n + 1 ≤ (exps n).countP (fun x => (gmax (n - 1)).toNat ≤ x) := by
    have hl := lower_count n (gmax (n - 1)).toNat hn
    have h2 := famCount_n2_ge_one n (gmax (n - 1)).toNat hn (by rw [hB]; omega)
    have h4 := famCount_n4_ge_one n (gmax (n - 1)).toNat hn (by rw [hY2]; omega)
    have := Nat.mul_le_mul_left (FamDec.m (n - 2) n) h2
    have := Nat.mul_le_mul hm4 h4
    omega
  refine ⟨fun r hr1 hr => ?_, ?_, ?_⟩
  · apply cExp_eq_of_counts n r (Rulers.phi (n - 1)) (by omega) hr1 (by omega)
    · have hl := lower_count n (Rulers.phi (n - 1)).toNat hn
      have h2 := famCount_n2_ge_one n (Rulers.phi (n - 1)).toNat hn (by rw [hB]; omega)
      have := Nat.mul_le_mul_left (FamDec.m (n - 2) n) h2
      omega
    · have hu := upper_count n ((Rulers.phi (n - 1)).toNat + 1) X hn (by omega) hX
      rw [if_neg (by rw [hB]; omega), if_neg (by omega)] at hu
      omega
  · apply cExp_eq_of_counts n n X (by omega) (by omega) (by omega)
    · by_cases hc : Rulers.phi (n - 1) - 2 ≤ gmax (n - 1)
      · have hXG : X = gmax (n - 1) := by omega
        rw [hXG]; omega
      · have hXF : X = Rulers.phi (n - 1) - 2 := by omega
        have h41 : n % 4 = 1 := by
          by_contra h43
          have hphi1 : Rulers.phi (n - 1) = (n - 1 : ℕ) + 1 := by
            unfold Rulers.phi; rw [v2_two_mod_four (n - 1) (by omega)]; push_cast; ring
          have := le_gmax (n - 1) (n - 3) (by omega) (by omega)
          have := phi_four (n - 3) (by omega) (by omega)
          omega
        obtain ⟨h1I, -⟩ := one_min_of_mod_four n hn h41
        have hs : 1 ≤ (Windows.Ids (ds n)).card := card_pos.2 ⟨1, h1I⟩
        have hv0 := (B5 n hn h41).1
        have hl := lower_count n X.toNat hn
        have h2 := famCount_n2_ge_one n X.toNat hn (by rw [hB]; omega)
        have hn1 := famCount_n_ge_one n X.toNat hs (by omega)
        have := Nat.mul_le_mul_left (FamDec.m (n - 2) n) h2
        omega
    · have hu := upper_count n (X.toNat + 1) X hn (by omega) hX
      split_ifs at hu <;> omega
  · apply cExp_eq_of_counts n (n + 1) (gmax (n - 1)) (by omega) (by omega) (by omega) hlowG
    have hu := upper_count n ((gmax (n - 1)).toNat + 1) X hn (by omega) hX
    split_ifs at hu <;> omega

end PodiumCor
