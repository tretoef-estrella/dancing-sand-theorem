module

public import RequestProject.PodiumCor.Aux

/-!
# `C36_the_podium_corollary.md`: Part B — the bounds of the proof of Corollary 1.6

Encodings: `G := gmax (n − 1)` is written out; for the family `λ`, `d = Families.ds lam`,
`k = d.length`, `I = Windows.Ids d`, `s = I.card`, `N = 2 ^ Dance.mCount d` (`= 2 ^ s` by C33
`S3_card`), `Y_l = Podium.Y k I l`.  The pooled clocks are `FamilyGroup.yPool d i p` and
`FamilyGroup.yPool0 d q` (integers), `φ = Rulers.phi` (integer valued).
-/

@[expose] public section

namespace PodiumCor

open Finset Families

/-- C35 (Ld) for the family `λ` (auxiliary for Part B of `C36_the_podium_corollary.md`). -/
lemma Ld_fam (lam y : ℕ) (hy : 1 ≤ y) (hyN : y ≤ lam + 1) :
    ∃ l ≤ (Windows.Ids (ds lam)).card,
      Rulers.phi y ≤ Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l) :=
  Podium.Ld (MainTheorem.S3_subset lam) y hy (by rw [MainTheorem.S1_lam]; exact hyN)

/-- **(B0)** of `C36_the_podium_corollary.md`: for `n ≥ 4` and `λ ≥ 1` with `m λ n ≠ 0`,
`k − 1 < G` (`k = (ds λ).length`, `G = gmax (n − 1)`): every small clock is below `G`.  (The
hypothesis `λ ≥ 1` is kept as in the file; it also follows from `m λ n ≠ 0` by C31 (M3).) -/
theorem B0 (n lam : ℕ) (hn : 4 ≤ n) (_hlam : 1 ≤ lam) (hm : FamDec.m lam n ≠ 0) :
    ((ds lam).length : ℤ) - 1 < gmax (n - 1) := by
  have hsupp := MainTheorem.M3_support n (by omega) lam hm
  have h1 := MainTheorem.S1_succ lam
  have hk : (ds lam).length ≤ n - 2 := by
    by_contra h
    push_neg at h
    have : 2 ^ (n - 1) ≤ 2 ^ (ds lam).length := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := lt_two_pow_pred n hn
    omega
  have := gmax_ge (n - 1) (by omega)
  omega

/-- **(B1)** of `C36_the_podium_corollary.md`: for `n ≥ 4`, `λ ≥ 1` with `m λ n ≠ 0` and
`i := (n − λ)/2 ≥ 2`, `yPool (ds λ) i p ≤ G` for every `p < N` (from C35b (C1):
`y ≤ λ + i = n − i ≤ n − 2`).  (The hypothesis `λ ≥ 1` is kept as in the file; it also follows from
`m λ n ≠ 0`.) -/
theorem B1 (n lam : ℕ) (hn : 4 ≤ n) (_hlam : 1 ≤ lam) (hm : FamDec.m lam n ≠ 0)
    (hi : 2 ≤ (n - lam) / 2) (p : ℕ) (hp : p < 2 ^ Dance.mCount (ds lam)) :
    FamilyGroup.yPool (ds lam) ((n - lam) / 2) p ≤ gmax (n - 1) := by
  have hsupp := MainTheorem.M3_support n (by omega) lam hm
  obtain ⟨y, hy1, hy2, hle⟩ := PodiumWalk.C1 lam ((n - lam) / 2) (by omega) p hp
  exact hle.trans (le_gmax (n - 1) y hy1 (by omega))

/-- **(B2)** of `C36_the_podium_corollary.md`: for `n ≥ 4` and `d = ds (n − 2)`,
`yPool d 1 0 = max G (φ(n − 1))`, and `yPool d 1 p ≤ G` for `1 ≤ p < N` (C35b (T1), (T2), C35 (Ld),
`Y_l ≤ n − 2` for `l ≥ 1`). -/
theorem B2 (n : ℕ) (hn : 4 ≤ n) :
    FamilyGroup.yPool (ds (n - 2)) 1 0 = max (gmax (n - 1)) (Rulers.phi (n - 1)) ∧
      ∀ p, 1 ≤ p → p < 2 ^ Dance.mCount (ds (n - 2)) →
        FamilyGroup.yPool (ds (n - 2)) 1 p ≤ gmax (n - 1) := by
  obtain ⟨⟨l₀, hl₀, he⟩, hall⟩ := PodiumWalk.T1 (n - 2)
  have hY0 := Y_zero (n - 2)
  rw [show n - 2 + 1 = n - 1 by omega] at hY0
  have hphi : Rulers.phi (n - 1) ≤ FamilyGroup.yPool (ds (n - 2)) 1 0 := by
    have := hall 0 (Nat.zero_le _); rwa [hY0] at this
  have hG : gmax (n - 1) ≤ FamilyGroup.yPool (ds (n - 2)) 1 0 :=
    gmax_le_of _ (by omega) _ fun y hy1 hy2 => by
      obtain ⟨l, hl, hle⟩ := Ld_fam (n - 2) y hy1 (by omega)
      exact hle.trans (hall l hl)
  refine ⟨le_antisymm ?_ (max_le hG hphi), fun p hp1 hp => ?_⟩
  · rw [he]
    rcases Nat.eq_zero_or_pos l₀ with h0 | hpos
    · rw [h0, hY0]; exact le_max_right _ _
    · have := Y_le_self (n - 2) l₀ hpos hl₀
      exact (le_gmax _ _ (Y_pos _ _ _) (by omega)).trans (le_max_left _ _)
  · obtain ⟨l, hl1, hl, hle⟩ := PodiumWalk.T2 (n - 2) p hp1 hp
    have := Y_le_self (n - 2) l hl1 hl
    exact hle.trans (le_gmax _ _ (Y_pos _ _ _) (by omega))

/-- **(B3)** of `C36_the_podium_corollary.md`: for `n ≥ 4` and `d = ds n`:
`yPool0 d q ≤ G` for `1 ≤ q < N − 1` (C35b (Z2)), and `φ(Y_l) ≤ G` for `2 ≤ l ≤ s`
(`Y_l ≤ n − 2`).  (The file's hypothesis `s ≥ 1` is not needed: the first part holds vacuously
when `N − 1 ≤ 1`, the second when `s ≤ 1`.) -/
theorem B3 (n : ℕ) (hn : 4 ≤ n) :
    (∀ q, 1 ≤ q → q < 2 ^ Dance.mCount (ds n) - 1 → FamilyGroup.yPool0 (ds n) q ≤ gmax (n - 1)) ∧
      ∀ l, 2 ≤ l → l ≤ (Windows.Ids (ds n)).card →
        Rulers.phi (Podium.Y (ds n).length (Windows.Ids (ds n)) l) ≤ gmax (n - 1) := by
  have hY : ∀ l, 2 ≤ l → l ≤ (Windows.Ids (ds n)).card →
      Rulers.phi (Podium.Y (ds n).length (Windows.Ids (ds n)) l) ≤ gmax (n - 1) :=
    fun l hl2 hl => le_gmax _ _ (Y_pos _ _ _) (by have := Y_le_sub_two n l hl2 hl; omega)
  refine ⟨fun q hq1 hq => ?_, hY⟩
  obtain ⟨l, hl2, hl, hle⟩ := PodiumWalk.Z2 n q hq1 hq
  exact hle.trans (hY l hl2 hl)

/-- C35b (Z1) for `d = ds n` when the least element of `I` is `t`: with `Y_1 = n + 1 − 2^t`,
`φ(Y_1) − 2^t ≤ yPool0 d 0 ≤ max G (φ(Y_1) − 2^t)` (auxiliary for (B4)–(B6) of
`C36_the_podium_corollary.md`). -/
lemma B_Z (n t : ℕ) (hn : 4 ≤ n) (ht : t ∈ Windows.Ids (ds n))
    (hmin : ∀ u ∈ Windows.Ids (ds n), t ≤ u) :
    Rulers.phi (n + 1 - 2 ^ t) - 2 ^ t ≤ FamilyGroup.yPool0 (ds n) 0 ∧
      FamilyGroup.yPool0 (ds n) 0 ≤ max (gmax (n - 1)) (Rulers.phi (n + 1 - 2 ^ t) - 2 ^ t) := by
  have hs : 1 ≤ (Windows.Ids (ds n)).card := card_pos.2 ⟨t, ht⟩
  obtain ⟨hY1, htA⟩ := Y_one_of_min n t ht hmin
  have hY : Podium.Y (ds n).length (Windows.Ids (ds n)) 1 = n + 1 - 2 ^ t := by omega
  obtain ⟨h1, -, h3⟩ := PodiumWalk.Z1 n hs
  rw [hY, htA] at h1 h3
  refine ⟨h1, ?_⟩
  rcases h3 with h | ⟨l, hl2, hl, h⟩
  · rw [h]; exact le_max_right _ _
  · rw [h]; exact ((B3 n hn).2 l hl2 hl).trans (le_max_left _ _)

/-- **(B4)** of `C36_the_podium_corollary.md`: for even `n ≥ 4`,
`φ(n) − 1 ≤ yPool0 (ds n) 0 ≤ max G (φ(n) − 1)` (`t₁ = 0`, `Y_1 = n`). -/
theorem B4 (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    Rulers.phi n - 1 ≤ FamilyGroup.yPool0 (ds n) 0 ∧
      FamilyGroup.yPool0 (ds n) 0 ≤ max (gmax (n - 1)) (Rulers.phi n - 1) := by
  obtain ⟨l, hl⟩ : ∃ l, n = 2 * l + 2 := ⟨n / 2 - 1, by omega⟩
  have h0 : 0 ∈ Windows.Ids (ds n) := hl ▸ zero_mem_even l
  have := B_Z n 0 hn h0 (fun u _ => Nat.zero_le u)
  simpa only [pow_zero, Nat.add_sub_cancel] using this

/-- `1 ∈ I` and `0 ∉ I` for `n ≡ 1 (mod 4)`, `n ≥ 5` (auxiliary for (B5) of
`C36_the_podium_corollary.md`). -/
lemma one_min_of_mod_four (n : ℕ) (hn : 4 ≤ n) (h : n % 4 = 1) :
    1 ∈ Windows.Ids (ds n) ∧ ∀ u ∈ Windows.Ids (ds n), 1 ≤ u := by
  obtain ⟨l, hl⟩ : ∃ l, n = 2 * (2 * l + 2) + 1 := ⟨(n - 5) / 4, by omega⟩
  subst hl
  refine ⟨(mem_Ids_odd _ 1).2 ⟨0, zero_mem_even l, rfl⟩, fun u hu => ?_⟩
  obtain ⟨w, -, rfl⟩ := (mem_Ids_odd _ u).1 hu
  omega

/-- **(B5)** of `C36_the_podium_corollary.md`: for `n ≥ 4` with `n % 4 = 1`,
`φ(n − 1) − 2 ≤ yPool0 (ds n) 0 ≤ max G (φ(n − 1) − 2)` (`t₁ = 1`, `Y_1 = n − 1`). -/
theorem B5 (n : ℕ) (hn : 4 ≤ n) (h4 : n % 4 = 1) :
    Rulers.phi (n - 1) - 2 ≤ FamilyGroup.yPool0 (ds n) 0 ∧
      FamilyGroup.yPool0 (ds n) 0 ≤ max (gmax (n - 1)) (Rulers.phi (n - 1) - 2) := by
  obtain ⟨h1, hmin⟩ := one_min_of_mod_four n hn h4
  have := B_Z n 1 hn h1 hmin
  simpa only [pow_one, show n + 1 - 2 = n - 1 by omega] using this

/-- All elements of `I` are `≥ 2` for `n ≡ 3 (mod 4)` (auxiliary for (B6) of
`C36_the_podium_corollary.md`). -/
lemma two_le_of_mod_four (n : ℕ) (h : n % 4 = 3) : ∀ u ∈ Windows.Ids (ds n), 2 ≤ u := by
  obtain ⟨l, hl⟩ : ∃ l, n = 2 * (2 * l + 1) + 1 := ⟨n / 4, by omega⟩
  subst hl
  intro u hu
  obtain ⟨w, hw, rfl⟩ := (mem_Ids_odd _ u).1 hu
  obtain ⟨w', -, rfl⟩ := (mem_Ids_odd _ w).1 hw
  omega

/-- **(B6)** of `C36_the_podium_corollary.md`: for `n ≥ 4` with `n % 4 = 3` and `1 ≤ s`,
`yPool0 (ds n) 0 ≤ G` (`t₁ ≥ 2`, so `φ(Y_1) − 2^{t₁} ≤ φ(Y_1) ≤ G` with `Y_1 ≤ n − 3`). -/
theorem B6 (n : ℕ) (hn : 4 ≤ n) (h4 : n % 4 = 3) (hs : 1 ≤ (Windows.Ids (ds n)).card) :
    FamilyGroup.yPool0 (ds n) 0 ≤ gmax (n - 1) := by
  have hne : (Windows.Ids (ds n)).Nonempty := card_pos.1 hs
  obtain ⟨t, ht, hmin⟩ : ∃ t ∈ Windows.Ids (ds n), ∀ u ∈ Windows.Ids (ds n), t ≤ u :=
    ⟨Rulers.minOr (ds n).length _, Rulers.minOr_mem hne, fun u hu => Rulers.minOr_le hu⟩
  have ht2 := two_le_of_mod_four n h4 t ht
  obtain ⟨hY1, -⟩ := Y_one_of_min n t ht hmin
  have hYp := Y_pos (ds n).length (Windows.Ids (ds n)) 1
  have h4t : 4 ≤ 2 ^ t := (Nat.pow_le_pow_right (by norm_num) ht2).trans_eq' (by norm_num)
  obtain ⟨-, hup⟩ := B_Z n t hn ht hmin
  have hphi : Rulers.phi (n + 1 - 2 ^ t) ≤ gmax (n - 1) := le_gmax _ _ (by omega) (by omega)
  have h2t : (0 : ℤ) ≤ 2 ^ t := by positivity
  exact hup.trans (max_le le_rfl (by linarith))

/-- **(B7)** of `C36_the_podium_corollary.md`: for even `n ≥ 4`,
`yPool (ds (n − 2)) 1 0 = G`, `yPool (ds (n − 2)) 1 1 = G` and `N ≥ 2` for the family `n − 2`
(C35b (T1), (T3), with `φ(n − 1) = n − 1 ≤ φ(n − 2)`). -/
theorem B7 (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    FamilyGroup.yPool (ds (n - 2)) 1 0 = gmax (n - 1) ∧
      FamilyGroup.yPool (ds (n - 2)) 1 1 = gmax (n - 1) ∧
        2 ≤ 2 ^ Dance.mCount (ds (n - 2)) := by
  obtain ⟨l, hl⟩ : ∃ l, n - 2 = 2 * l + 2 := ⟨n / 2 - 2, by omega⟩
  have h0 : 0 ∈ Windows.Ids (ds (n - 2)) := hl ▸ zero_mem_even l
  have hs : 1 ≤ (Windows.Ids (ds (n - 2))).card := card_pos.2 ⟨0, h0⟩
  have hphi1 : Rulers.phi (n - 1) ≤ gmax (n - 1) := by
    rw [phi_odd _ (by omega)]
    have := le_gmax (n - 1) (n - 2) (by omega) (by omega)
    have := phi_even (n - 2) (by omega) (by omega)
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [(B2 n hn).1, max_eq_left hphi1]
  · obtain ⟨⟨l₁, hl1, hl, he1⟩, hall⟩ := PodiumWalk.T3 (n - 2) h0
    obtain ⟨hY1, -⟩ := Y_one_of_min (n - 2) 0 h0 (fun u _ => Nat.zero_le u)
    refine le_antisymm ?_ (gmax_le_of _ (by omega) _ fun y hy1 hy2 => ?_)
    · rw [he1]
      have := Y_le_self (n - 2) l₁ hl1 hl
      exact le_gmax _ _ (Y_pos _ _ _) (by omega)
    · obtain ⟨l', hl1', hl', hle⟩ := Podium.Ld_one (MainTheorem.S3_subset (n - 2)) hs y hy1
        (by rw [pow_zero] at hY1; omega)
      exact hle.trans (hall l' hl1' hl')
  · rw [← MainTheorem.S3_card]
    exact (Nat.pow_le_pow_right (by norm_num) hs).trans_eq' (by norm_num)

/-- **(B8)** of `C36_the_podium_corollary.md`: for odd `n ≥ 4`, `yPool (ds (n − 4)) 2 0 = G`
((W2), C35b (T1), C35 (Ld): it is `g(n − 2)`, which is `G` since `φ(n − 2) = n − 2 ≤ φ(n − 3)`). -/
theorem B8 (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) :
    FamilyGroup.yPool (ds (n - 4)) 2 0 = gmax (n - 1) := by
  rw [W2 (n - 4) (by omega)]
  obtain ⟨⟨l₀, hl₀, he⟩, hall⟩ := PodiumWalk.T1 (n - 4)
  have hlow : ∀ y, 1 ≤ y → y ≤ n - 3 → Rulers.phi y ≤ FamilyGroup.yPool (ds (n - 4)) 1 0 :=
    fun y hy1 hy2 => by
      obtain ⟨l, hl, hle⟩ := Ld_fam (n - 4) y hy1 (by omega)
      exact hle.trans (hall l hl)
  refine le_antisymm ?_ (gmax_le_of _ (by omega) _ fun y hy1 hy2 => ?_)
  · rw [he]
    have := Y_le_succ (n - 4) l₀
    exact le_gmax _ _ (Y_pos _ _ _) (by omega)
  · rcases Nat.lt_or_ge y (n - 2) with h | h
    · exact hlow y hy1 (by omega)
    · rw [show y = n - 2 by omega, phi_odd _ (by omega)]
      have := hlow (n - 3) (by omega) le_rfl
      have := phi_even (n - 3) (by omega) (by omega)
      omega

end PodiumCor
