module

public import RequestProject.PodiumCor.Defs

/-!
# `C36_the_podium_corollary.md`: Part W — the shift-2 clocks of an odd family

Encodings: `Rulers.clock k I i D = φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)` (C3), with
`ξ_D = Rulers.xi k I D = λ + 1 − 2 o_D`; the family `λ` has `d = Families.ds lam`, and the pooled
clocks are `FamilyGroup.yPool d i : ℕ → ℤ` (C16), compared as functions.
-/

@[expose] public section

namespace PodiumCor

open Finset

/-- `s_2(2x) = s_2(x)` (auxiliary for Part W of `C36_the_podium_corollary.md`). -/
lemma s2_double (x : ℕ) : Rulers.s2 (2 * x) = Rulers.s2 x := by
  have := Rulers.s2_bit 0 x (by norm_num)
  simpa using this

/-- `s_2(2x + 1) = s_2(x) + 1` (auxiliary for Part W of `C36_the_podium_corollary.md`). -/
lemma s2_double_add_one (x : ℕ) : Rulers.s2 (2 * x + 1) = Rulers.s2 x + 1 := by
  have := Rulers.s2_bit 1 x (by norm_num)
  rw [add_comm 1 (2 * x)] at this
  omega

/-- For even `a`, `b`: `κ(a + 1, b) = κ(a, b)` (adding `1` to an even number creates no carry;
auxiliary for (W1) of `C36_the_podium_corollary.md`). -/
lemma kappa_succ_of_even (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    Rulers.kappa (a + 1) b = Rulers.kappa a b := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 * x := ⟨a / 2, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 2 * y := ⟨b / 2, by omega⟩
  unfold Rulers.kappa
  rw [show 2 * x + 1 + 2 * y = 2 * (x + y) + 1 by ring, show 2 * x + 2 * y = 2 * (x + y) by ring]
  simp only [s2_double_add_one, s2_double]
  push_cast
  ring

/-- `o_E` is even when `0 ∉ E` (auxiliary for (W1) of `C36_the_podium_corollary.md`). -/
lemma oE_even {E : Finset ℕ} (h0 : 0 ∉ E) : Rulers.oE E % 2 = 0 := by
  have := Podium.two_pow_dvd_oE (S := E) (q := 1) fun t ht => by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exact absurd ht h0
    · exact h
  omega

/-- **(W1)** of `C36_the_podium_corollary.md`: if `1 ≤ k`, `0 ∉ I` and `D ⊆ I`, then
`clock k I 2 D = clock k I 1 D`. -/
theorem W1 (k : ℕ) (I D : Finset ℕ) (hk : 1 ≤ k) (h0 : 0 ∉ I) (hD : D ⊆ I) :
    Rulers.clock k I 2 D = Rulers.clock k I 1 D := by
  unfold Rulers.clock
  have hoD : Rulers.oE D % 2 = 0 := oE_even fun h => h0 (hD h)
  have hoI : Rulers.oE I % 2 = 0 := oE_even h0
  have hK : 2 ^ k % 2 = 0 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]; omega
  have hxi : Rulers.xi k I D % 2 = 0 := by
    unfold Rulers.xi
    rw [Podium.lam_add_one]
    omega
  rw [show 2 + Rulers.oE D - 1 = Rulers.oE D + 1 by omega,
    show 1 + Rulers.oE D - 1 = Rulers.oE D by omega, kappa_succ_of_even _ _ hoD hxi]

/-- For odd `λ`, `0 ∉ I` and `1 ≤ k` (auxiliary for (W2) of `C36_the_podium_corollary.md`). -/
lemma odd_family (l : ℕ) :
    1 ≤ (Families.ds (2 * l + 1)).length ∧ 0 ∉ Windows.Ids (Families.ds (2 * l + 1)) := by
  rw [Families.ds_odd, Windows.Ids_cons]
  simp

/-- **(W2)** of `C36_the_podium_corollary.md`: for odd `λ`,
`yPool (ds λ) 2 = yPool (ds λ) 1` (as functions). -/
theorem W2 (lam : ℕ) (ho : lam % 2 = 1) :
    FamilyGroup.yPool (Families.ds lam) 2 = FamilyGroup.yPool (Families.ds lam) 1 := by
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  obtain ⟨hk, h0⟩ := odd_family l
  unfold FamilyGroup.yPool
  congr 1
  funext j
  exact W1 _ _ _ hk h0 (filter_subset _ _)

end PodiumCor
