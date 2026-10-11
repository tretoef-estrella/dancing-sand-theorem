module

public import RequestProject.Rulers.All

/-!
# `C37_the_mirror_that_doubles.md`: Part B — Lemma 9.9 (the raw clocks of the two cubes)

Namespace `Mirror`.  C3's `Rulers.clock`, `xi`, `lam`, `phi`, `kappa`, `s2`, `v2`, `oE`, `hSum`
are used directly.  The family is `k : ℕ`, `I ⊆ Finset.range k`, a dancer `D ⊆ I` and a shift
`i : ℕ`; `J := i + Rulers.oE D` is written out as `i + Rulers.oE D` (a natural number).  The
identities are identities in `ℤ`; `J − 1` in (B2) is the natural-number subtraction (harmless,
since `J ≥ 1`).
-/

@[expose] public section

namespace Mirror

open Finset Rulers

/-- `s₂((2^f − 1) − b) + s₂(b) = f` for `b < 2^f` (the binary complement; auxiliary for Part B of
`C37_the_mirror_that_doubles.md`). -/
lemma s2_complement (f : ℕ) : ∀ b, b < 2 ^ f → s2 (2 ^ f - 1 - b) + s2 b = f := by
  induction f with
  | zero => intro b hb; simp at hb; subst hb; simp
  | succ f ih =>
    intro b hb
    have hb2 : b / 2 < 2 ^ f := by rw [pow_succ] at hb; omega
    have e1 : 2 ^ (f + 1) - 1 - b = (1 - b % 2) + 2 * (2 ^ f - 1 - b / 2) := by
      rw [pow_succ]; omega
    have e2 : b = b % 2 + 2 * (b / 2) := (Nat.mod_add_div b 2).symm
    have hsb : s2 b = b % 2 + s2 (b / 2) := by
      have := s2_bit (b % 2) (b / 2) (Nat.mod_lt _ (by norm_num)); rwa [← e2] at this
    rw [e1, s2_bit _ _ (by omega), hsb]
    have := ih (b / 2) hb2
    have : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

/-- `v₂(2^f − J) = v₂(J)` for `1 ≤ J < 2^f` (auxiliary for Part B of
`C37_the_mirror_that_doubles.md`). -/
lemma v2_complement (f J : ℕ) (h1 : 1 ≤ J) (h2 : J < 2 ^ f) : v2 (2 ^ f - J) = v2 J := by
  have a := s2_succ (J - 1)
  rw [Nat.sub_add_cancel h1] at a
  have b := s2_succ (2 ^ f - J - 1)
  rw [Nat.sub_add_cancel (by omega)] at b
  have c := s2_complement f (J - 1) (by omega)
  rw [show 2 ^ f - 1 - (J - 1) = 2 ^ f - J by omega] at c
  have d := s2_complement f J h2
  rw [show 2 ^ f - 1 - J = 2 ^ f - J - 1 by omega] at d
  have c' : ((s2 (2 ^ f - J) : ℕ) : ℤ) + s2 (J - 1) = f := by exact_mod_cast c
  have d' : ((s2 (2 ^ f - J - 1) : ℕ) : ℤ) + s2 J = f := by exact_mod_cast d
  have : ((v2 (2 ^ f - J) : ℕ) : ℤ) = v2 J := by linarith
  exact_mod_cast this

/-- `v₂(2x) = v₂(x) + 1` for `x ≥ 1` (auxiliary for Part B of
`C37_the_mirror_that_doubles.md`). -/
lemma v2_two_mul {x : ℕ} (hx : 1 ≤ x) : v2 (2 * x) = v2 x + 1 := by
  unfold v2
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num), add_comm]

/-- `v₂` of an odd number is `0` (auxiliary for Part B of `C37_the_mirror_that_doubles.md`). -/
lemma v2_two_mul_add_one (x : ℕ) : v2 (2 * x + 1) = 0 := by
  unfold v2
  exact padicValNat.eq_zero_of_not_dvd (by omega)

/-- `o_D ≤ o_I < 2^k` for `D ⊆ I ⊆ range k` (auxiliary for Part B of
`C37_the_mirror_that_doubles.md`). -/
lemma oE_bounds {k : ℕ} {I D : Finset ℕ} (hI : I ⊆ range k) (hD : D ⊆ I) :
    oE D ≤ oE I ∧ oE I < 2 ^ k :=
  ⟨sum_le_sum_of_subset hD, oE_lt I k fun _ ht => mem_range.1 (hI ht)⟩

/-- **(B1)** of `C37_the_mirror_that_doubles.md` (Lemma 9.9, the cube `N`): let
`I ⊆ range k`, `D ⊆ I`, `J := i + o_D`.  If `2^k + o_I + 2i = 2^e` and `1 ≤ J`, then
`Rulers.clock k I i D = 2^e − 2J + v₂(J) + s₂(J) + h(D)` (in `ℤ`). -/
theorem B1 (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) {D : Finset ℕ} (hD : D ⊆ I) (i e : ℕ)
    (hsum : 2 ^ k + oE I + 2 * i = 2 ^ e) (hJ : 1 ≤ i + oE D) :
    clock k I i D = (2 : ℤ) ^ e - 2 * ((i + oE D : ℕ) : ℤ) + (v2 (i + oE D) : ℤ) +
      (s2 (i + oE D) : ℤ) + (hSum k I D : ℤ) := by
  obtain ⟨hDI, hIk⟩ := oE_bounds hI hD
  set J := i + oE D with hJdef
  have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2J : 2 * J < 2 ^ e := by omega
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := by
    rcases e with _ | f
    · simp at h2J; omega
    · exact ⟨f, rfl⟩
  rw [pow_succ] at h2J hsum
  have hJf : J < 2 ^ f := by omega
  obtain ⟨X, hX⟩ : ∃ X, X + J = 2 ^ f := ⟨2 ^ f - J, by omega⟩
  have hX1 : 1 ≤ X := by omega
  have hxi : xi k I D = 2 * X := by unfold xi lam; omega
  have hv : v2 (2 * X) = v2 J + 1 := by
    rw [v2_two_mul hX1, show X = 2 ^ f - J by omega, v2_complement f J hJ hJf]
  have hs1 : s2 (2 * X) = s2 X := by simpa using s2_bit 0 X (by norm_num)
  have hs2 : s2 X + s2 (J - 1) = f := by
    rw [show X = 2 ^ f - 1 - (J - 1) by omega]; exact s2_complement f (J - 1) (by omega)
  have hs3 : s2 (J - 1 + 2 * X) + s2 J = f + 1 := by
    rw [show J - 1 + 2 * X = 2 ^ (f + 1) - 1 - J by rw [pow_succ]; omega]
    exact s2_complement (f + 1) J (by rw [pow_succ]; omega)
  have hsJ := s2_succ (J - 1)
  rw [Nat.sub_add_cancel hJ] at hsJ
  unfold clock phi kappa
  rw [hxi, hv, hs1]
  have hs2' : ((s2 X : ℕ) : ℤ) + s2 (J - 1) = f := by exact_mod_cast hs2
  have hs3' : ((s2 (J - 1 + 2 * X) : ℕ) : ℤ) + s2 J = f + 1 := by exact_mod_cast hs3
  have hX' : ((X : ℕ) : ℤ) + J = (2 : ℤ) ^ f := by exact_mod_cast hX
  push_cast
  rw [pow_succ]
  linarith

/-- **(B2)** of `C37_the_mirror_that_doubles.md` (Lemma 9.9, the cube `n`): let
`I ⊆ range k`, `D ⊆ I`, `J := i + o_D`.  If `2^k + o_I + 2i = 2^e + 1` and `1 ≤ J`, then
`Rulers.clock k I i D = 2^e + 1 − 2J + s₂(J − 1) + h(D)` (in `ℤ`). -/
theorem B2 (k : ℕ) (I : Finset ℕ) (hI : I ⊆ range k) {D : Finset ℕ} (hD : D ⊆ I) (i e : ℕ)
    (hsum : 2 ^ k + oE I + 2 * i = 2 ^ e + 1) (hJ : 1 ≤ i + oE D) :
    clock k I i D = (2 : ℤ) ^ e + 1 - 2 * ((i + oE D : ℕ) : ℤ) + (s2 (i + oE D - 1) : ℤ) +
      (hSum k I D : ℤ) := by
  obtain ⟨hDI, hIk⟩ := oE_bounds hI hD
  set J := i + oE D with hJdef
  have hK : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2J : 2 * J ≤ 2 ^ e := by omega
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := by
    rcases e with _ | f
    · simp at h2J; omega
    · exact ⟨f, rfl⟩
  rw [pow_succ] at h2J hsum
  have hJf : J ≤ 2 ^ f := by omega
  obtain ⟨X, hX⟩ : ∃ X, X + J = 2 ^ f := ⟨2 ^ f - J, by omega⟩
  have hxi : xi k I D = 2 * X + 1 := by unfold xi lam; omega
  have hs1 : s2 (2 * X + 1) = s2 X + 1 := by
    rw [show 2 * X + 1 = 1 + 2 * X by ring, s2_bit 1 X (by norm_num), add_comm]
  have hs2 : s2 X + s2 (J - 1) = f := by
    rw [show X = 2 ^ f - 1 - (J - 1) by omega]; exact s2_complement f (J - 1) (by omega)
  have hs3 : s2 (J - 1 + (2 * X + 1)) + s2 (J - 1) = f + 1 := by
    rw [show J - 1 + (2 * X + 1) = 2 ^ (f + 1) - 1 - (J - 1) by rw [pow_succ]; omega]
    exact s2_complement (f + 1) (J - 1) (by rw [pow_succ]; omega)
  unfold clock phi kappa
  rw [hxi, v2_two_mul_add_one, hs1]
  have hs2' : ((s2 X : ℕ) : ℤ) + s2 (J - 1) = f := by exact_mod_cast hs2
  have hs3' : ((s2 (J - 1 + (2 * X + 1)) : ℕ) : ℤ) + s2 (J - 1) = f + 1 := by exact_mod_cast hs3
  have hX' : ((X : ℕ) : ℤ) + J = (2 : ℤ) ^ f := by exact_mod_cast hX
  push_cast
  rw [pow_succ]
  linarith

end Mirror
