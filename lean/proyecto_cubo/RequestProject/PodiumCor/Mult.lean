module

public import RequestProject.FamDec.All

/-!
# `C36_the_podium_corollary.md`: Part L — Lemma 9.7 (multiplicities)

Encodings: `FamDec.m μ n = (FamDec.L n).count μ` is the multiplicity of the family `μ` in
`V^{⊗ n}` (C31), `FamDec.Vdot` is C31's `V̇`, and `L (n + 1) = (L n).flatMap Vdot`.  The bracket
`[P]` is `if P then 1 else 0`.  Natural-number subtraction is used as in the file; it never
truncates in the stated ranges.
-/

@[expose] public section

namespace PodiumCor

open FamDec

/-- `2l + 1` occurs twice in `Vdot (2l + 2)` (auxiliary for Part L of
`C36_the_podium_corollary.md`). -/
lemma count_Vdot_pred (l : ℕ) : (Vdot (2 * l + 2)).count (2 * l + 1) = 2 := by
  rw [Vdot_even, List.count_append, count_map_odd]
  have : (Vdot l).count l = 0 :=
    List.count_eq_zero.2 fun h => by have := (mem_Vdot l l h).2.2; omega
  simp [this]

/-- `2l + 1` occurs in `Vdot (2l + 4)` twice if `l` is odd and never if `l` is even (auxiliary for
Part L of `C36_the_podium_corollary.md`). -/
lemma count_Vdot_pred3 (l : ℕ) :
    (Vdot (2 * l + 4)).count (2 * l + 1) = if l % 2 = 1 then 2 else 0 := by
  rw [show 2 * l + 4 = 2 * (l + 1) + 2 by ring, Vdot_even, List.count_append, count_map_odd]
  have h0 : [2 * (l + 1) + 1, 2 * (l + 1) + 1].count (2 * l + 1) = 0 := by simp
  rw [h0, zero_add]
  rcases Nat.even_or_odd' l with ⟨a, rfl | rfl⟩
  · rw [if_neg (by omega), Vdot_odd]; simp
  · rw [if_pos (by omega), show 2 * a + 1 + 1 = 2 * a + 2 by ring, count_Vdot_pred]

/-- The multiplicity of `n − 1` in `Vdot λ` for `λ` in the support of `L n` (auxiliary for (L2) of
`C36_the_podium_corollary.md`). -/
lemma count_Vdot_L2 (n lam : ℕ) (hn : 2 ≤ n) (h : 1 ≤ lam ∧ lam ≤ n ∧ lam % 2 = n % 2) :
    (Vdot lam).count (n - 1) =
      (if lam = n - 2 then 1 else 0) + (if lam = n then (if n % 2 = 0 then 2 else 0) else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hl : lam = n
  · subst hl
    rw [if_neg (by omega), if_pos rfl, zero_add]
    rcases Nat.even_or_odd' lam with ⟨a, rfl | rfl⟩
    · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [if_pos (by omega), show 2 * (b + 1) = 2 * b + 2 by ring,
        show 2 * b + 2 - 1 = 2 * b + 1 by omega, count_Vdot_pred]
    · rw [if_neg (by omega), Vdot_odd]; simp
  · rw [if_neg hl, add_zero]
    by_cases hl2 : lam = n - 2
    · rw [if_pos hl2, show n - 1 = lam + 1 by omega, count_succ_Vdot]
    · rw [if_neg hl2]
      apply List.count_eq_zero.2
      intro hm
      have := mem_Vdot lam _ hm
      omega

/-- The recursion `m (n − 1) (n + 1) = m (n − 2) n + 2 [n even]` for `n ≥ 2` (auxiliary for (L2) of
`C36_the_podium_corollary.md`). -/
lemma m_L2_step (n : ℕ) (hn : 2 ≤ n) :
    m (n - 1) (n + 1) = m (n - 2) n + (if n % 2 = 0 then 2 else 0) := by
  unfold m
  rw [count_L_succ, List.map_congr_left (fun lam hlam =>
      count_Vdot_L2 n lam hn (M3 n (by omega) lam hlam)), List.sum_map_add,
    sum_map_eq_count_mul _ _ (n - 2) 1 (fun _ _ => rfl),
    sum_map_eq_count_mul _ _ n _ (fun _ _ => rfl)]
  have := m_self n
  unfold m at this
  rw [this]
  simp

/-- **(L1)** of `C36_the_podium_corollary.md` (Lemma 9.7): `m n n = 1` for `n ≥ 1`.  (The
hypothesis `1 ≤ n` is not needed: C31 `m_self` holds for every `n`.) -/
theorem L1 (n : ℕ) (_hn : 1 ≤ n) : m n n = 1 := m_self n

/-- **(L2)** of `C36_the_podium_corollary.md` (Lemma 9.7): for `n ≥ 2`,
`m (n − 2) n = n − 1 − [n even]`. -/
theorem L2 (n : ℕ) (hn : 2 ≤ n) : m (n - 2) n = n - 1 - (if n % 2 = 0 then 1 else 0) := by
  induction n, hn using Nat.le_induction with
  | base => rw [show (2 : ℕ) - 2 = 0 from rfl, FamDec.L1 2 (by omega)]; rfl
  | succ n hn ih =>
    rw [show n + 1 - 2 = n - 1 by omega, m_L2_step n hn, ih]
    split_ifs <;> omega

/-- The multiplicity of `N − 3` in `Vdot λ` for `λ` in the support of `L N`, `N` even `≥ 4`
(auxiliary for (L3) of `C36_the_podium_corollary.md`). -/
lemma count_Vdot_L3a (N lam : ℕ) (hN : 4 ≤ N) (he : N % 2 = 0)
    (h : 1 ≤ lam ∧ lam ≤ N ∧ lam % 2 = N % 2) :
    (Vdot lam).count (N - 3) = (if lam = N - 4 then 1 else 0) + (if lam = N - 2 then 2 else 0) +
      (if lam = N then (if N % 4 = 2 then 2 else 0) else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  by_cases hl : lam = N
  · subst hl
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 4 := ⟨lam / 2 - 2, by omega⟩
    rw [show 2 * l + 4 - 3 = 2 * l + 1 by omega, count_Vdot_pred3]
    split_ifs <;> omega
  · by_cases hl2 : lam = N - 2
    · rw [if_neg (by omega), if_pos hl2, if_neg hl]
      obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 2 := ⟨lam / 2 - 1, by omega⟩
      rw [show N - 3 = 2 * l + 1 by omega, count_Vdot_pred]
    · rw [if_neg hl2, if_neg hl]
      by_cases hl4 : lam = N - 4
      · rw [if_pos hl4, show N - 3 = lam + 1 by omega, count_succ_Vdot]
      · rw [if_neg hl4]
        apply List.count_eq_zero.2
        intro hm
        have := mem_Vdot lam _ hm
        omega

/-- The recursion `m (N − 3) (N + 1) = m (N − 4) N + 2 m (N − 2) N + 2 [N ≡ 2 mod 4]` for even
`N ≥ 4` (auxiliary for (L3) of `C36_the_podium_corollary.md`). -/
lemma m_L3_stepA (N : ℕ) (hN : 4 ≤ N) (he : N % 2 = 0) :
    m (N - 3) (N + 1) = m (N - 4) N + 2 * m (N - 2) N + (if N % 4 = 2 then 2 else 0) := by
  unfold m
  rw [count_L_succ, List.map_congr_left (fun lam hlam =>
      count_Vdot_L3a N lam hN he (M3 N (by omega) lam hlam)), List.sum_map_add,
    List.sum_map_add, sum_map_eq_count_mul _ _ (N - 4) 1 (fun _ _ => rfl),
    sum_map_eq_count_mul _ _ (N - 2) 2 (fun _ _ => rfl),
    sum_map_eq_count_mul _ _ N _ (fun _ _ => rfl)]
  have := m_self N
  unfold m at this
  rw [this]
  ring

/-- The recursion `m (M − 3) (M + 1) = m (M − 4) M` for odd `M ≥ 5` (auxiliary for (L3) of
`C36_the_podium_corollary.md`). -/
lemma m_L3_stepB (M : ℕ) (hM : 5 ≤ M) (ho : M % 2 = 1) : m (M - 3) (M + 1) = m (M - 4) M := by
  unfold m
  rw [count_L_succ, List.map_congr_left (g := fun lam => if lam = M - 4 then 1 else 0)
      (fun lam hlam => ?_), sum_map_eq_count_mul _ _ (M - 4) 1 (fun _ _ => rfl), mul_one]
  obtain ⟨h1, h2, h3⟩ := M3 M (by omega) lam hlam
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  rw [Vdot_odd]
  dsimp only
  by_cases hl : 2 * l + 1 = M - 4
  · rw [if_pos hl, show M - 3 = 2 * l + 2 by omega, List.count_singleton_self]
  · rw [if_neg hl, List.count_eq_zero]
    simp only [List.mem_singleton]
    omega

/-- (L3) of `C36_the_podium_corollary.md` in the parametrization `n = 2j + 5`:
`m (2j + 1) (2j + 5) = (j + 2)(2j + 3) − 1 − [j even]` (auxiliary). -/
lemma m_L3_param (j : ℕ) :
    m (2 * j + 1) (2 * j + 5) = (j + 2) * (2 * j + 3) - 1 - (if j % 2 = 0 then 1 else 0) := by
  induction j with
  | zero =>
    have h := m_L3_stepA 4 (by omega) (by omega)
    rw [show (4 : ℕ) - 4 = 0 from rfl, FamDec.L1 4 (by omega),
      show (4 : ℕ) - 2 = 2 from rfl, show m 2 4 = 2 by
        have := L2 4 (by omega); simpa using this] at h
    simpa using h
  | succ j ih =>
    have hA := m_L3_stepA (2 * j + 6) (by omega) (by omega)
    have hB := m_L3_stepB (2 * j + 5) (by omega) (by omega)
    have h2 := L2 (2 * j + 6) (by omega)
    rw [show 2 * j + 6 - 4 = 2 * j + 2 by omega, show 2 * j + 6 - 2 = 2 * j + 4 by omega,
      show 2 * j + 6 - 3 = 2 * j + 3 by omega, show 2 * j + 6 + 1 = 2 * j + 7 by omega] at hA
    rw [show 2 * j + 5 - 3 = 2 * j + 2 by omega, show 2 * j + 5 - 4 = 2 * j + 1 by omega,
      show 2 * j + 5 + 1 = 2 * j + 6 by omega] at hB
    rw [show 2 * j + 6 - 2 = 2 * j + 4 by omega] at h2
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, show 2 * (j + 1) + 5 = 2 * j + 7 by ring, hA,
      hB, ih, h2]
    have e : (j + 1 + 2) * (2 * (j + 1) + 3) = (j + 2) * (2 * j + 3) + 4 * j + 9 := by ring
    rw [e]
    have : 6 ≤ (j + 2) * (2 * j + 3) := by nlinarith
    split_ifs <;> omega

/-- **(L3)** of `C36_the_podium_corollary.md` (Lemma 9.7): for odd `n ≥ 5`,
`m (n − 4) n = (n − 1)(n − 2)/2 − 1 − [n % 4 = 1]`, and this is `≥ 4`. -/
theorem L3 (n : ℕ) (hn : 5 ≤ n) (ho : n % 2 = 1) :
    m (n - 4) n = (n - 1) * (n - 2) / 2 - 1 - (if n % 4 = 1 then 1 else 0) ∧ 4 ≤ m (n - 4) n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = 2 * j + 5 := ⟨(n - 5) / 2, by omega⟩
  have hj : (2 * j + 5 - 1) * (2 * j + 5 - 2) / 2 = (j + 2) * (2 * j + 3) := by
    rw [show (2 * j + 5 - 1) * (2 * j + 5 - 2) = 2 * ((j + 2) * (2 * j + 3)) by
      rw [show 2 * j + 5 - 1 = 2 * (j + 2) by omega, show 2 * j + 5 - 2 = 2 * j + 3 by omega]; ring]
    omega
  rw [show 2 * j + 5 - 4 = 2 * j + 1 by omega, m_L3_param, hj]
  have : 6 ≤ (j + 2) * (2 * j + 3) := by nlinarith
  refine ⟨?_, ?_⟩
  · by_cases hj2 : j % 2 = 0
    · rw [if_pos hj2, if_pos (by omega)]
    · rw [if_neg hj2, if_neg (by omega)]
  · split_ifs <;> omega

end PodiumCor
