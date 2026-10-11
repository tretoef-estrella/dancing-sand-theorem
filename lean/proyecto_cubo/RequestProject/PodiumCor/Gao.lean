module

public import RequestProject.PodiumCor.Corollary

/-!
# `C36_the_podium_corollary.md`: Part G — the statements of Gao et al. and of the poster

Encodings: `c r` is `cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r`, compared with integers
through `(c r : ℤ)`; `v_2 = Rulers.v2` (natural-number valued, cast to `ℤ`), `gmax`, `φ = Rulers.phi`.
`v2 n + n − 1` is computed in `ℤ`.
-/

@[expose] public section

namespace PodiumCor

open Finset Families

/-! ### The case `n = 3` -/

/-- `ds 1 = [false]` (auxiliary for Part G of `C36_the_podium_corollary.md`). -/
lemma ds_one : ds 1 = [false] := by rw [show 1 = 2 * 0 + 1 by rfl, ds_odd, ds_zero]

/-- `ds 3 = [false, false]` (auxiliary for Part G of `C36_the_podium_corollary.md`). -/
lemma ds_three : ds 3 = [false, false] := by rw [show 3 = 2 * 1 + 1 by rfl, ds_odd, ds_one]

/-- `L 3 = [1, 1, 3]` (auxiliary for Part G of `C36_the_podium_corollary.md`). -/
lemma L_three : FamDec.L 3 = [1, 1, 3] := by
  have v0 := FamDec.Vdot_zero
  have v1 : FamDec.Vdot 1 = [2] := FamDec.Vdot_odd 0
  have v2 : FamDec.Vdot 2 = [1, 1, 3] := by have := FamDec.Vdot_even 0; simpa [v0] using this
  rw [FamDec.L_succ, FamDec.L_succ, FamDec.L_succ, FamDec.L_zero]
  simp [v0, v1, v2]

/-- `φ(1) = 1` (auxiliary). -/
lemma phi_one : Rulers.phi 1 = 1 := by rw [phi_odd 1 rfl]; rfl

/-- `φ(2) = 3` (auxiliary). -/
lemma phi_two : Rulers.phi 2 = 3 := by
  unfold Rulers.phi; rw [v2_two_mod_four 2 (by norm_num)]; norm_num

/-- `gmax 2 = 1` (auxiliary for Part G of `C36_the_podium_corollary.md`). -/
lemma gmax_two : gmax 2 = 1 := by
  obtain ⟨x, h1, h2, he⟩ := (g0 2 le_rfl).1
  rw [he, show x = 1 by omega, phi_one]

/-- `gmax 3 = 3` (auxiliary for Part G of `C36_the_podium_corollary.md`). -/
lemma gmax_three : gmax 3 = 3 := by
  rw [gmax_succ 2 le_rfl, gmax_two, phi_two]; rfl

/-- `yPool (ds 1) 1 0 = 3` (from C35b (T1); auxiliary for Part G). -/
lemma yPool_ds_one : FamilyGroup.yPool (ds 1) 1 0 = 3 := by
  have hc : (Windows.Ids (ds 1)).card = 0 := by rw [ds_one]; decide
  obtain ⟨⟨l₀, hl₀, he⟩, -⟩ := PodiumWalk.T1 1
  rw [hc] at hl₀
  obtain rfl : l₀ = 0 := by omega
  rw [he, Y_zero, phi_two]

/-- `exps 3 = {3, 3, 1}`, i.e. `Syl_2 K(Q_3) ≅ ℤ/2 ⊕ (ℤ/8)^2` (auxiliary for Part G of
`C36_the_podium_corollary.md`). -/
lemma exps_three : exps 3 = {3} + ({3} + ({1} + 0)) := by
  have h1 : famExps 1 1 = {3} := by
    have hc : (Windows.Ids (ds 1)).card = 0 := by rw [ds_one]; decide
    have hl : (ds 1).length = 1 := by rw [ds_one]; rfl
    unfold famExps smallExps bigExps
    rw [hc, hl]
    simp [yPool_ds_one]
  have h3 : famExps 3 0 = {1} := by
    have hc : (Windows.Ids (ds 3)).card = 0 := by rw [ds_three]; decide
    have hl : (ds 3).length = 2 := by rw [ds_three]; rfl
    unfold famExps smallExps bigExps
    rw [hc, hl]
    simp
    rfl
  unfold exps
  rw [L_three]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [show (3 - 1) / 2 = 1 from rfl, show (3 - 3) / 2 = 0 from rfl, h1, h3]

/-- Reading off `c_r` from two counts, natural-number version (via (E2); auxiliary). -/
lemma cExp_eq_of_counts_nat (n r v : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hv : 1 ≤ v)
    (h1 : r ≤ (exps n).countP (fun x => v ≤ x)) (h2 : (exps n).countP (fun x => v + 1 ≤ x) < r) :
    cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r = v := by
  have a := (E2 n hn r v hr hv).2 h1
  have b : ¬ (v + 1 ≤ cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r) := fun h =>
    absurd ((E2 n hn r (v + 1) hr (by omega)).1 h) (by omega)
  omega

/-- `c 1 = c 2 = 3` and `c 3 = 1` for `n = 3` (auxiliary for Part G). -/
lemma cExp_three :
    cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 3)) 1 = 3 ∧
      cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 3)) 2 = 3 ∧
        cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 3)) 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · apply cExp_eq_of_counts_nat _ _ _ (by norm_num) (by norm_num) (by norm_num) <;>
    · rw [exps_three]; decide

/-! ### (G1), (G2), (G3) -/

/-- `v_2(n) + n − 1 = φ(n) − 1` (auxiliary). -/
lemma v2_add_eq (n : ℕ) : (Rulers.v2 n : ℤ) + n - 1 = Rulers.phi n - 1 := by
  unfold Rulers.phi; ring

/-- **(G1)** of `C36_the_podium_corollary.md` ([GMMY24, Theorems 4.1, 4.2]): for `n ≥ 3`,
`(c 1 : ℤ) = max (gmax n) (v_2(n) + n − 1)` and `(c r : ℤ) = gmax n` for `2 ≤ r ≤ n − 1`. -/
theorem G1 (n : ℕ) (hn : 3 ≤ n) :
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (gmax n) ((Rulers.v2 n : ℤ) + n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n - 1 →
        (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = gmax n := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn4
  · obtain ⟨c1, c2, -⟩ := cExp_three
    refine ⟨?_, fun r hr2 hr => ?_⟩
    · rw [c1, gmax_three, show Rulers.v2 3 = 0 by
        unfold Rulers.v2; exact padicValNat.eq_zero_of_not_dvd (by norm_num)]
      norm_num
    · rw [show r = 2 by omega, c2, gmax_three]; rfl
  have hgn : gmax n = max (gmax (n - 1)) (Rulers.phi (n - 1)) := by
    have := gmax_succ (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega] at this
  rw [v2_add_eq, hgn]
  have hG2 := gmax_ge (n - 1) (by omega)
  rcases Nat.mod_two_eq_zero_or_one n with hev | ho
  · have hphi1 : Rulers.phi (n - 1) ≤ gmax (n - 1) := by
      rw [phi_odd _ (by omega)]
      have := le_gmax (n - 1) (n - 2) (by omega) (by omega)
      have := phi_even (n - 2) (by omega) (by omega)
      omega
    obtain ⟨p1, p2⟩ := P1 n (by omega) hev
    rw [max_eq_left hphi1]
    exact ⟨p1, fun r hr2 hr => p2 r hr2 (by omega)⟩
  · have hphin : Rulers.phi n - 1 ≤ Rulers.phi (n - 1) := by
      rw [phi_odd n ho]
      have := phi_even (n - 1) (by omega) (by omega)
      push_cast [show (n - 1 : ℕ) = (n : ℤ) - 1 by omega] at this ⊢
      omega
    by_cases hc : Rulers.phi (n - 1) ≤ gmax (n - 1)
    · have p := P2 n (by omega) ho hc
      rw [max_eq_left hc, max_eq_left (hphin.trans hc)]
      exact ⟨p 1 le_rfl (by omega), fun r hr2 hr => p r (by omega) (by omega)⟩
    · push_neg at hc
      obtain ⟨p1, -, -⟩ := P3 n (by omega) ho hc
      rw [max_eq_right hc.le, max_eq_left hphin]
      exact ⟨p1 1 le_rfl (by omega), fun r hr2 hr => p1 r (by omega) hr⟩

/-- **(G2)** of `C36_the_podium_corollary.md` ([GMMY24, Conjecture 4.14]): for `n ≥ 3`,
`(c n : ℤ) = max (gmax (n − 1)) (v_2(n − 1) + n − 3)`. -/
theorem G2 (n : ℕ) (hn : 3 ≤ n) :
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) n : ℤ) =
      max (gmax (n - 1)) ((Rulers.v2 (n - 1) : ℤ) + n - 3) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn4
  · obtain ⟨-, -, c3⟩ := cExp_three
    rw [c3, show 3 - 1 = 2 from rfl, gmax_two, show Rulers.v2 2 = 1 from
      v2_two_mod_four 2 (by norm_num)]
    norm_num
  have hv : (Rulers.v2 (n - 1) : ℤ) + n - 3 = Rulers.phi (n - 1) - 2 := by
    unfold Rulers.phi; push_cast [show (n - 1 : ℕ) = (n : ℤ) - 1 by omega]; ring
  rw [hv]
  have hG2 := gmax_ge (n - 1) (by omega)
  rcases Nat.mod_two_eq_zero_or_one n with hev | ho
  · have hphi1 : Rulers.phi (n - 1) - 2 ≤ gmax (n - 1) := by
      rw [phi_odd _ (by omega)]
      push_cast [show (n - 1 : ℕ) = (n : ℤ) - 1 by omega] at hG2 ⊢
      omega
    rw [(P1 n (by omega) hev).2 n (by omega) (by omega), max_eq_left hphi1]
  · by_cases hc : Rulers.phi (n - 1) ≤ gmax (n - 1)
    · rw [P2 n (by omega) ho hc n (by omega) (by omega), max_eq_left (by linarith)]
    · push_neg at hc
      exact (P3 n (by omega) ho hc).2.1

/-- **(G3)** of `C36_the_podium_corollary.md` ([MGM19], the `(n + 1)`-th factor of the poster):
for `n ≥ 4`, `(c (n + 1) : ℤ) = gmax (n − 1)`. -/
theorem G3 (n : ℕ) (hn : 4 ≤ n) :
    (cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) (n + 1) : ℤ) = gmax (n - 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with hev | ho
  · exact (P1 n hn hev).2 (n + 1) (by omega) le_rfl
  · by_cases hc : Rulers.phi (n - 1) ≤ gmax (n - 1)
    · exact P2 n hn ho hc (n + 1) (by omega) le_rfl
    · push_neg at hc
      exact (P3 n hn ho hc).2.2

end PodiumCor
