module

public import RequestProject.FormalAct.Defs
public import RequestProject.FormalOps.All
public import RequestProject.Filt.PartT

/-!
# `C40c_the_action_of_a_system_and_one_move.md`: Part N — the dance lattices

`Doubling.phi` (C20) and `Filt.T` (C29) are only defined over a ring with
`[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, so Part N carries these instances.

* (N1) `N1` (this is exactly C39's `FoldHalf.E0`, restated here);
* (N2) `N2`, by strong induction on `l` with `Filt.T_zero`, `Filt.T_odd`, `Filt.T_even`,
  C40's `T0`, `V0` and (N1).
-/

@[expose] public section

noncomputable section

namespace FormalAct

open DPLattice Doubling FormalOps Filt

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- **(N1)** of `C40c_the_action_of_a_system_and_one_move.md`: if `N` satisfies (nil BN), then
`phi N` satisfies (nil (2 * BN)): `∀ s ≥ 2 * BN, (phi N).Fd s = 0`. -/
theorem N1 {N : DPLattice A} {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) :
    ∀ s ≥ 2 * BN, (phi N).Fd s = 0 :=
  FoldHalf.E0 N BN hnil

/-- **(N2)** of `C40c_the_action_of_a_system_and_one_move.md`: for every `l : ℕ`, the dance
lattice `T A l` satisfies (top l) (with `W = (l : ℤ)`) and (nil (l + 1)). -/
theorem N2 (l : ℕ) :
    (∀ i, (T A l).wt i ≤ (l : ℤ) ∧ Even ((l : ℤ) - (T A l).wt i)) ∧
      (∀ s ≥ l + 1, (T A l).Fd s = 0) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · rw [T_zero]
      refine ⟨fun i => ⟨le_refl _, by simp [one]⟩, fun s hs => ?_⟩
      show oneFd A s = 0
      simp [oneFd]; omega
    · obtain ⟨ht, hn⟩ := ih k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, T_even]
      obtain ⟨h3, h4⟩ := V0 (T0 ht) (N1 hn)
      refine ⟨fun i => ?_, fun s hs => h4 s (by omega)⟩
      push_cast
      rw [show (2 : ℤ) * k + 2 = 2 * k + 1 + 1 by ring]
      exact h3 i
  · obtain ⟨ht, hn⟩ := ih k (by omega)
    rw [T_odd]
    refine ⟨fun i => ?_, fun s hs => N1 hn s (by omega)⟩
    push_cast
    exact T0 ht i

end FormalAct
