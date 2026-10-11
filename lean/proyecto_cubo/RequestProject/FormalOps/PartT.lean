module

public import RequestProject.FormalOps.PartB
public import RequestProject.FoldHalf.PartE

/-!
# `C40_the_formal_operators.md`: Part T — the twist map

`N : DPLattice A`, `Doubling.phi N` is C20's `Φ(N)` (basis `Fin 2 × N.ι`, the vector with `n` in
the slot `e` is C18's `bvec e n`). Since `Doubling.phi` is only defined over a ring with
`[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, so is Part T. The divided powers of `Φ(N)` are
used only through C20's `Doubling.B3`, and the vanishing `F^{(r)} = 0` for `r ≥ 2·BN` is C39's
`FoldHalf.E0`.

* (T0) `T0`;
* (T1) `T1_b0`, `T1_b1`, collected in `T1`.

Hypotheses: (top W) is used in (T0) and, through the floors of `Φ(N)`, in (T1); (nil BN) is used in
(T1). Both are needed.
-/

@[expose] public section

noncomputable section

namespace FormalOps

open DPLattice Doubling Finset

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]
  {N : DPLattice A} {W : ℤ} {BN : ℕ}

/-- **(T0)** of `C40_the_formal_operators.md`: if `N` satisfies (top W), then `Doubling.phi N`
satisfies (top (2W + 1)):
`∀ i, (phi N).wt i ≤ 2W + 1 ∧ Even (2W + 1 − (phi N).wt i)`. -/
theorem T0 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) :
    ∀ i, (phi N).wt i ≤ 2 * W + 1 ∧ Even (2 * W + 1 - (phi N).wt i) := by
  rintro ⟨e, j⟩
  obtain ⟨h1, -⟩ := htop j
  show 2 * N.wt j + wtV e ≤ 2 * W + 1 ∧ Even (2 * W + 1 - (2 * N.wt j + wtV e))
  rw [Int.even_iff]
  fin_cases e <;> simp <;> omega

lemma flD_phi_b0 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (p : ℤ → A) (n : N.ι → A) :
    flD (phi N) (2 * W + 1) p (bvec 0 n) = bvec 0 (flD N W (fun g => p (2 * g)) n) := by
  funext ⟨e, i⟩
  simp only [flD_apply, bvec_apply]
  split_ifs with he
  · subst he
    have h2 := (htop i).2
    rw [Int.even_iff] at h2
    show p ((2 * W + 1 - (2 * N.wt i + wtV 0)) / 2) * n i = _
    rw [wtV_zero]
    congr 2
    omega
  · rw [mul_zero]

lemma flD_phi_b1 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (p : ℤ → A) (n : N.ι → A) :
    flD (phi N) (2 * W + 1) p (bvec 1 n) = bvec 1 (flD N W (fun g => p (2 * g + 1)) n) := by
  funext ⟨e, i⟩
  simp only [flD_apply, bvec_apply]
  split_ifs with he
  · subst he
    have h2 := (htop i).2
    rw [Int.even_iff] at h2
    show p ((2 * W + 1 - (2 * N.wt i + wtV 1)) / 2) * n i = _
    rw [wtV_one]
    congr 2
    omega
  · rw [mul_zero]

lemma sum_range_two_mul {X : Type*} [AddCommMonoid X] (K : ℕ) (g : ℕ → X) :
    ∑ m ∈ range (2 * K), g m = ∑ q ∈ range K, (g (2 * q) + g (2 * q + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

omit [IsDomain A] [CharZero A] [OddUnits A] in
lemma smul_bvec_flD (e : Fin 2) (c : A) (p : ℤ → A) (v : N.ι → A) :
    c • bvec e (flD N W p v) = bvec e (flD N W (fun f => c * p f) v) := by
  rw [flD_const_mul, LinearMap.smul_apply, map_smul]

/-- **(T1)** of `C40_the_formal_operators.md`, first formula: under (top W) and (nil BN), for
every `x : Bf A`, `n : N.ι → A`, `B ≥ 2·BN` and `B' ≥ BN`,
`act (phi N) (2W + 1) B x (bvec 0 n) = bvec 0 (act N W B' (tw00 x) n) + bvec 1 (act N W B' (tw10 x) n)`. -/
theorem T1_b0 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (x : Bf A) (n : N.ι → A) {B B' : ℕ} (hB : 2 * BN ≤ B) (hB' : BN ≤ B') :
    act (phi N) (2 * W + 1) B x (bvec 0 n) =
      bvec 0 (act N W B' (tw00 x) n) + bvec 1 (act N W B' (tw10 x) n) := by
  rw [act_bound (FoldHalf.E0 N BN hnil) hB (le_refl (2 * BN)), act_bound hnil hB' (le_refl BN),
    act_bound hnil hB' (le_refl BN), act_apply, act_apply, act_apply, sum_range_two_mul,
    map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [(Doubling.B3 N q n).1 0, (Doubling.B3 N q n).2.1, map_smul, map_smul, flD_phi_b0 htop, flD_phi_b1 htop,
    smul_bvec_flD, smul_bvec_flD]
  rfl

/-- **(T1)** of `C40_the_formal_operators.md`, second formula: under (top W) and (nil BN), for
every `x : Bf A`, `n : N.ι → A`, `B ≥ 2·BN` and `B' ≥ BN`,
`act (phi N) (2W + 1) B x (bvec 1 n) = bvec 0 (act N W B' (tw01 x) n) + bvec 1 (act N W B' (tw11 x) n)`. -/
theorem T1_b1 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (x : Bf A) (n : N.ι → A) {B B' : ℕ} (hB : 2 * BN ≤ B) (hB' : BN ≤ B') :
    act (phi N) (2 * W + 1) B x (bvec 1 n) =
      bvec 0 (act N W B' (tw01 x) n) + bvec 1 (act N W B' (tw11 x) n) := by
  rw [act_bound (FoldHalf.E0 N BN hnil) hB (le_refl (2 * BN)),
    act_bound hnil hB' (Nat.le_succ BN) (tw01 x), act_bound hnil hB' (le_refl BN) (tw11 x),
    act_apply, act_apply, act_apply, sum_range_two_mul, Finset.sum_range_succ',
    show (tw01 x).coef 0 = 0 from funext fun f => rfl, flD_zero, LinearMap.zero_apply, add_zero,
    map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [(Doubling.B3 N q n).1 1, (Doubling.B3 N q n).2.2, map_smul, map_smul, flD_phi_b0 htop,
    flD_phi_b1 htop, smul_bvec_flD, smul_bvec_flD, add_comm]
  rfl

/-- **(T1)** of `C40_the_formal_operators.md`: under (top W) and (nil BN), for every `x : Bf A`,
`n : N.ι → A`, `B ≥ 2·BN` and `B' ≥ BN`:
`act (phi N) (2W + 1) B x (bvec 0 n) = bvec 0 (act N W B' (tw00 x) n) + bvec 1 (act N W B' (tw10 x) n)`
and
`act (phi N) (2W + 1) B x (bvec 1 n) = bvec 0 (act N W B' (tw01 x) n) + bvec 1 (act N W B' (tw11 x) n)`. -/
theorem T1 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (x : Bf A) (n : N.ι → A) {B B' : ℕ} (hB : 2 * BN ≤ B) (hB' : BN ≤ B') :
    act (phi N) (2 * W + 1) B x (bvec 0 n) =
      bvec 0 (act N W B' (tw00 x) n) + bvec 1 (act N W B' (tw10 x) n) ∧
    act (phi N) (2 * W + 1) B x (bvec 1 n) =
      bvec 0 (act N W B' (tw01 x) n) + bvec 1 (act N W B' (tw11 x) n) :=
  ⟨T1_b0 htop hnil x n hB hB', T1_b1 htop hnil x n hB hB'⟩

end FormalOps
