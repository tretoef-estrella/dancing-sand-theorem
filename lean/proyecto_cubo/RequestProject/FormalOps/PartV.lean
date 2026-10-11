module

public import RequestProject.FormalOps.PartB
public import RequestProject.DPLattice.Tensor

/-!
# `C40_the_formal_operators.md`: Part V — the `V`-split

`M : DPLattice A` over any commutative ring `A`; `tensorV M` is C18's `V ⊗ M` (basis
`Fin 2 × M.ι`), and `bvec e y` is the vector `b_e ⊗ y` (C18). The divided powers of `V ⊗ M` are
used only through C18's coproduct formulas `tensorV_Fd_b0`, `tensorV_Fd_b0_zero`,
`tensorV_Fd_b1`.

* (V0) `V0` (`V0_top`, `V0_nil`);
* (V1) `V1_b0`, `V1_b1`, collected in `V1`.

Hypotheses. (V0) uses (top W) for the first half and (nil BN) for the second half. In (V1) the
floors `(W + 1 − (1 + w)) / 2 = (W − w) / 2` and `(W + 1 − (−1 + w)) / 2 = (W − w) / 2 + 1` hold
for every integer `w`, so (top W) is not needed: (V1) is stated with (nil BN) only (more general).
-/

@[expose] public section

noncomputable section

namespace FormalOps

open DPLattice Finset

variable {A : Type*} [CommRing A] {M : DPLattice A} {W : ℤ} {BN : ℕ}

/-- **(V0)** of `C40_the_formal_operators.md`, first half: if `M` satisfies (top W), then
`tensorV M` satisfies (top (W + 1)). -/
theorem V0_top (htop : ∀ i, M.wt i ≤ W ∧ Even (W - M.wt i)) :
    ∀ i, (tensorV M).wt i ≤ W + 1 ∧ Even (W + 1 - (tensorV M).wt i) := by
  rintro ⟨e, j⟩
  obtain ⟨h1, h2⟩ := htop j
  rw [Int.even_iff] at h2 ⊢
  rw [tensorV_wt]
  fin_cases e <;> simp <;> omega

/-- **(V0)** of `C40_the_formal_operators.md`, second half: if `M` satisfies (nil BN), then
`tensorV M` satisfies (nil (BN + 1)). -/
theorem V0_nil (hnil : ∀ s ≥ BN, M.Fd s = 0) : ∀ s ≥ BN + 1, (tensorV M).Fd s = 0 := by
  intro s hs
  refine ext_bvec (fun m => ?_) (fun m => ?_)
  · refine (tensorV_Fd_b0 M s (by omega) m).trans ?_
    rw [hnil s (by omega), hnil (s - 1) (by omega)]
    simp
  · refine (tensorV_Fd_b1 M s m).trans ?_
    rw [hnil s (by omega)]
    simp

/-- **(V0)** of `C40_the_formal_operators.md`: `tensorV M` satisfies (top (W + 1)) and
(nil (BN + 1)). -/
theorem V0 (htop : ∀ i, M.wt i ≤ W ∧ Even (W - M.wt i)) (hnil : ∀ s ≥ BN, M.Fd s = 0) :
    (∀ i, (tensorV M).wt i ≤ W + 1 ∧ Even (W + 1 - (tensorV M).wt i)) ∧
    (∀ s ≥ BN + 1, (tensorV M).Fd s = 0) :=
  ⟨V0_top htop, V0_nil hnil⟩

variable (M W)

lemma flD_tensor_b0 (p : ℤ → A) (y : M.ι → A) :
    flD (tensorV M) (W + 1) p (bvec 0 y) = bvec 0 (flD M W p y) := by
  funext ⟨e, i⟩
  simp only [flD_apply, bvec_apply]
  split_ifs with he
  · subst he
    rw [tensorV_wt, wtV_zero, show W + 1 - (1 + M.wt i) = W - M.wt i by ring]
  · rw [mul_zero]

lemma flD_tensor_b1 (p : ℤ → A) (y : M.ι → A) :
    flD (tensorV M) (W + 1) p (bvec 1 y) = bvec 1 (flD M W (fun g => p (g + 1)) y) := by
  funext ⟨e, i⟩
  simp only [flD_apply, bvec_apply]
  split_ifs with he
  · subst he
    rw [tensorV_wt, wtV_one]
    congr 2
    omega
  · rw [mul_zero]

variable {M W}

/-- **(V1)** of `C40_the_formal_operators.md`, first formula: under (nil BN), for every
`x : Bf A`, `y : M.ι → A`, `B ≥ BN + 1` and `B' ≥ BN`,
`act (tensorV M) (W + 1) B x (bvec 0 y) = bvec 0 (act M W B' x y) + bvec 1 (act M W B' (vprime x) y)`.
(Without (top W): more general.) -/
theorem V1_b0 (hnil : ∀ s ≥ BN, M.Fd s = 0) (x : Bf A) (y : M.ι → A) {B B' : ℕ}
    (hB : BN + 1 ≤ B) (hB' : BN ≤ B') :
    act (tensorV M) (W + 1) B x (bvec 0 y) =
      bvec 0 (act M W B' x y) + bvec 1 (act M W B' (vprime x) y) := by
  rw [act_bound (V0_nil hnil) hB (le_refl (BN + 1)), act_bound hnil hB' (Nat.le_succ BN) x,
    act_bound hnil hB' (le_refl BN) (vprime x), act_apply, act_apply, act_apply,
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hk : ∀ k : ℕ, flD (tensorV M) (W + 1) (x.coef (k + 1)) ((tensorV M).Fd (k + 1) (bvec 0 y)) =
      bvec 0 (flD M W (x.coef (k + 1)) (M.Fd (k + 1) y)) +
        bvec 1 (flD M W ((vprime x).coef k) (M.Fd k y)) := by
    intro k
    rw [tensorV_Fd_b0 M (k + 1) (by omega), Nat.add_sub_cancel, map_add, flD_tensor_b0,
      flD_tensor_b1]
    rfl
  simp only [hk, Finset.sum_add_distrib, map_add, map_sum, tensorV_Fd_b0_zero, flD_tensor_b0,
    M.isDP.P0_F, Module.End.one_apply]
  abel

/-- **(V1)** of `C40_the_formal_operators.md`, second formula: under (nil BN), for every
`x : Bf A`, `y : M.ι → A`, `B ≥ BN + 1` and `B' ≥ BN`,
`act (tensorV M) (W + 1) B x (bvec 1 y) = bvec 1 (act M W B' (vplus x) y)`.
(Without (top W): more general.) -/
theorem V1_b1 (hnil : ∀ s ≥ BN, M.Fd s = 0) (x : Bf A) (y : M.ι → A) {B B' : ℕ}
    (hB : BN + 1 ≤ B) (hB' : BN ≤ B') :
    act (tensorV M) (W + 1) B x (bvec 1 y) = bvec 1 (act M W B' (vplus x) y) := by
  rw [act_bound (V0_nil hnil) hB (le_refl (BN + 1)), act_bound hnil hB' (Nat.le_succ BN),
    act_apply, act_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [tensorV_Fd_b1, flD_tensor_b1]
  rfl

/-- **(V1)** of `C40_the_formal_operators.md`: under (nil BN) (and, in the file, (top W), which
is not needed), for every `x : Bf A`, `y : M.ι → A`, `B ≥ BN + 1`, `B' ≥ BN`:
`act (tensorV M) (W + 1) B x (bvec 0 y) = bvec 0 (act M W B' x y) + bvec 1 (act M W B' (vprime x) y)`
and `act (tensorV M) (W + 1) B x (bvec 1 y) = bvec 1 (act M W B' (vplus x) y)`. -/
theorem V1 (hnil : ∀ s ≥ BN, M.Fd s = 0) (x : Bf A) (y : M.ι → A) {B B' : ℕ}
    (hB : BN + 1 ≤ B) (hB' : BN ≤ B') :
    act (tensorV M) (W + 1) B x (bvec 0 y) =
      bvec 0 (act M W B' x y) + bvec 1 (act M W B' (vprime x) y) ∧
    act (tensorV M) (W + 1) B x (bvec 1 y) = bvec 1 (act M W B' (vplus x) y) :=
  ⟨V1_b0 hnil x y hB hB', V1_b1 hnil x y hB hB'⟩

end FormalOps
