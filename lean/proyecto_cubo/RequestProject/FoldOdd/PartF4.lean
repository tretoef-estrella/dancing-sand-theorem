module

public import RequestProject.FoldOdd.PartF

/-!
# `C49_the_fold_law_on_the_odd_families.md`: Part F — (F4), `Ψ_j` and `Σ_c` on `T(l)`
-/

@[expose] public section

noncomputable section

namespace FoldOdd

open FormalOps Doubling Finset DPLattice

/-- Auxiliary for (F4): `act` is subtractive (from C40 `act_add`). -/
lemma act_sub' {A : Type*} [CommRing A] (N : DPLattice A) (W : ℤ) (B : ℕ) (x y : Bf A) :
    act N W B (x - y) = act N W B x - act N W B y := by
  rw [eq_sub_iff_add_eq, ← act_add, sub_add_cancel]

/-- Auxiliary for (F4): on `T(l)` with `W = l`, if `p k = 4 k + 2 (e − l)` then
`flD (T l) l p = ((2 * e : ℤ) : ℤ_[2]) • 1 − 2 • H` (every weight `w` has `l − w` even, (O4)). -/
lemma flD_T (l : ℕ) (p : ℤ → ℤ_[2]) (e : ℤ) (hp : ∀ k : ℤ, p k = 4 * (k : ℤ_[2]) + 2 * (e - l)) :
    flD (Filt.T ℤ_[2] l) (l : ℤ) p =
      ((2 * e : ℤ) : ℤ_[2]) • 1 - (2 : ℤ_[2]) • H (Filt.T ℤ_[2] l) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  obtain ⟨_, k, hk⟩ := FoldCube.O4 (A := ℤ_[2]) l i
  have hdiv : ((l : ℤ) - (Filt.T ℤ_[2] l).wt i) / 2 = k := by omega
  have hw : ((Filt.T ℤ_[2] l).wt i : ℤ_[2]) = (l : ℤ_[2]) - 2 * (k : ℤ_[2]) := by
    have : (Filt.T ℤ_[2] l).wt i = (l : ℤ) - 2 * k := by omega
    rw [this]; push_cast; ring
  simp only [flD_apply, hdiv, hp, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Hop_apply, hw]
  push_cast
  ring

/-- Auxiliary for (F4): on `T(l)`, `parOp (T l) (l + j) = (−1)^j • 1` (via (O4)). -/
lemma parOp_T (l j : ℕ) :
    FoldHalf.parOp (Filt.T ℤ_[2] l) ((l : ℤ) + j) = ((-1 : ℤ_[2]) ^ j) • 1 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  obtain ⟨hle, k, hk⟩ := FoldCube.O4 (A := ℤ_[2]) l i
  rw [FoldHalf.parOp_apply]
  simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have : ((l : ℤ) + j - (Filt.T ℤ_[2] l).wt i).natAbs = 2 * k.toNat + j := by omega
  rw [this, pow_add, pow_mul]
  simp

/-- **(F4)** of `C49_the_fold_law_on_the_odd_families.md` (`Ψ_j` and `Σ_c` on `T(l)`): for
`l j c B : ℕ` with `l + 1 ≤ B`, over `ℤ_[2]`,
`act (Filt.T ℤ_[2] l) l B (PsiF j) = FoldHalf.Psi (Filt.T ℤ_[2] l) (l + j) (l + 1)` and
`act (Filt.T ℤ_[2] l) l B (SigF c) = FoldCube.SigmaOp (Filt.T ℤ_[2] l) (l + 2 * c)`. -/
theorem F4 (l j c B : ℕ) (hB : l + 1 ≤ B) :
    act (Filt.T ℤ_[2] l) (l : ℤ) B (PsiF j) =
        FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1) ∧
      act (Filt.T ℤ_[2] l) (l : ℤ) B (SigF c) =
        FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (c : ℤ)) := by
  have hnil := (FoldHalf.A3 ℤ_[2] l).2
  have hB1 : 1 ≤ B := by omega
  obtain ⟨hCh, -, hShInv⟩ := F3 (Filt.T ℤ_[2] l) (l : ℤ) (l + 1) B hnil hB hB1
  constructor
  · rw [PsiF, KF, act_add, act_mul hnil hB, act_sub', act_smul, act_one hB1, hCh, hShInv,
      act_dg hB1, FoldHalf.Psi, parOp_T,
      flD_T l _ ((l : ℤ) + j) (fun k => by push_cast; ring)]
  · rw [SigF, act_add, act_dg hB1, act_fd hnil hB, FoldCube.SigmaOp,
      flD_T l _ ((l : ℤ) + 2 * (c : ℤ)) (fun k => by push_cast; ring)]
    abel

end FoldOdd
