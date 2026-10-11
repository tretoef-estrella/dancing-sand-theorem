module

public import RequestProject.EvenZero.PartK

/-!
# `C50h_theorem_10_22_at_zero.md`: Part L — the singular arm

(L) the arm `U′` at `i = 0`: for every `n`, (K3) gives the approximants at the shift `2 ^ n` and
(M1′) the matrix `W_n`; (K1), (K2) and C49b `T1`, `T2` make the final matrices converge; a
subsequence of `(W_n)` converges by compactness of `Matrix (Fin ns) (Fin ns) ℤ_[2]`, and the three
conditions pass to the limit.
-/

@[expose] public section

noncomputable section

namespace EvenZero

open FormalOps FormalDance Filter Topology

/-- Proof of (L) of `C50h_theorem_10_22_at_zero.md`: entrywise congruences modulo `2 ^ (n - k)`
(for `n ≥ k`) give convergence of matrices over `ℤ_[2]`. -/
lemma tendsto_of_pow_cong {ι : Type*} [Fintype ι] (k : ℕ) (A : Matrix ι ι ℤ_[2])
    (Xn : ℕ → Matrix ι ι ℤ_[2])
    (hc : ∀ n, k ≤ n → ∀ s s', ∃ w : ℤ_[2], Xn n s s' - A s s' = 2 ^ (n - k) * w) :
    Tendsto Xn atTop (𝓝 A) := by
  rw [tendsto_pi_nhds]; intro s
  rw [tendsto_pi_nhds]; intro s'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    (eventually_atTop.2 ⟨k, fun n hn => ?_⟩)
    ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).comp
      (tendsto_sub_atTop_nat k))
  obtain ⟨w, hw⟩ := hc n hn s s'
  exact ContZero.norm_le_of_eq_pow_mul hw

/-- Proof of (L) of `C50h_theorem_10_22_at_zero.md` (the passage to the limit): if `Xn → A`,
`Vn → B` and `Vn n = W n * Xn n` with `IsUnit (W n).det` and `‖((W n - 1) s s' : ℚ_[2])‖ ≤ 1/2`,
then some `W'` satisfies the same conditions with `B = W' * A`. -/
lemma limit_of_approx {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℤ_[2])
    (Xn Vn W : ℕ → Matrix ι ι ℤ_[2]) (hX : Tendsto Xn atTop (𝓝 A))
    (hV : Tendsto Vn atTop (𝓝 B))
    (hW : ∀ n, IsUnit (W n).det ∧ (∀ s s', ‖(((W n - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
      Vn n = W n * Xn n) :
    ∃ W' : Matrix ι ι ℤ_[2], IsUnit W'.det ∧
      (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧ B = W' * A := by
  haveI : CompactSpace (Matrix ι ι ℤ_[2]) := inferInstanceAs (CompactSpace (ι → ι → ℤ_[2]))
  haveI : FirstCountableTopology (Matrix ι ι ℤ_[2]) :=
    inferInstanceAs (FirstCountableTopology (ι → ι → ℤ_[2]))
  obtain ⟨W', φ, hφ, hWφ⟩ := CompactSpace.tendsto_subseq W
  have hXφ := hX.comp hφ.tendsto_atTop
  have hVφ := hV.comp hφ.tendsto_atTop
  refine ⟨W', ?_, fun s s' => ?_, ?_⟩
  · have hdet : Tendsto (fun n => ‖(W (φ n)).det‖) atTop (𝓝 ‖W'.det‖) :=
      (continuous_norm.comp (continuous_id.matrix_det)).continuousAt.tendsto.comp hWφ
    have h1 : (fun n => ‖(W (φ n)).det‖) = fun _ => (1 : ℝ) := funext fun n =>
      PadicInt.isUnit_iff.mp (hW (φ n)).1
    rw [h1] at hdet
    exact PadicInt.isUnit_iff.mpr (tendsto_nhds_unique hdet tendsto_const_nhds)
  · rw [← PadicInt.norm_def]
    have hc : Continuous fun M : Matrix ι ι ℤ_[2] => ‖(M - 1) s s'‖ := by fun_prop
    refine le_of_tendsto' (hc.continuousAt.tendsto.comp hWφ) fun n => ?_
    have := (hW (φ n)).2.1 s s'
    rw [← PadicInt.norm_def] at this
    exact this
  · have hm : Tendsto (fun n => W (φ n) * Xn (φ n)) atTop (𝓝 (W' * A)) := hWφ.mul hXφ
    refine tendsto_nhds_unique hVφ ?_
    exact hm.congr fun n => ((hW (φ n)).2.2).symm

/-- **(L)** of `C50h_theorem_10_22_at_zero.md` (the arm `U′` at `i = 0`): let `l : ℕ`,
`V : Bf ℤ_[2]` with `(2 : ℤ_[2]) • V = FoldOdd.PsiF 0 * (FoldOdd.PsiF 0 + (2 : ℤ_[2]) • 1)`, and
`Xk Vk` with `DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF 0) Xk` and
`DanceRel (Families.ds l) 1 (fun _ _ => V) Vk`. Then there is
`W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) ℤ_[2]`
with `IsUnit W'.det`, `‖((W' - 1) s s' : ℚ_[2])‖ ≤ 1 / 2` for all `s s'`, and
`finalM Vk = W' * finalM Xk`. -/
theorem L (l : ℕ) (V : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = FoldOdd.PsiF 0 * (FoldOdd.PsiF 0 + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hXk : DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF 0) Xk)
    (hVk : DanceRel (Families.ds l) 1 (fun _ _ => V) Vk) :
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit W'.det ∧ (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
        finalM Vk = W' * finalM Xk := by
  obtain ⟨hM0, hU⟩ := M0
  choose Vn Xn Vkn hVn hXn hVkn using K3 l
  have hW := fun n => M1' l (2 ^ n) Nat.one_le_two_pow (FoldOdd.kJ 0 1) hU (FoldOdd.kJ 0) 2
    (Or.inl rfl) (Vn n) (hVn n) (Xn n) (Vkn n) (hXn n) (hVkn n)
  choose W hW using hW
  rw [← hM0] at hV hXk
  have hX : Tendsto (fun n => finalM (Xn n)) atTop (𝓝 (finalM Xk)) :=
    tendsto_of_pow_cong (Families.ds l).length _ _ fun n hn s s' =>
      ContZero.T2 (ContZero.T1 _ 1 (n - (Families.ds l).length) _ _ _ _ (hXn n) hXk
        ((K1 n).mono (by omega))) s s'
  have hVc : Tendsto (fun n => finalM (Vkn n)) atTop (𝓝 (finalM Vk)) :=
    tendsto_of_pow_cong (Families.ds l).length _ _ fun n hn s s' =>
      ContZero.T2 (ContZero.T1 _ 1 (n - (Families.ds l).length) _ _ _ _ (hVkn n) hVk
        ((K2 n (Vn n) V (hVn n) hV).mono (by omega))) s s'
  exact limit_of_approx _ _ _ _ W hX hVc hW

end EvenZero
