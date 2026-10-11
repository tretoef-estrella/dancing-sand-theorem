module

public import RequestProject.FoldLaw.PartH

/-!
# `C51_theorem_DW.md`: Part L — the layers of the folded cube

* (L0) `L0`: `ℓ_0(2M) = ℓ_1(M)` for every abelian group `M`.
* (L1) `L1`: `ℓ_0(Syl2 (KBar n)) = 2 ^ (2 ^ (n − 1) − 1 − aN n)` for `n ≥ 2`
  ((DW), (L0), C34 `BaiCounts.B2`).
-/

@[expose] public section

noncomputable section

namespace FoldLaw

open CubeLaplacian Fold FoldGroup BaiCounts

/-- `aN n ≤ 2 ^ (n − 1) − 1` (auxiliary for (DW′) and (R) of `C51_theorem_DW.md`). -/
lemma aN_le (n : ℕ) (hn : 2 ≤ n) : aN n ≤ 2 ^ (n - 1) - 1 := by
  unfold aN
  have h1 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : 1 ≤ 2 ^ ((n - 2) / 2) := Nat.one_le_two_pow
  omega

/-- **(L0)** of `C51_theorem_DW.md` (Part L): for every abelian group `M`,
`BaiCounts.l0 (FoldGroup.twoM M) = BaiCounts.l1 M`. -/
theorem L0 (M : Type*) [AddCommGroup M] :
    BaiCounts.l0 (FoldGroup.twoM M) = BaiCounts.l1 M := by
  let f : FoldGroup.twoM M →+ BaiCounts.twoPow M 1 :=
    { toFun := fun y => ⟨y.1, by
        obtain ⟨x, hx⟩ := FoldGroup.mem_twoM.1 y.2
        exact ⟨x, by rw [pow_one]; exact hx⟩⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let g := (QuotientAddGroup.mk' ((twoPow M 2).addSubgroupOf (twoPow M 1))).comp f
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨⟨w, ⟨y, hy⟩⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    exact ⟨⟨w, FoldGroup.mem_twoM.2 ⟨y, by rw [← hy, pow_one]⟩⟩, rfl⟩
  unfold BaiCounts.l0 BaiCounts.l1
  refine card_quot_of_surj g hg _ fun x => ?_
  simp only [g, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, mem_twoPow]
  change (∃ y : FoldGroup.twoM M, 2 ^ 1 • y = x) ↔ ∃ y : M, 2 ^ 2 • y = (x : M)
  constructor
  · rintro ⟨⟨y, hy⟩, hyx⟩
    obtain ⟨z, rfl⟩ := FoldGroup.mem_twoM.1 hy
    refine ⟨z, ?_⟩
    rw [← hyx, AddSubgroup.coe_nsmul, smul_smul]; norm_num
  · rintro ⟨z, hz⟩
    refine ⟨⟨2 • z, FoldGroup.mem_twoM.2 ⟨z, rfl⟩⟩, Subtype.ext ?_⟩
    rw [AddSubgroup.coe_nsmul, ← hz, smul_smul]; norm_num

/-- **(L1)** of `C51_theorem_DW.md` (Part L): for every `n ≥ 2`,
`BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) = 2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n)`. -/
theorem L1 (n : ℕ) (hn : 2 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) =
      2 ^ (2 ^ (n - 1) - 1 - BaiCounts.aN n) := by
  obtain ⟨e⟩ := DW n (by omega)
  rw [l0_congr e, L0, B2 n hn]

end FoldLaw
