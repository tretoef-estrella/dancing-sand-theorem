module

public import RequestProject.FoldLaw.All

/-!
# `C53_the_small_cases.md`: Part S — the case `n = 1`

* (S0) `S0`: `BaiCounts.aN 1 = 0`.
* (S1) `S1`: `Syl2 (K 1)` is trivial.
* (S2) `S2`: `Syl2 (KBar 1)` is trivial.
* (S3) `S3`: `Fold.lapBar A 1 = 0` for every commutative ring `A`.
* (DW'1) `DW'_one`: Theorem DW′ at `n = 1` (with `H = PUnit`).
* (L1-1) `L1_one`: (L1) at `n = 1`.
* (R1) `R1`: (R) at `n = 1`.

Nothing of the Setting is redefined; the only new declarations are auxiliary lemmas.
-/

@[expose] public section

noncomputable section

namespace SmallCases

open CubeLaplacian Fold FoldGroup BaiCounts

/-- An additive isomorphism between two subsingleton additive groups (auxiliary for (DW'1) of
`C53_the_small_cases.md`). -/
def addEquivOfSubsingleton (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Subsingleton M]
    [Subsingleton N] : M ≃+ N where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

/-- `ℓ_0(M) = 1` for a subsingleton group `M` (auxiliary for Part S of
`C53_the_small_cases.md`). -/
lemma l0_of_subsingleton (M : Type*) [AddCommGroup M] [Subsingleton M] : l0 M = 1 := by
  unfold l0
  haveI : Subsingleton (M ⧸ twoPow M 1) := (QuotientAddGroup.mk_surjective).subsingleton
  exact Nat.card_of_subsingleton (0 : M ⧸ twoPow M 1)

/-- `ℓ_1(M) = 1` for a subsingleton group `M` (auxiliary for Part S of
`C53_the_small_cases.md`). -/
lemma l1_of_subsingleton (M : Type*) [AddCommGroup M] [Subsingleton M] : l1 M = 1 := by
  unfold l1
  haveI : Subsingleton (twoPow M 1 ⧸ (twoPow M 2).addSubgroupOf (twoPow M 1)) :=
    (QuotientAddGroup.mk_surjective).subsingleton
  exact Nat.card_of_subsingleton 0

/-- **(S0)** of `C53_the_small_cases.md` (Part S): `BaiCounts.aN 1 = 0`
(`2^0 − 2^0 = 0` in `ℕ`). -/
theorem S0 : BaiCounts.aN 1 = 0 := by
  simp [BaiCounts.aN]

/-- **(S1)** of `C53_the_small_cases.md` (Part S):
`Subsingleton (CubeLaplacian.Syl2 (CubeLaplacian.K 1))`.  From C34 (B1) at `n = 1`
(`ℓ_0 = 1`) and the structure of finite abelian `2`-groups. -/
theorem S1 : Subsingleton (CubeLaplacian.Syl2 (CubeLaplacian.K 1)) := by
  classical
  haveI := K_finite 1
  obtain ⟨ι, hι, f, hf1, ⟨e⟩⟩ := FoldLaw.two_group_structure (Syl2 (K 1)) fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, Subtype.ext hk⟩
  have h0 := l0_congr e
  rw [B1 1 le_rfl, l0_pi, Finset.prod_congr rfl fun i _ => FoldLaw.l0_zmod (hf1 i)] at h0
  simp only [Finset.prod_const, Finset.card_univ] at h0
  have hc : Fintype.card ι = 0 := by
    have h1 : (2 : ℕ) ^ Fintype.card ι = 2 ^ 0 := by rw [← h0]; rfl
    exact Nat.pow_right_injective le_rfl h1
  haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
  exact e.toEquiv.subsingleton

/-- **(S2)** of `C53_the_small_cases.md` (Part S):
`Subsingleton (CubeLaplacian.Syl2 (Fold.KBar 1))`.  From C51 (DW) at `n = 1` and (S1). -/
theorem S2 : Subsingleton (CubeLaplacian.Syl2 (Fold.KBar 1)) := by
  haveI := S1
  obtain ⟨d⟩ := FoldLaw.DW 1 le_rfl
  exact d.toEquiv.subsingleton

/-- **(S3)** of `C53_the_small_cases.md` (Part S): `Fold.lapBar A 1 = 0` for every commutative
ring `A`.  In `Gbar 1`, `mk 1 (e 0) = mk 1 (aElt 1) = 0`, so `lapBar A 1 u x = 1·u x − u x = 0`. -/
theorem S3 (A : Type*) [CommRing A] : Fold.lapBar A 1 = 0 := by
  have hm : mk 1 (e 1 0) = 0 := by
    have he : e 1 0 = aElt 1 := by
      funext i
      rw [Subsingleton.elim i 0]
      simp [e, aElt]
    rw [he]
    exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)
  refine LinearMap.ext fun u => funext fun x => ?_
  rw [lapBar_apply, Fin.sum_univ_one, hm, add_zero]
  simp

/-- **(DW'1)** of `C53_the_small_cases.md` (Part S): Theorem DW′ at `n = 1`, in exactly the form
of `FoldLaw.DW'` (with `H = PUnit`). -/
theorem DW'_one :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 1) ≃+
        (Fin (BaiCounts.aN 1) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar 1) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H := by
  haveI := S1
  haveI := S2
  haveI : Subsingleton (Fin (BaiCounts.aN 1) → ZMod 2) := by rw [S0]; infer_instance
  refine ⟨PUnit, inferInstance, inferInstance, ⟨addEquivOfSubsingleton _ _⟩,
    ⟨addEquivOfSubsingleton _ _⟩, ?_⟩
  rw [l0_of_subsingleton, l1_of_subsingleton]

/-- **(L1-1)** of `C53_the_small_cases.md` (Part S): (L1) at `n = 1`,
`BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar 1)) = 2 ^ (2 ^ (1 - 1) - 1 - BaiCounts.aN 1)`
(both sides are `1`). -/
theorem L1_one :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar 1)) = 2 ^ (2 ^ (1 - 1) - 1 - BaiCounts.aN 1) := by
  haveI := S2
  rw [l0_of_subsingleton, S0]
  rfl

/-- **(R1)** of `C53_the_small_cases.md` (Part S): (R) at `n = 1`,
`Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) 1)) = BaiCounts.aN 1`
(both sides are `0`). -/
theorem R1 :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) 1)) = BaiCounts.aN 1 := by
  rw [S3, LinearMap.range_zero, finrank_bot, S0]

end SmallCases
