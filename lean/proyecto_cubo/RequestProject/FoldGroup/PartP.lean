module

public import RequestProject.FoldGroup.PartD

/-!
# `C38b_the_folded_cube_and_proposition_103.md`: Part P — Proposition 10.3

* (P1) `twoMPi` (products over any index type, in particular finite families), `twoMProd`,
  `twoMCongr`, `twoMPadic`, collected in `P1`.
* (P2) `P2` (Proposition 10.3, Theorem DW under the hypothesis `HX`).
-/

@[expose] public section

noncomputable section

namespace FoldGroup

open CubeLaplacian Fold

/-! ### (P1) -/

/-- **(P1)** of `C38b_the_folded_cube_and_proposition_103.md`, products:
`twoM (Π_j M_j) ≃+ Π_j twoM (M_j)`. Stated for every index type (more general than finite
families). -/
def twoMPi {ι : Type*} (M : ι → Type*) [∀ j, AddCommGroup (M j)] :
    twoM ((j : ι) → M j) ≃+ ((j : ι) → twoM (M j)) where
  toFun y j := ⟨y.1 j, by
    obtain ⟨x, hx⟩ := mem_twoM.1 y.2
    exact mem_twoM.2 ⟨x j, by rw [← hx]; rfl⟩⟩
  invFun w := ⟨fun j => (w j).1, mem_twoM.2
    ⟨fun j => (mem_twoM.1 (w j).2).choose,
      funext fun j => (mem_twoM.1 (w j).2).choose_spec⟩⟩
  left_inv y := rfl
  right_inv w := rfl
  map_add' y y' := rfl

/-- **(P1)** of `C38b_the_folded_cube_and_proposition_103.md`, binary products:
`twoM (M × N) ≃+ twoM M × twoM N`. -/
def twoMProd (M N : Type*) [AddCommGroup M] [AddCommGroup N] :
    twoM (M × N) ≃+ twoM M × twoM N where
  toFun y := (⟨y.1.1, by
      obtain ⟨x, hx⟩ := mem_twoM.1 y.2
      exact mem_twoM.2 ⟨x.1, by rw [← hx]; rfl⟩⟩,
    ⟨y.1.2, by
      obtain ⟨x, hx⟩ := mem_twoM.1 y.2
      exact mem_twoM.2 ⟨x.2, by rw [← hx]; rfl⟩⟩)
  invFun w := ⟨(w.1.1, w.2.1), mem_twoM.2
    ⟨((mem_twoM.1 w.1.2).choose, (mem_twoM.1 w.2.2).choose),
      Prod.ext (mem_twoM.1 w.1.2).choose_spec (mem_twoM.1 w.2.2).choose_spec⟩⟩
  left_inv y := rfl
  right_inv w := rfl
  map_add' y y' := rfl

/-- **(P1)** of `C38b_the_folded_cube_and_proposition_103.md`, functoriality: an additive
equivalence `M ≃+ N` induces `twoM M ≃+ twoM N`. -/
def twoMCongr {M N : Type*} [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) :
    twoM M ≃+ twoM N where
  toFun y := ⟨e y.1, by
    obtain ⟨x, hx⟩ := mem_twoM.1 y.2
    exact mem_twoM.2 ⟨e x, by rw [← map_nsmul, hx]⟩⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨x, hx⟩ := mem_twoM.1 y.2
    exact mem_twoM.2 ⟨e.symm x, by rw [← map_nsmul, hx]⟩⟩
  left_inv y := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_add' y y' := Subtype.ext (map_add e _ _)

/-- `ℤ_[2]` has no `2`-power torsion (auxiliary for (P1), (P2)). -/
lemma padic_torsionFree : ∀ (a : ℤ_[2]) (k : ℕ), (2 ^ k : ℕ) • a = 0 → a = 0 := by
  intro a k h
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (by exact_mod_cast (pow_ne_zero k two_ne_zero : (2 : ℕ) ^ k ≠ 0))
  · exact h

/-- **(P1)** of `C38b_the_folded_cube_and_proposition_103.md`: `twoM ℤ_[2] ≃+ ℤ_[2]` (inverse of
`x ↦ 2 • x`). -/
def twoMPadic : twoM ℤ_[2] ≃+ ℤ_[2] :=
  (AddEquiv.ofBijective (nsmulAddMonoidHom (α := ℤ_[2]) 2).rangeRestrict
    ⟨fun x y hxy => by
      have h := congrArg Subtype.val hxy
      simp only [AddMonoidHom.coe_rangeRestrict, nsmulAddMonoidHom_apply] at h
      have h2 : (2 ^ 1 : ℕ) • (x - y) = 0 := by rw [pow_one, smul_sub, h, sub_self]
      exact sub_eq_zero.1 (padic_torsionFree _ 1 h2),
     AddMonoidHom.rangeRestrict_surjective _⟩).symm

/-- **(P1)** of `C38b_the_folded_cube_and_proposition_103.md`, all four facts together (as
`Nonempty` statements; the explicit equivalences are `twoMPi`, `twoMProd`, `twoMCongr`,
`twoMPadic`). The product statement holds for every index type, finite or not. -/
theorem P1 :
    (∀ (ι : Type) (M : ι → Type) [∀ j, AddCommGroup (M j)],
      Nonempty (twoM ((j : ι) → M j) ≃+ ((j : ι) → twoM (M j)))) ∧
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N],
      Nonempty (twoM (M × N) ≃+ twoM M × twoM N)) ∧
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N], (M ≃+ N) →
      Nonempty (twoM M ≃+ twoM N)) ∧
    Nonempty (twoM ℤ_[2] ≃+ ℤ_[2]) :=
  ⟨fun _ M _ => ⟨twoMPi M⟩, fun M N _ _ => ⟨twoMProd M N⟩, fun _ _ _ _ e => ⟨twoMCongr e⟩,
    ⟨twoMPadic⟩⟩

/-! ### (P2) -/

/-- **(P2)** of `C38b_the_folded_cube_and_proposition_103.md` (Proposition 10.3): if
`XbarFam λ i ≃+ twoM (FamilyGroup.X (Families.ds λ) 1 i)` for every `λ ≥ 1` and every `i`
(hypothesis `HX`, the fold law family by family), then for every `n ≥ 1`,
`Syl2 (KBar n) ≃+ twoM (Syl2 (K n))` (Theorem DW). -/
theorem P2 (HX : ∀ lam ≥ 1, ∀ i,
      Nonempty (XbarFam lam i ≃+ twoM (FamilyGroup.X (Families.ds lam) 1 i)))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (Syl2 (KBar n) ≃+ twoM (Syl2 (K n))) := by
  obtain ⟨d2⟩ := D2 n
  obtain ⟨t2⟩ := Families.T2 n
  let h : ∀ j : Fin (FamDec.L n).length,
      XbarFam ((FamDec.L n).get j) ((n - (FamDec.L n).get j) / 2) ≃+
        twoM (FamilyGroup.X (Families.ds ((FamDec.L n).get j)) 1
          ((n - (FamDec.L n).get j) / 2)) := fun j =>
    (HX _ (FamDec.M3 n hn _ (List.get_mem _ j)).1 _).some
  let E : ℤ_[2] × Syl2 (KBar n) ≃+ ℤ_[2] × twoM (Syl2 (K n)) :=
    ((((d2.trans (AddEquiv.piCongrRight h)).trans (twoMPi _).symm).trans
      (twoMCongr t2.symm)).trans (twoMProd _ _)).trans
      (AddEquiv.prodCongr twoMPadic (AddEquiv.refl _))
  refine Mirror.cancel_torsion padic_torsionFree padic_torsionFree ?_ ?_ E
  · rintro ⟨x, k, hk⟩
    exact ⟨k, Subtype.ext hk⟩
  · rintro ⟨⟨y, k, hk⟩, hy⟩
    exact ⟨k, Subtype.ext (Subtype.ext hk)⟩

end FoldGroup
