module

public import RequestProject.FormalProp.Aux

/-!
# `C40d_proposition_10_7.md`: (Q0) — the dimension of `T(l)`

`(T A l).ι` has `2 ^ ((ds l).length + mCount (ds l))` elements. Proof (second route of the file's
sketch): `|(T A l).ι| = |Dance.Idx (ds l)|` by strong induction on `l` with `T_zero`, `T_odd`,
`T_even`, `ds_zero`, `ds_odd`, `ds_even` (`phi` doubles, `tensorV ∘ phi` multiplies by `4`), then
C34's `BaiCounts.S1`.
-/

@[expose] public section

noncomputable section

namespace FormalProp

open DPLattice Doubling Filt

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- (Q0) of `C40d_proposition_10_7.md`, auxiliary: `|(T A l).ι| = |Dance.Idx (ds l)|`. -/
lemma card_T_eq_card_Idx (l : ℕ) :
    Fintype.card (T A l).ι = Fintype.card (Dance.Idx (Families.ds l)) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · rw [T_zero, Families.ds_zero]; rfl
    · have hk := ih k (by omega)
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, T_even, Families.ds_even,
        Fintype.card_congr (α := (tensorV (phi (T A k))).ι) (β := Fin 2 × Fin 2 × (T A k).ι)
          (Equiv.refl _),
        Fintype.card_congr (α := Dance.Idx (true :: Families.ds k))
          (β := Dance.Idx (Families.ds k) × Fin 4) (Equiv.refl _)]
      simp only [Fintype.card_prod, Fintype.card_fin, hk]
      ring
  · have hk := ih k (by omega)
    rw [T_odd, Families.ds_odd,
      Fintype.card_congr (α := (phi (T A k)).ι) (β := Fin 2 × (T A k).ι) (Equiv.refl _),
      Fintype.card_congr (α := Dance.Idx (false :: Families.ds k))
        (β := Dance.Idx (Families.ds k) × Fin 2) (Equiv.refl _)]
    simp only [Fintype.card_prod, Fintype.card_fin, hk]
    ring

/-- **(Q0)** of `C40d_proposition_10_7.md`: for every `l`,
`Fintype.card (T A l).ι = 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l))`. -/
theorem Q0 (l : ℕ) :
    Fintype.card (T A l).ι = 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l)) := by
  rw [card_T_eq_card_Idx, BaiCounts.S1]

end FormalProp
