module

public import RequestProject.FormalProp.PartQ0

/-!
# `C40d_proposition_10_7.md`: (Q1) — Proposition 10.7, scaled

Induction along `ds = Families.ds l` (`Q1_aux`, by induction on the list `ds`, for all `l` with
`ds l = ds`, all `r`, `G`, `Gk`, `B ≥ l + 1` and `h` at once):

* `[]`: `l = 0`, `T A 0 = one A` has (top 0), so C40c (A1) turns `G` into `Gk`, and C40c (A4)
  with `c = 2^h` concludes; the product over `Fin 0` is trivial.
* `false :: rest`: `l = 2l' + 1`, `T A l = phi (T A l')`; C40c (S1) (`S1equivQ`, with `N = T A l'`,
  `W = l'`, `BN = B' = l' + 1`, by C40c (N2)) and the induction hypothesis at `h + 1`.
* `true :: rest`: `l = 2l' + 2`, `T A l = tensorV (phi (T A l'))`; C40c (S2) (`S2equivQ`), the
  relabelling C40c (A3) (`A3equiv`, along `j ↦ ofLex ((splitIso r).symm j)`), and the induction
  hypothesis at `h + 1` with `r * 2` slots.
* The new clock is counted by (Q0) and flattened as in C13 `Dance.D2_clocks`
  (`Fin.consLinearEquiv`, `Dance.pqCast`).

The bound: the induction is run for every `B ≥ l + 1` directly (the hypotheses `2 * BN ≤ B`,
`2 * BN + 1 ≤ B` of (S1), (S2) are exactly `l + 1 ≤ B`), the next level being taken with
`B' = l' + 1`.
-/

@[expose] public section

noncomputable section

namespace FormalProp

open DPLattice Doubling Filt FormalOps FormalDance FormalAct Pointwise

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- (Q1) of `C40d_proposition_10_7.md`, auxiliary: shape of `l` when `ds l = []`. -/
lemma eq_zero_of_ds_nil {l : ℕ} (hl : Families.ds l = []) : l = 0 := by
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · rfl
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, Families.ds_even] at hl; cases hl
  · rw [Families.ds_odd] at hl; cases hl

/-- (Q1) of `C40d_proposition_10_7.md`, auxiliary: shape of `l` when `ds l = false :: rest`. -/
lemma exists_of_ds_false {l : ℕ} {rest : List Bool} (hl : Families.ds l = false :: rest) :
    ∃ l', l = 2 * l' + 1 ∧ Families.ds l' = rest := by
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · rw [Nat.mul_zero, Families.ds_zero] at hl; cases hl
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, Families.ds_even] at hl; cases hl
  · rw [Families.ds_odd] at hl
    exact ⟨k, rfl, (List.cons.inj hl).2⟩

/-- (Q1) of `C40d_proposition_10_7.md`, auxiliary: shape of `l` when `ds l = true :: rest`. -/
lemma exists_of_ds_true {l : ℕ} {rest : List Bool} (hl : Families.ds l = true :: rest) :
    ∃ l', l = 2 * l' + 2 ∧ Families.ds l' = rest := by
  rcases Nat.even_or_odd' l with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · rw [Nat.mul_zero, Families.ds_zero] at hl; cases hl
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, Families.ds_even] at hl
      exact ⟨k, rfl, (List.cons.inj hl).2⟩
  · rw [Families.ds_odd] at hl; cases hl

/-- (Q1) of `C40d_proposition_10_7.md`, auxiliary: the relabelling
`Fin (r * 2) ≃ Fin r × Fin 2`, `j ↦ ofLex ((Dance.splitIso r).symm j)` of the split clause. -/
def splitEquiv (r : ℕ) : Fin (r * 2) ≃ Fin r × Fin 2 :=
  (Dance.splitIso r).symm.toEquiv.trans ofLex

/-- (Q1) of `C40d_proposition_10_7.md`, the induction along `ds` (scaled form, with the clocks
written with C13's `Dance.PQ a e = (Fin a → A) ⧸ 2^e·⊤`). -/
theorem Q1_aux (ds : List Bool) : ∀ (l : ℕ), Families.ds l = ds →
    ∀ (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
      (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A)),
      DanceRel ds r G Gk → ∀ (B : ℕ), l + 1 ≤ B → ∀ h : ℕ,
      Nonempty (((Fin r → (T A l).ι → A) ⧸
          LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B G)) ≃ₗ[A]
        (((a : Fin ds.length) →
            Dance.PQ A (r * 2 ^ (ds.length + Dance.mCount ds - 1 - a)) (h + a)) ×
          ((Fin (Dance.slots ds r) → A) ⧸
            LinearMap.range ((2 : A) ^ (h + ds.length) • Matrix.mulVecLin (finalM Gk))))) := by
  induction ds with
  | nil =>
    intro l hl r G Gk hG B hB h
    obtain rfl := eq_zero_of_ds_nil hl
    rw [T_zero, Nat.cast_zero]
    have htop : ∀ i, (one A).wt i ≤ (0 : ℤ) ∧ Even ((0 : ℤ) - (one A).wt i) :=
      fun _ => ⟨le_refl _, by simp [one]⟩
    have hGk : sysAct (one A) 0 B G = sysAct (one A) 0 B (n := Fin r) Gk := A1 htop hG B
    rw [hGk]
    haveI : IsEmpty (Fin ([] : List Bool).length) := inferInstanceAs (IsEmpty (Fin 0))
    exact ⟨(A4equiv (by omega) (n := Fin r) Gk ((2 : A) ^ h)).trans
      (LinearEquiv.uniqueProd (M₂ := (a : Fin ([] : List Bool).length) →
        Dance.PQ A (r * 2 ^ (([] : List Bool).length + Dance.mCount [] - 1 - a)) (h + a))).symm⟩
  | cons d rest ih =>
    intro l hl r G Gk hG B hB h
    cases d with
    | false =>
      obtain ⟨l', rfl, hl'⟩ := exists_of_ds_false hl
      obtain ⟨G', ⟨Q, hPQ, hQP, hS⟩, hG'⟩ := hG
      obtain ⟨htop, hnil⟩ := N2 (A := A) l'
      obtain ⟨e2⟩ := ih l' hl' r G' Gk hG' (l' + 1) le_rfl (h + 1)
      rw [T_odd, show ((2 * l' + 1 : ℕ) : ℤ) = 2 * (l' : ℤ) + 1 by push_cast; ring]
      have e1 := S1equivQ htop hnil (B := B) (B' := l' + 1) (le_refl _) (by omega) hPQ hQP
        (by omega) hS h
      let M : Fin (rest.length + 1) → Type _ := fun a =>
        Dance.PQ A (r * 2 ^ (rest.length + 1 + Dance.mCount rest - 1 - a)) (h + a)
      have hcard : Fintype.card (Fin r × (T A l').ι) =
          r * 2 ^ (rest.length + 1 + Dance.mCount rest - 1 - ((0 : Fin (rest.length + 1)) : ℕ)) := by
        rw [Fintype.card_prod, Fintype.card_fin, Q0, hl', Fin.val_zero]
        congr 2; omega
      let e0 : ((Fin r → (T A l').ι → A) ⧸
          (2 : A) ^ h • (⊤ : Submodule A (Fin r → (T A l').ι → A))) ≃ₗ[A] M 0 :=
        (sysQuotPQ hcard _).trans (Dance.pqCast rfl (by simp))
      let e1' : ((a : Fin rest.length) →
          Dance.PQ A (r * 2 ^ (rest.length + Dance.mCount rest - 1 - a)) (h + 1 + a)) ≃ₗ[A]
          ((a : Fin rest.length) → M a.succ) :=
        LinearEquiv.piCongrRight fun a => Dance.pqCast
          (by simp only [Fin.val_succ]; congr 2; omega) (by simp only [Fin.val_succ]; omega)
      let e3 : ((Fin (Dance.slots rest r) → A) ⧸ LinearMap.range
            ((2 : A) ^ (h + 1 + rest.length) • Matrix.mulVecLin (finalM Gk))) ≃ₗ[A]
          ((Fin (Dance.slots rest r) → A) ⧸ LinearMap.range
            ((2 : A) ^ (h + (rest.length + 1)) • Matrix.mulVecLin (finalM Gk))) :=
        Submodule.quotEquivOfEq _ _ (by rw [show h + 1 + rest.length = h + (rest.length + 1) by
          omega])
      exact ⟨e1.trans ((LinearEquiv.prodCongr e0 (e2.trans (LinearEquiv.prodCongr e1' e3))).trans
        ((LinearEquiv.prodAssoc A _ _ _).symm.trans
          (LinearEquiv.prodCongr (Fin.consLinearEquiv A M) (LinearEquiv.refl A _))))⟩
    | true =>
      obtain ⟨l', rfl, hl'⟩ := exists_of_ds_true hl
      obtain ⟨G'', ⟨Q, hPQ, hQP, hS⟩, hG''⟩ := hG
      obtain ⟨htop, hnil⟩ := N2 (A := A) l'
      obtain ⟨e2⟩ := ih l' hl' (r * 2) _ Gk hG'' (l' + 1) le_rfl (h + 1)
      rw [T_even, show ((2 * l' + 2 : ℕ) : ℤ) = 2 * (l' : ℤ) + 2 by push_cast; ring]
      have e1 := S2equivQ htop hnil (B := B) (B' := l' + 1) (by omega) (le_refl _) (by omega)
        hPQ hQP hS h
      have eR := (A3equiv (N := T A l') (W := (l' : ℤ)) (l' + 1) (splitEquiv r) G''
        ((2 : A) ^ (h + 1))).symm
      let M : Fin (rest.length + 1) → Type _ := fun a =>
        Dance.PQ A (r * 2 ^ (rest.length + 1 + (Dance.mCount rest + 1) - 1 - a)) (h + a)
      have hcard : Fintype.card ((Fin r × Fin 2) × (T A l').ι) =
          r * 2 ^ (rest.length + 1 + (Dance.mCount rest + 1) - 1 -
            ((0 : Fin (rest.length + 1)) : ℕ)) := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Q0, hl',
          Fin.val_zero, mul_assoc, ← pow_succ']
        congr 2; omega
      let e0 : ((Fin r × Fin 2 → (T A l').ι → A) ⧸
          (2 : A) ^ h • (⊤ : Submodule A (Fin r × Fin 2 → (T A l').ι → A))) ≃ₗ[A] M 0 :=
        (sysQuotPQ hcard _).trans (Dance.pqCast rfl (by simp))
      let e1' : ((a : Fin rest.length) →
          Dance.PQ A (r * 2 * 2 ^ (rest.length + Dance.mCount rest - 1 - a)) (h + 1 + a)) ≃ₗ[A]
          ((a : Fin rest.length) → M a.succ) :=
        LinearEquiv.piCongrRight fun a => Dance.pqCast
          (by
            simp only [Fin.val_succ]
            rw [mul_assoc, ← pow_succ']
            congr 2
            have := a.isLt
            omega)
          (by simp only [Fin.val_succ]; omega)
      let e3 : ((Fin (Dance.slots rest (r * 2)) → A) ⧸ LinearMap.range
            ((2 : A) ^ (h + 1 + rest.length) • Matrix.mulVecLin (finalM Gk))) ≃ₗ[A]
          ((Fin (Dance.slots rest (r * 2)) → A) ⧸ LinearMap.range
            ((2 : A) ^ (h + (rest.length + 1)) • Matrix.mulVecLin (finalM Gk))) :=
        Submodule.quotEquivOfEq _ _ (by rw [show h + 1 + rest.length = h + (rest.length + 1) by
          omega])
      exact ⟨e1.trans ((LinearEquiv.prodCongr e0
        (eR.trans (e2.trans (LinearEquiv.prodCongr e1' e3)))).trans
        ((LinearEquiv.prodAssoc A _ _ _).symm.trans
          (LinearEquiv.prodCongr (Fin.consLinearEquiv A M) (LinearEquiv.refl A _))))⟩

end FormalProp
