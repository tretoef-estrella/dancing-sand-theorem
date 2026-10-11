module

public import RequestProject.MainTheorem.Shape
public import RequestProject.FamilyGroup.All

/-!
# `C33_the_main_theorem.md`: Part G — the group of a family, in one form

Encodings (namespace `MainTheorem`):

* `XFam lam i : Type` is defined by cases on the shift `i` exactly as in (G0):
  `XFam lam 0 = SC (ds lam) × (ℤ_[2] × Π_{q : Fin (N − 1)} Q (yPool0 (ds lam) q).toNat)` and
  `XFam lam (i + 1) = SC (ds lam) × Π_{p : Fin N} Q (yPool (ds lam) (i + 1) p).toNat`, with
  `N = 2 ^ Dance.mCount (ds lam)`; the products are Lean's dependent function types, read at
  `p.val`, and `×` is the product module.  The integer exponents are turned into natural numbers by
  `Int.toNat`, harmless by (G1).
* The group of the tower is C16's `FamilyGroup.X (ds lam) 1 i`; an isomorphism is a
  `ℤ_[2]`-linear equivalence (`Nonempty (… ≃ₗ[ℤ_[2]] …)`, with an explicit `G2equiv`).
-/

@[expose] public section

namespace MainTheorem

open Families

/-! ### (G0) -/

/-- **(G0)** of `C33_the_main_theorem.md` (Part G): the group of a family in uniform form,
by cases on the shift:
* `XFam λ 0 := SC (ds λ) × (ℤ_[2] × Π_{q : Fin (N λ − 1)} Q (yPool0 (ds λ) q).toNat)`,
* `XFam λ (i + 1) := SC (ds λ) × Π_{p : Fin (N λ)} Q (yPool (ds λ) (i + 1) p).toNat`. -/
abbrev XFam (lam : ℕ) : ℕ → Type
  | 0 => FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))
  | i + 1 => FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)

/-- The additive group structure of `XFam λ i` (the product structure, by cases on `i`; part of
(G0) of `C33_the_main_theorem.md`). -/
noncomputable instance instAddCommGroupXFam (lam : ℕ) : (i : ℕ) → AddCommGroup (XFam lam i)
  | 0 => inferInstanceAs (AddCommGroup (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))))
  | i + 1 => inferInstanceAs (AddCommGroup (FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)))

/-- The `ℤ_[2]`-module structure of `XFam λ i` (the product structure, by cases on `i`; part of
(G0) of `C33_the_main_theorem.md`). -/
noncomputable instance instModuleXFam (lam : ℕ) : (i : ℕ) → Module ℤ_[2] (XFam lam i)
  | 0 => inferInstanceAs (Module ℤ_[2] (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))))
  | i + 1 => inferInstanceAs (Module ℤ_[2] (FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)))

/-- **(G0)** of `C33_the_main_theorem.md` (Part G), shift `0`, as an equation of types. -/
theorem XFam_zero (lam : ℕ) :
    XFam lam 0 = (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
      ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
        FamilyGroup.Q (FamilyGroup.yPool0 (ds lam) q).toNat))) := rfl

/-- **(G0)** of `C33_the_main_theorem.md` (Part G), shift `i + 1`, as an equation of types. -/
theorem XFam_succ (lam i : ℕ) :
    XFam lam (i + 1) = (FamilyGroup.SC (ds lam) ×
      ((p : Fin (2 ^ Dance.mCount (ds lam))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i + 1) p).toNat)) := rfl

/-! ### (G1) -/

/-- **(G1)** of `C33_the_main_theorem.md` (Part G), shifts `i ≥ 1`: for `λ ≥ 1`, `p < N λ`,
`0 ≤ yPool (ds λ) i p`.  From C16 `T1`. -/
theorem G1_pos (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) (p : ℕ)
    (hp : p < 2 ^ Dance.mCount (ds lam)) : 0 ≤ FamilyGroup.yPool (ds lam) i p := by
  obtain ⟨E, hE, -⟩ := FamilyGroup.T1 (ds lam) (S2_length lam hlam) i hi
  rw [← hE p hp]; exact Int.natCast_nonneg _

/-- **(G1)** of `C33_the_main_theorem.md` (Part G), shift `0`: for `λ ≥ 1`, `I λ ≠ ∅` and
`q < N λ − 1`, `0 ≤ yPool0 (ds λ) q`.  From C16 `T2`. -/
theorem G1_zero (lam : ℕ) (hlam : 1 ≤ lam) (hne : Windows.Ids (ds lam) ≠ ∅) (q : ℕ)
    (hq : q < 2 ^ Dance.mCount (ds lam) - 1) : 0 ≤ FamilyGroup.yPool0 (ds lam) q := by
  obtain ⟨E, hE, -⟩ := FamilyGroup.T2 (ds lam) (S2_length lam hlam) hne
  rw [← hE q hq]; exact Int.natCast_nonneg _

/-! ### (G2) -/

/-- Transport of `Q` along an equality of exponents (auxiliary for (G2) of
`C33_the_main_theorem.md`). -/
def castQ {a b : ℕ} (h : a = b) : FamilyGroup.Q a ≃ₗ[ℤ_[2]] FamilyGroup.Q b := by
  subst h; exact LinearEquiv.refl _ _

/-- The case `i ≥ 1` of (G2) of `C33_the_main_theorem.md` (auxiliary). -/
lemma G2_succ (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FamilyGroup.X (ds lam) 1 (i + 1) ≃ₗ[ℤ_[2]] XFam lam (i + 1)) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := FamilyGroup.T1 (ds lam) (S2_length lam hlam) (i + 1) (by omega)
  refine ⟨e.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
    (LinearEquiv.piCongrRight fun p => castQ ?_))⟩
  rw [← hE p p.2, Int.toNat_natCast]

/-- The case `i = 0`, `I ≠ ∅` of (G2) of `C33_the_main_theorem.md` (auxiliary). -/
lemma G2_zero_ne (lam : ℕ) (hlam : 1 ≤ lam) (hne : Windows.Ids (ds lam) ≠ ∅) :
    Nonempty (FamilyGroup.X (ds lam) 1 0 ≃ₗ[ℤ_[2]] XFam lam 0) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := FamilyGroup.T2 (ds lam) (S2_length lam hlam) hne
  refine ⟨e.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
    (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
      (LinearEquiv.piCongrRight fun q => castQ ?_)))⟩
  rw [← hE q q.2, Int.toNat_natCast]

/-- The case `i = 0`, `I = ∅` of (G2) of `C33_the_main_theorem.md` (auxiliary): `N = 1`, the
product over `Fin 0` is a singleton, and C16 `T2_empty` applies. -/
lemma G2_zero_empty (lam : ℕ) (hI : Windows.Ids (ds lam) = ∅) :
    Nonempty (FamilyGroup.X (ds lam) 1 0 ≃ₗ[ℤ_[2]] XFam lam 0) := by
  obtain ⟨e⟩ := FamilyGroup.T2_empty (ds lam) hI
  have hm : Dance.mCount (ds lam) = 0 := by rw [← S3_card, hI, Finset.card_empty]
  haveI : IsEmpty (Fin (2 ^ Dance.mCount (ds lam) - 1)) :=
    ⟨fun q => by have := q.2; simp only [hm] at this; omega⟩
  exact ⟨e.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
    (LinearEquiv.prodUnique (R := ℤ_[2])).symm)⟩

/-- **(G2)** of `C33_the_main_theorem.md` (Part G): for every `λ ≥ 1` and every shift `i`,
`FamilyGroup.X (ds λ) 1 i ≅ XFam λ i`.  From C16 `T1`, `T2`, `T2_empty` and (S2). -/
theorem G2 (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FamilyGroup.X (ds lam) 1 i ≃ₗ[ℤ_[2]] XFam lam i) := by
  rcases i with _ | i
  · by_cases hI : Windows.Ids (ds lam) = ∅
    · exact G2_zero_empty lam hI
    · exact G2_zero_ne lam hlam hI
  · exact G2_succ lam hlam i

/-- **(G2)** of `C33_the_main_theorem.md` (Part G), a chosen explicit equivalence
`FamilyGroup.X (ds λ) 1 i ≃ₗ[ℤ_[2]] XFam λ i` for `λ ≥ 1`. -/
noncomputable def G2equiv (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    FamilyGroup.X (ds lam) 1 i ≃ₗ[ℤ_[2]] XFam lam i :=
  (G2 lam hlam i).some

end MainTheorem
