module

public import RequestProject.Cleanliness.PartW

/-!
# `C48_cleanliness_one_move.md`: Part V — the V-split

Namespace `Cleanliness`. (V0)–(V3) and (L1) of the file. The equality of (V1) is an equality of
formal operators (entries of matrices over `Bf ℤ_[2]`), not only agreement.
-/

@[expose] public section

noncomputable section

namespace Cleanliness

open RingK FormalOps FormalDance Doubling Finset

/-- **(V0)** of `C48_cleanliness_one_move.md`: `splitDn P h hP` (an equivalence
`Dn P × Fin 2 ≃ Dn (insert h P)` by construction) sends `(D, 0)` to `D` and `(D, 1)` to
`insert h D`; its inverse sends `D` to `(D.erase h, if h ∈ D then 1 else 0)`. -/
theorem V0 (P : Finset ℕ) (h : ℕ) (hP : h ∉ P) :
    (∀ D : Dn P, splitDn P h hP (D, 0) = ⟨D.1, D.2.trans (subset_insert h P)⟩) ∧
    (∀ D : Dn P, splitDn P h hP (D, 1) = ⟨insert h D.1, insert_subset_insert h D.2⟩) ∧
    (∀ D : Dn (insert h P), ((splitDn P h hP).symm D).1.1 = D.1.erase h ∧
      ((splitDn P h hP).symm D).2 = if h ∈ D.1 then 1 else 0) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Helper for (V1) of `C48_cleanliness_one_move.md`: `splitDn P h hP (D, 0) = D`. -/
lemma splitDn_zero (P : Finset ℕ) (h : ℕ) (hP : h ∉ P) (D : Dn P) :
    splitDn P h hP (D, 0) = ⟨D.1, D.2.trans (subset_insert h P)⟩ := rfl

/-- Helper for (V1) of `C48_cleanliness_one_move.md`: `splitDn P h hP (D, 1) = insert h D`. -/
lemma splitDn_one (P : Finset ℕ) (h : ℕ) (hP : h ∉ P) (D : Dn P) :
    splitDn P h hP (D, 1) = ⟨insert h D.1, insert_subset_insert h D.2⟩ := rfl

/-- Helper for (V1) of `C48_cleanliness_one_move.md`: `oS (insert h D) = oS D + 2^h` for
`h ∉ D` ((T0)). -/
lemma oS_insert {D : Finset ℕ} {h : ℕ} (hD : h ∉ D) :
    ((oS (insert h D) : ℕ) : ℤ_[2]) = (oS D : ℤ_[2]) + 2 ^ h := by
  rw [oS, sum_insert hD, ← oS]; push_cast; ring

/-- **(V1)** of `C48_cleanliness_one_move.md` (the split system is covariant at the same level):
if `h ∉ P`, then for all `q q' : Dn P × Fin 2`,
`vsplit (covSys P h c Γ) q q' =
covSys (insert h P) h c (vsplitG h Γ) (splitDn P h hP q) (splitDn P h hP q')`. -/
theorem V1 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hP : h ∉ P) (q q' : Dn P × Fin 2) :
    vsplit (covSys P h c Γ) q q' =
      covSys (insert h P) h c (vsplitG h Γ) (splitDn P h hP q) (splitDn P h hP q') := by
  obtain ⟨D, g⟩ := q
  obtain ⟨D', g'⟩ := q'
  have hD : h ∉ D.1 := fun hh => hP (D.2 hh)
  have hD' : h ∉ D'.1 := fun hh => hP (D'.2 hh)
  have hDD : h ∉ D.1 \ D'.1 := fun hh => hD (mem_sdiff.1 hh).1
  obtain rfl | rfl : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  · obtain rfl | rfl : g' = 0 ∨ g' = 1 := by fin_cases g' <;> simp
    · rw [show vsplit (covSys P h c Γ) (D, 0) (D', 0) = covSys P h c Γ D D' by simp [vsplit],
        splitDn_zero, splitDn_zero]
      ext m f
      simp only [covSys_coef, vsplitG, if_neg hDD]
    · rw [show vsplit (covSys P h c Γ) (D, 0) (D', 1) = 0 by simp [vsplit],
        splitDn_zero, splitDn_one]
      ext m f
      simp [covSys_coef, insert_subset_iff, hD]
  · obtain rfl | rfl : g' = 0 ∨ g' = 1 := by fin_cases g' <;> simp
    · rw [show vsplit (covSys P h c Γ) (D, 1) (D', 0) = vprime (covSys P h c Γ D D') by
        simp [vsplit], splitDn_one, splitDn_zero]
      ext m f
      simp only [coef_vprime, covSys_coef, subset_insert_iff_of_notMem hD',
        insert_sdiff_of_notMem _ hD', vsplitG, mem_insert_self, if_true, erase_insert hDD,
        oS_insert hD]
      split_ifs
      · congr 1; push_cast; ring
      · rfl
    · rw [show vsplit (covSys P h c Γ) (D, 1) (D', 1) = vplus (covSys P h c Γ D D') by
        simp [vsplit], splitDn_one, splitDn_one]
      ext m f
      simp only [coef_vplus, covSys_coef, insert_subset_insert_iff hD', insert_sdiff_insert,
        sdiff_insert_of_notMem hD, vsplitG, if_neg hDD, oS_insert hD]
      split_ifs
      · congr 1; push_cast; ring
      · rfl

/-- **(V2)** of `C48_cleanliness_one_move.md`: if `Good Γ` then `Good (vsplitG h Γ)`, for every
`h`; and `vsplitG h Γ {h} 0 = Γ ∅ 1`. -/
theorem V2 (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    (Good Γ → Good (vsplitG h Γ)) ∧ vsplitG h Γ {h} 0 = Γ ∅ 1 := by
  refine ⟨fun ⟨hK, hA, hB⟩ => ⟨fun Δ m => ?_, fun y => ?_, fun y => ?_⟩, ?_⟩
  · by_cases hh : h ∈ Δ
    · have : vsplitG h Γ Δ m = Γ (Δ.erase h) (m + 1) := by funext y; simp [vsplitG, hh]
      rw [this]; exact hK _ _
    · have : vsplitG h Γ Δ m = Γ Δ m := by funext y; simp [vsplitG, hh]
      rw [this]; exact hK _ _
  · simpa [vsplitG] using hA y
  · simpa [vsplitG] using hB y
  · funext y; simp [vsplitG]

/-- **(L1)** of `C48_cleanliness_one_move.md` (reindexing): for `Fintype`s with `DecidableEq`, an
equivalence `e : n ≃ n'` and `G G' : Matrix n' n' (Bf A)` over any commutative ring `A`,
`CleanStep G G' → CleanStep (fun j j' => G (e j) (e j')) (fun j j' => G' (e j) (e j'))`. -/
theorem L1 {A : Type*} [CommRing A] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G G' : Matrix n' n' (Bf A)) :
    CleanStep G G' → CleanStep (fun j j' => G (e j) (e j')) (fun j j' => G' (e j) (e j')) := by
  rintro ⟨Q, h1, h2, h3⟩
  refine ⟨Q.submatrix e e, ?_, ?_, ?_⟩
  · change MAgree ((twP G).submatrix e e * Q.submatrix e e) 1
    rw [Matrix.submatrix_mul_equiv, ← Matrix.submatrix_one_equiv e]
    exact fun s s' => h1 (e s) (e s')
  · change MAgree (Q.submatrix e e * (twP G).submatrix e e) 1
    rw [Matrix.submatrix_mul_equiv, ← Matrix.submatrix_one_equiv e]
    exact fun s s' => h2 (e s) (e s')
  · change MAgree ((twD G).submatrix e e - (twB G).submatrix e e * Q.submatrix e e *
      (twC G).submatrix e e) ((2 : A) • G'.submatrix e e)
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact fun s s' => h3 (e s) (e s')

/-- **(V3)** of `C48_cleanliness_one_move.md` (Theorem 10.15, the split move): if `h ∉ P` and
`Good Γ`, there is `Γ'` with `Good Γ'` and
`CleanStep (vsplit (covSys P h c Γ))
(fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q'))`. -/
theorem V3 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hP : h ∉ P) (hG : Good Γ) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      CleanStep (vsplit (covSys P h c Γ))
        (fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q')) := by
  obtain ⟨Γ', hG', hC, -⟩ := W5 (insert h P) h c (vsplitG h Γ) ((V2 h Γ).1 hG)
  refine ⟨Γ', hG', ?_⟩
  have hV : vsplit (covSys P h c Γ) = fun q q' =>
      covSys (insert h P) h c (vsplitG h Γ) (splitDn P h hP q) (splitDn P h hP q') :=
    funext fun q => funext fun q' => V1 P h c Γ hP q q'
  rw [hV]
  exact L1 (splitDn P h hP) _ _ hC

end Cleanliness
