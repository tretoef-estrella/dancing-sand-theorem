import RequestProject.Dance.All

/-! Auditor's check file for Lean piece C13 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C13_the_dance.md` and closed by `rfl`; the main statements
restated by hand with the systems unfolded and closed by the certified theorems; then
`#print axioms`. -/

open Payment Split Dance DirectSum
open scoped Pointwise

-- Counts
example : mCount [true, false, true, true] = 3 := rfl
example : nLen [true, false, true, true] = 4 := rfl

-- The tower, digit by digit
example (rest : List Bool) : Idx (false :: rest) = (Idx rest × Fin 2) := rfl
example (rest : List Bool) : Idx (true :: rest) = (Idx rest × Fin 4) := rfl
example : Idx [] = Unit := rfl
example (rest : List Bool) : fl (false :: rest) = flΦ (fl rest) := rfl
example (rest : List Bool) : fl (true :: rest) = flΨ (fl rest) := rfl
example (A : Type) [CommRing A] (rest : List Bool) :
    Dance.F A (false :: rest) = FΦ (N := fun _ : Idx rest => A) (Dance.F A rest) := rfl
example (A : Type) [CommRing A] (rest : List Bool) :
    Dance.F A (true :: rest) = FΨ (N := fun _ : Idx rest => A) (Dance.F A rest) := rfl
example (A : Type) [CommRing A] : Dance.F A [] = 0 := rfl

-- Relabelling of the split slots: (s, j) ↦ 2s + j
example (r : ℕ) (s : Fin r) (j : Fin 2) : (splitIso r (toLex (s, j)) : ℕ) = 2 * s + j :=
  splitIso_val r s j

-- The dance data recursion
example (A : Type) [CommRing A] (rest : List Bool) (r : ℕ) (p : Fin r → ℕ → A)
    (κ : Fin r → Fin r → ℕ → A) :
    danceAux (false :: rest) r p κ = danceAux rest r (pT p) (κT p κ) := rfl
example (A : Type) [CommRing A] (rest : List Bool) (r : ℕ) (p : Fin r → ℕ → A)
    (κ : Fin r → Fin r → ℕ → A) :
    danceAux (true :: rest) r p κ =
      danceAux rest (r * 2) (fun t => pSp p ((splitIso r).symm t))
        (fun t u => κSp p κ ((splitIso r).symm t) ((splitIso r).symm u)) := rfl
example (r : ℕ) : slots [true, false, true] r = r * 2 * 2 := rfl

-- The final matrix, entry by entry
example (A : Type) [CommRing A] (R : ℕ) (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A)
    (s s' : Fin R) :
    Mfin p κ s s' = if s = s' then 2 * p s 0 else if s' < s then 2 * κ s s' 0 else 0 := rfl

-- σ
example (A : Type) [CommRing A] (α i f : ℕ) (s : Fin 1) :
    (pσ α i : Fin 1 → ℕ → A) s f = 2 ^ (α - 1) * ((i : A) + (f : A)) := rfl
example (A : Type) [CommRing A] (ds : List Bool) (α i : ℕ) :
    sigma A ds α i = G (fl ds) (Dance.F A ds) (pσ α i) κσ := rfl

-- (R1)
example (A : Type) [CommRing A] {ι : Type} [DecidableEq ι] {N : ι → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)] {S S' : Type} [Fintype S] [LinearOrder S]
    [Fintype S'] [LinearOrder S'] (fl : ι → ℕ) (F : (⨁ i, N i) →ₗ[A] (⨁ i, N i)) (e : S ≃o S')
    (p' : S' → ℕ → A) (κ' : S' → S' → ℕ → A) (c : A) :
    Nonempty ((Sys N S ⧸ LinearMap.range (c • G fl F (fun s => p' (e s))
        (fun s u => κ' (e s) (e u)))) ≃ₗ[A] (Sys N S' ⧸ LinearMap.range (c • G fl F p' κ'))) :=
  R1_coker fl F e p' κ' c

-- (D1)
example (A : Type) [CommRing A] (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A)
    (κ : Fin r → Fin r → ℕ → A) (h : ℕ) :
    Nonempty ((Sys (fun _ : Idx ds => A) (Fin r) ⧸
        LinearMap.range ((2 : A) ^ h • G (fl ds) (Dance.F A ds) p κ)) ≃ₗ[A]
      (Clocks A ds r h) × (Sys (fun _ : Idx [] => A) (Fin (r * 2 ^ mCount ds)) ⧸
        LinearMap.range ((2 : A) ^ (h + ds.length) •
          G (fl []) (Dance.F A []) (dance ds r p κ).1 (dance ds r p κ).2))) :=
  D1_scaled_dance ds r p κ h

-- (D2)
example (A : Type) [CommRing A] (ds : List Bool) (r h : ℕ) :
    Nonempty ((Clocks A ds r h) ≃ₗ[A] ((j : Fin ds.length) →
      (Fin (r * 2 ^ (ds.length + mCount ds - 1 - j)) → A) ⧸
        (2 : A) ^ (h + (j : ℕ)) •
          (⊤ : Submodule A (Fin (r * 2 ^ (ds.length + mCount ds - 1 - j)) → A)))) :=
  D2_clocks ds r h

-- (D3)
example (A : Type) [CommRing A] (R : ℕ) (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A)
    (c : A) :
    Nonempty ((Sys (fun _ : Idx [] => A) (Fin R) ⧸ LinearMap.range (c • G (fl []) (Dance.F A []) p κ))
      ≃ₗ[A] ((Fin R → A) ⧸ LinearMap.range (c • Matrix.toLin' (Mfin p κ)))) :=
  D3_final_matrix R p κ c

-- Proposition 4.3, over ℤ, for the digit list of λ = 4 (λ + 1 = 5 = 4 + 1: k = 2, I = {0})
example (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((Sys (fun _ : Idx [true, false] => ℤ) (Fin 1) ⧸
        LinearMap.range (G (fl [true, false]) (Dance.F ℤ [true, false]) (pσ α i) κσ)) ≃ₗ[ℤ]
      (((a : Fin 2) → (Fin (2 ^ (2 + 1 - 1 - (a : ℕ))) → ℤ) ⧸
          (2 : ℤ) ^ (a : ℕ) • (⊤ : Submodule ℤ (Fin (2 ^ (2 + 1 - 1 - (a : ℕ))) → ℤ))) ×
        ((Fin (2 ^ 1) → ℤ) ⧸ LinearMap.range ((2 : ℤ) ^ 2 •
          Matrix.toLin' ((Mfin (dance [true, false] 1 (pσ (A := ℤ) α i) κσ).1
              (dance [true, false] 1 (pσ α i) κσ).2).submatrix
            (Fin.cast (one_mul (2 ^ mCount [true, false])).symm)
            (Fin.cast (one_mul (2 ^ mCount [true, false])).symm)))))) :=
  proposition_4_3 [true, false] α i hα

-- Proposition 4.3, general form
example (A : Type) [CommRing A] (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((Sys (fun _ : Idx ds => A) (Fin 1) ⧸ LinearMap.range (sigma A ds α i)) ≃ₗ[A]
      (((a : Fin ds.length) → (Fin (2 ^ (ds.length + mCount ds - 1 - a)) → A) ⧸
          (2 : A) ^ (a : ℕ) • (⊤ : Submodule A (Fin (2 ^ (ds.length + mCount ds - 1 - a)) → A))) ×
        ((Fin (2 ^ mCount ds) → A) ⧸ LinearMap.range ((2 : A) ^ ds.length •
          Matrix.toLin' ((Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ α i) κσ).2).submatrix
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)))))) :=
  proposition_4_3 ds α i hα

-- (D4)
example (A : Type) [CommRing A] (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A)
    (κ : Fin r → Fin r → ℕ → A) :
    (∀ s s' : Fin (r * 2 ^ mCount ds), s < s' → Mfin (dance ds r p κ).1 (dance ds r p κ).2 s s' = 0) ∧
    (∀ s s' : Fin (r * 2 ^ mCount ds), s' ≤ s →
      ∃ a : A, Mfin (dance ds r p κ).1 (dance ds r p κ).2 s s' = 2 * a) :=
  D4_lower_triangular_even ds r p κ

#print axioms R1_intertwine
#print axioms R1_coker
#print axioms D1_aux
#print axioms D1_scaled_dance
#print axioms card_Idx
#print axioms D2_clocks
#print axioms D3_intertwine
#print axioms D3_final_matrix
#print axioms Mfin_relab
#print axioms proposition_4_3
#print axioms D4_lower_triangular_even
#print axioms slots_eq
#print axioms splitIso_val
