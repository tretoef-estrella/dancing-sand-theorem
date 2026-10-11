import RequestProject.Windows.All

/-! Auditor's check file for Lean piece C14 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C14_windows_and_theorem_D.md` and closed by `rfl`/`decide`;
the main statements restated by hand with every object unfolded and closed by the certified
theorems; then `#print axioms`. -/

open Finset Deficit Payment Split Dance Windows
open scoped Pointwise

-- The family I(ds) = {t < length ds : ds[t] = true}
example (ds : List Bool) :
    Ids ds = (Finset.range ds.length).filter (fun t => ds[t]? = some true) := rfl
example : Ids [true, false, true] = {0, 2} := by decide
-- rank t = #{u ∈ I : u < t}
example (I : Finset ℕ) (t : ℕ) : Windows.rank I t = (I.filter (· < t)).card := rfl
-- The dancers of a slot: the smallest t is the most significant bit
example (ds : List Bool) (s : ℕ) :
    Dset ds s = (Ids ds).filter
      (fun t => Nat.testBit s (mCount ds - 1 - Windows.rank (Ids ds) t) = true) := rfl
example : Dset [true, false, true] 2 = {0} := by decide
example : Dset [true, false, true] 1 = {2} := by decide
example : Dset [true, false, true] 3 = {0, 2} := by decide
-- The final matrix, read on Fin (2^m) as in proposition_4_3
example (A : Type) [CommRing A] (ds : List Bool) (α i : ℕ) :
    finalMatrix A ds α i =
      (Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ (A := A) α i) κσ).2).submatrix
        (Fin.cast (one_mul (2 ^ mCount ds)).symm) (Fin.cast (one_mul (2 ^ mCount ds)).symm) := rfl

-- (H1) the dance commutes with ring homomorphisms
example (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (ds : List Bool) (r : ℕ)
    (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    dance ds r (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) =
      ((fun s f => φ ((dance ds r p κ).1 s f)),
        (fun s u f => φ ((dance ds r p κ).2 s u f))) :=
  H1_dance φ ds r p κ

-- (H2)
example (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (R : ℕ)
    (p : Fin R → ℕ → A) (κ : Fin R → Fin R → ℕ → A) :
    Mfin (fun s f => φ (p s f)) (fun s u f => φ (κ s u f)) = (Mfin p κ).map φ :=
  H2_Mfin φ p κ

-- (H3)
example (A : Type) [CommRing A] (ds : List Bool) (α i : ℕ) :
    Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ (A := A) α i) κσ).2 =
      (Mfin (dance ds 1 (pσ (A := ℤ) α i) κσ).1 (dance ds 1 (pσ (A := ℤ) α i) κσ).2).map
        (Int.castRingHom A) :=
  H3_final_matrix A ds α i

-- (W), the windows after h moves, with π_0(d) = 2^α (i + d) written out
example (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (h : ℕ) (hh : h ≤ ds.length) (f : ℕ)
    (s s' : Fin (1 * 2 ^ mCount (ds.take h))) :
    (dance (ds.take h) 1 (pσ (A := ℚ) α i) κσ).1 s f =
        1 / 2 * Deficit.c (Ids ds) h ∅ *
          ∏ d ∈ Ico (2 ^ h * f + Rulers.oE (Dset (ds.take h) s))
            (2 ^ h * f + Rulers.oE (Dset (ds.take h) s) + 2 ^ h), Deficit.pi0 (α : ℤ) i d ∧
      (s' < s → Dset (ds.take h) s' ⊆ Dset (ds.take h) s →
        (dance (ds.take h) 1 (pσ (A := ℚ) α i) κσ).2 s s' f =
          1 / 2 * Deficit.c (Ids ds) h (Dset (ds.take h) s \ Dset (ds.take h) s') *
            ∏ d ∈ Ico (2 ^ h * f + Rulers.oE (Dset (ds.take h) s))
              (2 ^ h * f + Rulers.oE (Dset (ds.take h) s') + 2 ^ h), Deficit.pi0 (α : ℤ) i d) ∧
      (s' < s → ¬ Dset (ds.take h) s' ⊆ Dset (ds.take h) s →
        (dance (ds.take h) 1 (pσ (A := ℚ) α i) κσ).2 s s' f = 0) :=
  W_windows ds α i hα h hh f s s'

-- π_0 is 2^α (i + d)
example (α : ℤ) (i d : ℕ) : Deficit.pi0 α i d = (2 : ℚ) ^ α * ((i : ℚ) + d) := rfl
-- Mc(D, D') = −2^{1 − 2^k + o(D∖D')} a_k(D∖D') ∏_{[o_D, o_{D'} + 2^k)} π_0
example (I : Finset ℕ) (k : ℕ) (α : ℤ) (i : ℕ) (D D' : Finset ℕ) :
    Deficit.Mc I k α i D D' = -(2 : ℚ) ^ ((1 : ℤ) - 2 ^ k + Rulers.oE (D \ D')) *
      (Deficit.a I k (D \ D') : ℚ) * ∏ d ∈ Ico (Rulers.oE D) (Rulers.oE D' + 2 ^ k), Deficit.pi0 α i d :=
  rfl

-- Theorem 4.4
example (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ mCount ds)) :
    (Mfin (dance ds 1 (pσ (A := ℚ) α i) κσ).1 (dance ds 1 (pσ (A := ℚ) α i) κσ).2).submatrix
        (Fin.cast (one_mul (2 ^ mCount ds)).symm) (Fin.cast (one_mul (2 ^ mCount ds)).symm) s s' =
      if Dset ds s' ⊆ Dset ds s then Deficit.Mc (Ids ds) ds.length (α : ℤ) i (Dset ds s) (Dset ds s')
      else 0 :=
  theorem_4_4 ds α i hα s s'

-- Theorem D (D-i), over ℤ, with sigma and the final matrix written out
example (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((SysT ℤ ds (Fin 1) ⧸ LinearMap.range (sigma ℤ ds α i)) ≃ₗ[ℤ]
      (((a : Fin ds.length) → (Fin (2 ^ (ds.length + mCount ds - 1 - (a : ℕ))) → ℤ) ⧸
          (2 : ℤ) ^ (a : ℕ) •
            (⊤ : Submodule ℤ (Fin (2 ^ (ds.length + mCount ds - 1 - (a : ℕ))) → ℤ))) ×
        ((Fin (2 ^ mCount ds) → ℤ) ⧸ LinearMap.range ((2 : ℤ) ^ ds.length •
          Matrix.toLin' ((Mfin (dance ds 1 (pσ (A := ℤ) α i) κσ).1
              (dance ds 1 (pσ (A := ℤ) α i) κσ).2).submatrix
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)))))) :=
  theorem_D_i ds α i hα

-- (D-ii)
example (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ mCount ds)) :
    (Dset ds s' ⊆ Dset ds s →
      ((finalMatrix ℤ ds α i s s' : ℤ) : ℚ) =
        Deficit.Mc (Ids ds) ds.length (α : ℤ) i (Dset ds s) (Dset ds s')) ∧
    (¬ Dset ds s' ⊆ Dset ds s → finalMatrix ℤ ds α i s s' = 0) :=
  theorem_D_ii ds α i hα s s'

-- (D-iii), with Δ = D(ds,s) \ D(ds,s')
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α)
    (s s' : Fin (2 ^ mCount ds)) (hD : Dset ds s' ⊆ Dset ds s)
    (hi : 0 < i + Rulers.oE (Dset ds s)) :
    finalMatrix ℤ ds α i s s' ≠ 0 ∧
      (padicValInt 2 (finalMatrix ℤ ds α i s s') : ℤ) =
        1 - (2 : ℤ) ^ ds.length + (Rulers.oE (Dset ds s \ Dset ds s') : ℤ) +
          Rulers.delta ds.length (Dset ds s \ Dset ds s') +
          ∑ d ∈ Ico (Rulers.oE (Dset ds s)) (Rulers.oE (Dset ds s') + 2 ^ ds.length),
            ((α : ℤ) + (Rulers.v2 (i + d) : ℤ)) :=
  theorem_D_iii ds hk α i hα s s' hD hi

-- (D-iv)
example (A : Type) [CommRing A] (ds : List Bool) (α i : ℕ) :
    finalMatrix A ds α i = (finalMatrix ℤ ds α i).map (Int.castRingHom A) :=
  theorem_D_iv A ds α i

#print axioms H1_dance
#print axioms H2_Mfin
#print axioms H2_pσ
#print axioms H3_final_matrix
#print axioms W_windows
#print axioms theorem_4_4
#print axioms theorem_D_i
#print axioms theorem_D_ii
#print axioms theorem_D_iii
#print axioms theorem_D_iv
#print axioms theorem_D
#print axioms windows_gen
#print axioms card_Ids
