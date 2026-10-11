module

public import RequestProject.Smith2.PartZ

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`, Part Z — truncation with one zero diagonal entry

(Z3) `Z3`.

The proof follows the sketch of the file, in blocks `Fin m ⊕ Fin 1` (Mathlib's `fromBlocks`,
transported to `Fin (m + 1)` along `finSumFinEquiv`). With `Z := P X Q = D + 2^N S`
(`D = diagonal (if j < m then u j 2^{E j} else 0)`), write `Z = Dl * Y` with
`Dl = diagonal (u j 2^{E j}, 1)`; the upper-left block of `Y` is `1 + 2 W`, of unit determinant.
A column operation of unit determinant gives `Y U = [[1, 0], [C A⁻¹, s]]`, and `s = 0` because
`det Z = 0` (so `det Y = 0`). Then `C A⁻¹ = 2^N T`, a row operation `[[1, 0], [K, 1]]` with
`K j = −T j 2^{N − E j} u_j⁻¹` (integral since `E j < N`) clears it, and `diagonal (u_j⁻¹, 1)`
normalizes the units.
-/

@[expose] public section

noncomputable section

namespace ZeroSmith

open Matrix

/-- Proof of (Z3) of `C49c_smith_form_and_cokernel_at_zero.md`, in blocks `Fin m ⊕ Fin 1`: if
`Z = diagonal (u j 2^{E j}, 0) + 2^N S` with units `u j`, `E j < N` and `det Z = 0`, then
`P' Z Q' = diagonal (2^{E j}, 0)` for some `P' Q'` of unit determinant. -/
lemma Z3_sum (m N : ℕ) (u : Fin m → ℤ_[2]) (hu : ∀ j, IsUnit (u j)) (E : Fin m → ℕ)
    (hE : ∀ j, E j < N) (Z S : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ_[2])
    (hZ : Z = diagonal (Sum.elim (fun j => u j * 2 ^ E j) 0) + (2 : ℤ_[2]) ^ N • S)
    (hdet : Z.det = 0) :
    ∃ P' Q' : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * Z * Q' = diagonal (Sum.elim (fun j => (2 : ℤ_[2]) ^ E j) 0) := by
  set W : Matrix (Fin m) (Fin m ⊕ Fin 1) ℤ_[2] :=
    Matrix.of fun i j => Ring.inverse (u i) * 2 ^ (N - E i - 1) * S (Sum.inl i) j
  set Y : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ_[2] := Matrix.of fun i j =>
    Sum.elim (fun i' => (1 : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ_[2]) (Sum.inl i') j +
      2 * W i' j) (fun i' => Z (Sum.inr i') j) i
  set Dl : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℤ_[2] :=
    diagonal (Sum.elim (fun j => u j * 2 ^ E j) 1)
  -- `Z = Dl * Y`
  have hZY : Z = Dl * Y := by
    ext i j
    rw [diagonal_mul]
    rcases i with i | i
    · simp only [Y, W, of_apply, Sum.elim_inl]
      rw [hZ]
      simp only [add_apply, smul_apply, smul_eq_mul, diagonal_apply, one_apply]
      have hu1 : u i * Ring.inverse (u i) = 1 := Ring.mul_inverse_cancel _ (hu i)
      have hpow : (2 : ℤ_[2]) ^ N = 2 ^ E i * 2 * 2 ^ (N - E i - 1) := by
        rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; have := hE i; omega
      rw [hpow]
      split_ifs with h
      · subst h; simp
        linear_combination (-(2 ^ E i * 2 * 2 ^ (N - E i - 1) * S (Sum.inl i) (Sum.inl i))) * hu1
      · simp; linear_combination (-(2 ^ E i * 2 * 2 ^ (N - E i - 1) * S (Sum.inl i) j)) * hu1
    · simp [Y]
  have hDl : Dl.det ≠ 0 := by
    rw [det_diagonal, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, Finset.prod_const_one, mul_one]
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact mul_ne_zero (hu j).ne_zero (pow_ne_zero _ two_ne_zero)
  have hY0 : Y.det = 0 := by
    rw [hZY, det_mul] at hdet
    exact (mul_eq_zero.1 hdet).resolve_left hDl
  -- the blocks of `Y`
  set A := Y.toBlocks₁₁
  set B := Y.toBlocks₁₂
  set C := Y.toBlocks₂₁
  set Dd := Y.toBlocks₂₂
  have hA : A = 1 + (2 : ℤ_[2]) • Matrix.of fun i j => W i (Sum.inl j) := by
    ext i j
    simp [A, Y, toBlocks₁₁, one_apply]
  have hAu : IsUnit A.det := hA ▸ Smith2.isUnit_det_one_add_two _
  have hYb : Y = fromBlocks A B C Dd := (fromBlocks_toBlocks Y).symm
  -- the column operation
  set U := fromBlocks A⁻¹ (-(A⁻¹ * B)) 0 (1 : Matrix (Fin 1) (Fin 1) ℤ_[2])
  have hYU : Y * U = fromBlocks 1 0 (C * A⁻¹) (Dd - C * A⁻¹ * B) := by
    rw [hYb, fromBlocks_multiply]
    simp [mul_nonsing_inv _ hAu, Matrix.mul_neg, ← Matrix.mul_assoc, sub_eq_add_neg, add_comm]
  have hUu : IsUnit U.det := by
    rw [det_fromBlocks_zero₂₁, det_one, mul_one]; exact isUnit_nonsing_inv_det _ hAu
  have hs : Dd - C * A⁻¹ * B = 0 := by
    have h := congrArg det hYU
    rw [det_mul, hY0, zero_mul, det_fromBlocks_zero₁₂, det_one, one_mul, det_unique] at h
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    exact h.symm
  rw [hs] at hYU
  -- the row operation
  set T := S.toBlocks₂₁ * A⁻¹
  have hCT : C * A⁻¹ = (2 : ℤ_[2]) ^ N • T := by
    have : C = (2 : ℤ_[2]) ^ N • S.toBlocks₂₁ := by
      ext i j; simp [C, Y, toBlocks₂₁, hZ]
    rw [this, Matrix.smul_mul]
  rw [hCT] at hYU
  set K : Matrix (Fin 1) (Fin m) ℤ_[2] :=
    Matrix.of fun i j => -(T i j * 2 ^ (N - E j) * Ring.inverse (u j))
  have hDl' : Dl = fromBlocks (diagonal fun j => u j * 2 ^ E j) 0 0 1 := by
    rw [← diagonal_one, fromBlocks_diagonal]; rfl
  have hKD : K * diagonal (fun j => u j * 2 ^ E j) + (2 : ℤ_[2]) ^ N • T = 0 := by
    ext i j
    simp only [K, mul_diagonal, add_apply, of_apply, smul_apply, smul_eq_mul, zero_apply]
    have hu1 : Ring.inverse (u j) * u j = 1 := Ring.inverse_mul_cancel _ (hu j)
    have hpow : (2 : ℤ_[2]) ^ N = 2 ^ (N - E j) * 2 ^ E j := by
      rw [← pow_add]; congr 1; have := hE j; omega
    rw [hpow]
    linear_combination (-(T i j * 2 ^ (N - E j) * 2 ^ E j)) * hu1
  have hfin : diagonal (Sum.elim (fun j => (2 : ℤ_[2]) ^ E j) (0 : Fin 1 → ℤ_[2])) =
      fromBlocks (diagonal fun j => (2 : ℤ_[2]) ^ E j) 0 0 0 := by
    rw [← fromBlocks_diagonal]; congr 1; exact diagonal_zero
  have hinv : (diagonal fun j => Ring.inverse (u j)) * (diagonal fun j => u j * 2 ^ E j) =
      diagonal fun j => (2 : ℤ_[2]) ^ E j := by
    rw [diagonal_mul_diagonal]; congr 1; funext j
    rw [← mul_assoc, Ring.inverse_mul_cancel _ (hu j), one_mul]
  refine ⟨fromBlocks (diagonal fun j => Ring.inverse (u j)) 0 0 1 * fromBlocks 1 0 K 1, U, ?_,
    hUu, ?_⟩
  · rw [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
    simp only [det_one, mul_one, det_diagonal]
    exact IsUnit.prod_univ_iff.mpr fun j => (hu j).ringInverse
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hZY, Matrix.mul_assoc, hYU, hDl', hfin]
    simp only [fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, hKD, hinv]

/-- Proof of (Z3) of `C49c_smith_form_and_cokernel_at_zero.md`, on `Fin (m + 1)`: `Z3_sum`
transported along `finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)`. -/
lemma Z3_core (m N : ℕ) (u : ℕ → ℤ_[2]) (hu : ∀ j, IsUnit (u j)) (E : ℕ → ℕ)
    (hE : ∀ j < m, E j < N) (Z S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2])
    (hZ : Z = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then u j * 2 ^ E j else 0) +
      (2 : ℤ_[2]) ^ N • S)
    (hdet : Z.det = 0) :
    ∃ P' Q' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * Z * Q' = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then (2 : ℤ_[2]) ^ E j
        else 0) := by
  set e : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  have he : ∀ x : Fin m ⊕ Fin 1, ((e x : Fin (m + 1)) : ℕ) < m ↔ x.isLeft := by
    intro x; rcases x with x | x
    · simp [e, x.2]
    · simp [e, Fin.fin_one_eq_zero x]
  obtain ⟨P', Q', hP', hQ', hD⟩ := Z3_sum m N (fun j => u j) (fun j => hu j) (fun j => E j)
    (fun j => hE j j.2) (Z.submatrix e e) (S.submatrix e e) (by
      rw [hZ]
      ext i j
      simp only [submatrix_apply, add_apply, smul_apply, diagonal_apply,
        EmbeddingLike.apply_eq_iff_eq]
      congr 1
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        rcases i with x | x
        · simp [e]
        · simp [e, Fin.fin_one_eq_zero x]
      · rw [if_neg hij, if_neg hij])
    (by rw [det_submatrix_equiv_self]; exact hdet)
  refine ⟨P'.submatrix e.symm e.symm, Q'.submatrix e.symm e.symm,
    by rw [det_submatrix_equiv_self]; exact hP', by rw [det_submatrix_equiv_self]; exact hQ', ?_⟩
  have hZ' : Z = (Z.submatrix e e).submatrix e.symm e.symm := by simp
  rw [hZ', submatrix_mul_equiv, submatrix_mul_equiv, hD, submatrix_diagonal_equiv]
  congr 1; funext j
  obtain ⟨x, rfl⟩ := e.surjective j
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rcases x with x | x
  · simp [e, x.2]
  · simp [e, Fin.fin_one_eq_zero x]

/-- **(Z3)** of `C49c_smith_form_and_cokernel_at_zero.md` (truncation with one zero diagonal
entry): let `X` over `ℤ_[2]` and `Y` over `ℤ` on `Fin (m + 1)` with
`X i j − (Y i j : ℤ_[2]) = 2^N * R i j` for some `R`; `P Q` over `ℤ` with odd determinants;
`u : ℕ → ℤ` with every `u j` odd; `E : ℕ → ℕ` with `E j < N` for `j < m`;
`P * Y * Q = diagonal (fun j => if j < m then u j * 2 ^ E j else 0)`; and `X.det = 0`. Then there
are `P' Q'` over `ℤ_[2]` with unit determinants and
`P' * X * Q' = diagonal (fun j => if j < m then (2 : ℤ_[2]) ^ E j else 0)`. -/
theorem Z3 (m N : ℕ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2])
    (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ)
    (hXY : ∃ R : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2],
      ∀ i j, X i j - (Y i j : ℤ_[2]) = 2 ^ N * R i j)
    (P Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ) (hP : Odd P.det) (hQ : Odd Q.det) (u : ℕ → ℤ)
    (hu : ∀ j, Odd (u j)) (E : ℕ → ℕ) (hE : ∀ j < m, E j < N)
    (h : P * Y * Q = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then u j * 2 ^ E j else 0))
    (hdet : X.det = 0) :
    ∃ P' Q' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * X * Q' = diagonal (fun j : Fin (m + 1) => if (j : ℕ) < m then (2 : ℤ_[2]) ^ E j
        else 0) := by
  obtain ⟨R, hR⟩ := hXY
  set ι := Int.castRingHom ℤ_[2]
  have hX : X = Y.map ι + (2 : ℤ_[2]) ^ N • R := by
    ext i j; simp [ι, ← hR i j]
  have hD : P.map ι * Y.map ι * Q.map ι = diagonal (fun j : Fin (m + 1) =>
      if (j : ℕ) < m then ((u j : ℤ) : ℤ_[2]) * 2 ^ E j else 0) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h, diagonal_map (map_zero _)]
    congr 1; funext j; split_ifs <;> simp [ι]
  have hPd : IsUnit (P.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact FamilyGroup.U1 hP
  have hQd : IsUnit (Q.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact FamilyGroup.U1 hQ
  obtain ⟨P', Q', hP', hQ', hD'⟩ := Z3_core m N (fun j => ((u j : ℤ) : ℤ_[2]))
    (fun j => FamilyGroup.U1 (hu j)) E hE (P.map ι * X * Q.map ι) (P.map ι * R * Q.map ι)
    (by rw [hX, Matrix.mul_add, Matrix.add_mul, hD, Matrix.mul_smul, Matrix.smul_mul])
    (by rw [det_mul, det_mul, hdet, mul_zero, zero_mul])
  refine ⟨P' * P.map ι, Q.map ι * Q', by rw [det_mul]; exact hP'.mul hPd,
    by rw [det_mul]; exact hQd.mul hQ', ?_⟩
  rw [← hD']
  simp only [Matrix.mul_assoc]

end ZeroSmith
