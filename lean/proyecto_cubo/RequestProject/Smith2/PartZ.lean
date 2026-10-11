module

public import RequestProject.Smith2.Defs
public import RequestProject.FamilyGroup.Cokernel

/-!
# `C46_smith_form_and_cokernel_over_Z2.md`, Part Z — the Smith form over `ℤ_2` by truncation

(Z0) `Z0`; (Z1) `Z1`; (Z2) `Z2`. Norms are the norms of `ℤ_[2]`; `‖x‖ = 2^{−n}` is
`‖x‖ = (2 : ℝ) ^ (-(n : ℤ))`.
-/

@[expose] public section

noncomputable section

namespace Smith2

open Matrix

/-! ### (Z0) -/

/-- Part of (Z0) of `C46_smith_form_and_cokernel_over_Z2.md`: `norm_sub_appr_le`. -/
lemma norm_sub_appr_le (x : ℤ_[2]) (N : ℕ) :
    ‖x - ((x.appr N : ℕ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(N : ℤ)) := by
  have := PadicInt.appr_spec N x
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow] at this
  exact_mod_cast this

/-- **(Z0)** of `C46_smith_form_and_cokernel_over_Z2.md`: for `x : ℤ_[2]` and `N`,
`x − ((x.appr N : ℕ) : ℤ_[2]) = 2^N * r` for some `r` (i.e. it lies in `(2 : ℤ_[2]) ^ N • ⊤`);
if `x = 0` then `x.appr N = 0`; if `x ≠ 0`, `‖x‖ = 2^{−n}` and `n < N`, then
`y := ((x.appr N : ℕ) : ℤ)` satisfies `y ≠ 0`, `2^n ∣ y` and `¬ 2^(n+1) ∣ y`. -/
theorem Z0 (x : ℤ_[2]) (N : ℕ) :
    (∃ r : ℤ_[2], x - ((x.appr N : ℕ) : ℤ_[2]) = 2 ^ N * r) ∧
    (x = 0 → x.appr N = 0) ∧
    (∀ n : ℕ, x ≠ 0 → ‖x‖ = (2 : ℝ) ^ (-(n : ℤ)) → n < N →
      ((x.appr N : ℕ) : ℤ) ≠ 0 ∧ (2 : ℤ) ^ n ∣ ((x.appr N : ℕ) : ℤ) ∧
        ¬ (2 : ℤ) ^ (n + 1) ∣ ((x.appr N : ℕ) : ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · have := PadicInt.appr_spec N x
    rw [Ideal.mem_span_singleton] at this
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [hr]; push_cast; ring⟩
  · rintro rfl
    induction N with
    | zero => rfl
    | succ n ih => simp [PadicInt.appr, ih]
  · intro n hx hn hnN
    set y : ℤ := ((x.appr N : ℕ) : ℤ)
    have hy : ((y : ℤ) : ℤ_[2]) = ((x.appr N : ℕ) : ℤ_[2]) := by simp [y]
    have hlt : ‖(y : ℤ_[2]) - x‖ < ‖x‖ := by
      rw [← norm_neg, neg_sub, hy, hn]
      refine (norm_sub_appr_le x N).trans_lt ?_
      exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
    have hyn : ‖(y : ℤ_[2])‖ = (2 : ℝ) ^ (-(n : ℤ)) := by
      have h := PadicInt.norm_add_eq_max_of_ne (q := x) (r := (y : ℤ_[2]) - x) hlt.ne'
      rw [add_sub_cancel, max_eq_left hlt.le] at h
      rw [h, hn]
    refine ⟨?_, ?_, ?_⟩
    · intro h0
      rw [h0] at hyn
      simp at hyn
      exact absurd hyn.symm (by positivity)
    · have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := y) (n := n)).1
        (by rw [hyn]; norm_num)
      exact_mod_cast this
    · intro hd
      have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := y) (n := n + 1)).2
        (by exact_mod_cast hd)
      rw [hyn] at this
      have h2 : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) < (2 : ℝ) ^ (-(n : ℤ)) :=
        zpow_lt_zpow_right₀ (by norm_num) (by omega)
      push_cast at this h2
      linarith

/-! ### (Z1) -/

/-- Proof of (Z1) of `C46_smith_form_and_cokernel_over_Z2.md`: `det (1 + 2 W)` is a unit of
`ℤ_[2]` (reduction mod 2). -/
lemma isUnit_det_one_add_two {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℤ_[2]) :
    IsUnit (1 + (2 : ℤ_[2]) • W).det := by
  by_contra hn
  have hmem : (1 + (2 : ℤ_[2]) • W).det ∈ IsLocalRing.maximalIdeal ℤ_[2] :=
    (IsLocalRing.mem_maximalIdeal _).2 hn
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, RingHom.mapMatrix_apply] at hmem
  have h2 : (PadicInt.toZMod (2 : ℤ_[2]) : ZMod 2) = 0 := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]; rfl
  have : (1 + (2 : ℤ_[2]) • W).map PadicInt.toZMod = 1 := by
    ext i j
    simp [Matrix.one_apply, h2]
  rw [this, det_one] at hmem
  exact one_ne_zero hmem

/-- **(Z1)** of `C46_smith_form_and_cokernel_over_Z2.md`: let `X` over `ℤ_[2]`, `Y` over `ℤ`, `N`
with `X i j − (Y i j : ℤ_[2]) = 2^N * R i j` for some `R`; suppose `P Q` over `ℤ` with odd
determinants, odd integers `u j` and `E : ℕ → ℕ` with `E j < N` for `j < n`, such that
`P * Y * Q = diagonal (fun j => u j * 2 ^ E j)`. Then there are `P' Q'` over `ℤ_[2]` with unit
determinants and `P' * X * Q' = diagonal (fun j => (2 : ℤ_[2]) ^ E j)`. -/
theorem Z1 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℤ_[2]) (Y : Matrix (Fin n) (Fin n) ℤ) (N : ℕ)
    (hXY : ∃ R : Matrix (Fin n) (Fin n) ℤ_[2], ∀ i j, X i j - (Y i j : ℤ_[2]) = 2 ^ N * R i j)
    (P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd P.det) (hQ : Odd Q.det) (u : ℕ → ℤ)
    (hu : ∀ j, Odd (u j)) (E : ℕ → ℕ) (hE : ∀ j < n, E j < N)
    (h : P * Y * Q = diagonal (fun j : Fin n => u j * 2 ^ E j)) :
    ∃ P' Q' : Matrix (Fin n) (Fin n) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * X * Q' = diagonal (fun j : Fin n => (2 : ℤ_[2]) ^ E j) := by
  obtain ⟨R, hR⟩ := hXY
  set ι := Int.castRingHom ℤ_[2]
  have hX : X = Y.map ι + (2 : ℤ_[2]) ^ N • R := by
    ext i j; simp [ι, ← hR i j]
  have hD : P.map ι * Y.map ι * Q.map ι =
      diagonal (fun j : Fin n => (u j : ℤ_[2]) * 2 ^ E j) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h, diagonal_map (map_zero _)]
    congr 1; funext j; simp [ι]
  set S := P.map ι * R * Q.map ι
  set W' : Matrix (Fin n) (Fin n) ℤ_[2] :=
    Matrix.of fun i j => Ring.inverse (u i : ℤ_[2]) * 2 ^ (N - E i - 1) * S i j
  have hDW : diagonal (fun j : Fin n => (u j : ℤ_[2]) * 2 ^ E j) * ((2 : ℤ_[2]) • W') =
      (2 : ℤ_[2]) ^ N • S := by
    ext i j
    rw [diagonal_mul, smul_apply, smul_apply]
    simp only [W', of_apply]
    have hi := hE i i.2
    have hu1 : (u i : ℤ_[2]) * Ring.inverse (u i : ℤ_[2]) = 1 :=
      Ring.mul_inverse_cancel _ (FamilyGroup.U1 (hu i))
    have hpow : (2 : ℤ_[2]) ^ N = 2 ^ E i * 2 * 2 ^ (N - E i - 1) := by
      rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
    rw [hpow, smul_eq_mul, smul_eq_mul]
    linear_combination (2 ^ E i * 2 * 2 ^ (N - E i - 1) * S i j) * hu1
  have hPXQ : P.map ι * X * Q.map ι =
      diagonal (fun j : Fin n => (u j : ℤ_[2]) * 2 ^ E j) * (1 + (2 : ℤ_[2]) • W') := by
    rw [Matrix.mul_add, hDW, Matrix.mul_one, ← hD, hX, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  set U := diagonal (fun j : Fin n => Ring.inverse (u j : ℤ_[2]))
  have hUD : U * diagonal (fun j : Fin n => (u j : ℤ_[2]) * 2 ^ E j) =
      diagonal (fun j : Fin n => (2 : ℤ_[2]) ^ E j) := by
    rw [diagonal_mul_diagonal]; congr 1; funext j
    rw [← mul_assoc, Ring.inverse_mul_cancel _ (FamilyGroup.U1 (hu j)), one_mul]
  have hU : IsUnit U.det := by
    rw [det_diagonal]
    exact IsUnit.prod_univ_iff.mpr fun j => (FamilyGroup.U1 (hu j)).ringInverse
  have hW := isUnit_det_one_add_two W'
  have hPd : IsUnit (P.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact FamilyGroup.U1 hP
  have hQd : IsUnit (Q.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact FamilyGroup.U1 hQ
  refine ⟨U * P.map ι, Q.map ι * (1 + (2 : ℤ_[2]) • W')⁻¹, ?_, ?_, ?_⟩
  · rw [det_mul]; exact hU.mul hPd
  · rw [det_mul]; exact hQd.mul (isUnit_nonsing_inv_det _ hW)
  · calc U * P.map ι * X * (Q.map ι * (1 + (2 : ℤ_[2]) • W')⁻¹)
        = U * (P.map ι * X * Q.map ι) * (1 + (2 : ℤ_[2]) • W')⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (fun j : Fin n => (2 : ℤ_[2]) ^ E j) := by
          rw [hPXQ, ← Matrix.mul_assoc, hUD, Matrix.mul_assoc, mul_nonsing_inv _ hW,
            Matrix.mul_one]

/-! ### (Z2) -/

/-- **(Z2)** of `C46_smith_form_and_cokernel_over_Z2.md`: if `P₁ * X₁ * Q₁ = D` and
`P₂ * X₂ * Q₂ = D` with all four determinants units, then `X₂ = P * X₁ * Q` for some `P, Q` with
unit determinant. (Stated over any commutative ring and any finite index type; the file's case
is `ℤ_[2]`.) -/
theorem Z2 {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    {X₁ X₂ D P₁ Q₁ P₂ Q₂ : Matrix n n R} (h₁ : P₁ * X₁ * Q₁ = D) (h₂ : P₂ * X₂ * Q₂ = D)
    (hP₁ : IsUnit P₁.det) (hQ₁ : IsUnit Q₁.det) (hP₂ : IsUnit P₂.det) (hQ₂ : IsUnit Q₂.det) :
    ∃ P Q : Matrix n n R, IsUnit P.det ∧ IsUnit Q.det ∧ X₂ = P * X₁ * Q := by
  refine ⟨P₂⁻¹ * P₁, Q₁ * Q₂⁻¹, ?_, ?_, ?_⟩
  · rw [det_mul]; exact (isUnit_nonsing_inv_det P₂ hP₂).mul hP₁
  · rw [det_mul]; exact hQ₁.mul (isUnit_nonsing_inv_det Q₂ hQ₂)
  · have : X₂ = P₂⁻¹ * (P₂ * X₂ * Q₂) * Q₂⁻¹ := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hQ₂, Matrix.mul_one]
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ hP₂, Matrix.one_mul]
    rw [this, h₂, ← h₁]
    simp only [Matrix.mul_assoc]

end Smith2
