module

public import RequestProject.ZeroSmith.PartG
public import RequestProject.ZeroSmith.PartZ

/-!
# `C49c_smith_form_and_cokernel_at_zero.md`, Part V — the Smith form of `Ξ_0` and its
# equivalence with `M^{(α)}(l, 0)`

(V4) `V4`; (V5) `V5`; (V6) `V6`; (V7) `V7`.

Hypotheses (H0), as in C49b: `1 ≤ l`, `2 ≤ α`, `η : ℤ_[2]` with `IsUnit η`, `z : ℕ → ℤ_[2]`, and
`GkZ` with `DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ`.
With `ds := Families.ds l` and `cs := Fin.cast (Smith2.slots_cast ds)`, the matrix of the file is
`X := (finalM GkZ).submatrix cs cs`, written out in each statement.
-/

@[expose] public section

noncomputable section

namespace ZeroSmith

open FormalOps FormalDance Windows DanceSmith Matrix Finset

/-- (Z3) of `C49c_smith_form_and_cokernel_at_zero.md` on `Fin n` with `1 ≤ n` (the diagonal
condition `j < n − 1`), used in the proof of (V5). -/
lemma Z3_fin {n : ℕ} (hn : 1 ≤ n) (N : ℕ) (X : Matrix (Fin n) (Fin n) ℤ_[2])
    (Y : Matrix (Fin n) (Fin n) ℤ)
    (hXY : ∃ R : Matrix (Fin n) (Fin n) ℤ_[2], ∀ i j, X i j - (Y i j : ℤ_[2]) = 2 ^ N * R i j)
    (P Q : Matrix (Fin n) (Fin n) ℤ) (hP : Odd P.det) (hQ : Odd Q.det) (u : ℕ → ℤ)
    (hu : ∀ j, Odd (u j)) (E : ℕ → ℕ) (hE : ∀ j < n - 1, E j < N)
    (h : P * Y * Q = diagonal (fun j : Fin n => if (j : ℕ) < n - 1 then u j * 2 ^ E j else 0))
    (hdet : X.det = 0) :
    ∃ P' Q' : Matrix (Fin n) (Fin n) ℤ_[2], IsUnit P'.det ∧ IsUnit Q'.det ∧
      P' * X * Q' = diagonal (fun j : Fin n => if (j : ℕ) < n - 1 then (2 : ℤ_[2]) ^ E j
        else 0) := by
  cases n with
  | zero => omega
  | succ m => exact Z3 m N X Y hXY P Q hP hQ u hu E hE h hdet

/-- **(V4)** of `C49c_smith_form_and_cokernel_at_zero.md` (truncations): under (H0) there is `N₀`
such that for every `N ≥ N₀`, `Data0 ds α (Smith2.trunc N X)`, and every `E : ℕ → ℕ` with
`(E j : ℤ) = α 2^k + yHatS ds α (2^m − 2 − j)` for `j < 2^m − 1` has `E j < N` for those `j`
(`ds = Families.ds l`, `m = Dance.mCount ds`, `k = ds.length`, `X = (finalM GkZ).submatrix cs cs`). -/
theorem V4 {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Data0 (Families.ds l) α (Smith2.trunc N ((finalM GkZ).submatrix
        (Fin.cast (Smith2.slots_cast (Families.ds l)))
        (Fin.cast (Smith2.slots_cast (Families.ds l))))) ∧
      (∀ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l) - 1,
          (E j : ℤ) = (α : ℤ) * 2 ^ (Families.ds l).length +
            yHatS (Families.ds l) α (2 ^ Dance.mCount (Families.ds l) - 2 - j)) →
        ∀ j < 2 ^ Dance.mCount (Families.ds l) - 1, E j < N) := by
  have hk := Stability.length_ds_pos hl
  set f1 : Fin (2 ^ Dance.mCount (Families.ds l)) × Fin (2 ^ Dance.mCount (Families.ds l)) → ℕ := fun p =>
    ((α : ℤ) * 2 ^ (Families.ds l).length + Houses.cHatH (Ids (Families.ds l)) (Families.ds l).length (2 ^ (Families.ds l).length - 1) (α : ℤ)
      (Dset (Families.ds l) p.1) (Dset (Families.ds l) p.2)).toNat
  set f2 : Fin (2 ^ Dance.mCount (Families.ds l)) → ℕ := fun j =>
    ((α : ℤ) * 2 ^ (Families.ds l).length + yHatS (Families.ds l) α ((2 ^ Dance.mCount (Families.ds l)) - 2 - j)).toNat
  refine ⟨univ.sup f1 + univ.sup f2 + 1, fun N hN => ⟨fun s s' => ?_, fun E hE j hj => ?_⟩⟩
  · set x := finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l)) s) (Fin.cast (Smith2.slots_cast (Families.ds l)) s')
    have hV : ‖x‖ = ‖((finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])‖ :=
      ContZero.V1 hl hα hη z GkZ hG s s'
    have hZ := Smith2.Z0 x N
    have hD := G2 (Families.ds l) hk α (by omega) s s'
    have hx0 : finalMatrix ℤ (Families.ds l) α 0 s s' = 0 → x = 0 := fun h0 =>
      norm_eq_zero.1 (by rw [hV, h0]; simp)
    have htr : Smith2.trunc N ((finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
        (Fin.cast (Smith2.slots_cast (Families.ds l)))) s s' = ((x.appr N : ℕ) : ℤ) := rfl
    rw [htr]
    refine ⟨fun hsub => ?_, fun he => ?_, fun hsub hne => ?_⟩
    · rw [hZ.2.1 (hx0 (hD.1 hsub))]; rfl
    · rw [hZ.2.1 (hx0 (hD.2.1 he))]; rfl
    · obtain ⟨h0, n, hn, h1, h2⟩ := hD.2.2 hsub hne
      have hnorm : ‖x‖ = (2 : ℝ) ^ (-(n : ℤ)) := by
        rw [hV]; exact Smith2.norm_int_of_exact h1 h2
      have hxne : x ≠ 0 := by
        intro hx
        rw [hx, norm_zero] at hnorm
        exact absurd hnorm.symm (by positivity)
      have hnN : n < N := by
        have : n = f1 (s, s') := by simp only [f1]; rw [← hn, Int.toNat_natCast]
        have hle : f1 (s, s') ≤ univ.sup f1 := le_sup (mem_univ _)
        omega
      obtain ⟨g1, g2, g3⟩ := hZ.2.2 n hxne hnorm hnN
      exact ⟨g1, n, hn, g2, g3⟩
  · have hjM : j < (2 ^ Dance.mCount (Families.ds l)) := by omega
    have : E j = f2 ⟨j, hjM⟩ := by simp only [f2]; rw [← hE j hj, Int.toNat_natCast]
    have hle : f2 ⟨j, hjM⟩ ≤ univ.sup f2 := le_sup (mem_univ _)
    omega

/-- **(V5)** of `C49c_smith_form_and_cokernel_at_zero.md` (Smith form over `ℤ_[2]`): under (H0)
and `Ids ds ≠ ∅`, there are `P Q` over `ℤ_[2]` with unit determinants and `E : ℕ → ℕ` with
`(E j : ℤ) = α 2^k + yHatS ds α (2^m − 2 − j)` for `j < 2^m − 1`, such that
`P * X * Q = diagonal (fun j => if j < 2^m − 1 then (2 : ℤ_[2]) ^ E j else 0)`. -/
theorem V5 {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ)
    (hne : Ids (Families.ds l) ≠ ∅) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
        (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount (Families.ds l) - 1,
          (E j : ℤ) = (α : ℤ) * 2 ^ (Families.ds l).length +
            yHatS (Families.ds l) α (2 ^ Dance.mCount (Families.ds l) - 2 - j)) ∧
        P * (finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
          (Fin.cast (Smith2.slots_cast (Families.ds l))) * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount (Families.ds l)) =>
            if (j : ℕ) < 2 ^ Dance.mCount (Families.ds l) - 1 then (2 : ℤ_[2]) ^ E j else 0) := by
  have hk := Stability.length_ds_pos hl
  set X := (finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
    (Fin.cast (Smith2.slots_cast (Families.ds l)))
  obtain ⟨N₀, hN₀⟩ := V4 hl hα hη z GkZ hG
  obtain ⟨hG1, hEb⟩ := hN₀ N₀ le_rfl
  obtain ⟨P, Q, hP, hQ, u, hu, E, hE, hD⟩ :=
    G1 (Families.ds l) hk α (by omega) hne (Smith2.trunc N₀ X) hG1
  have hXY : ∃ R : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
      (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      ∀ i j, X i j - (Smith2.trunc N₀ X i j : ℤ_[2]) = 2 ^ N₀ * R i j :=
    ⟨fun i j => (Smith2.Z0 (X i j) N₀).1.choose, fun i j => by
      have := (Smith2.Z0 (X i j) N₀).1.choose_spec
      simp only [Smith2.trunc]; push_cast; exact this⟩
  have hdet : X.det = 0 := (ContZero.V3 hl hα hη z GkZ hG).2
  obtain ⟨P', Q', hP', hQ', hD'⟩ := Z3_fin Nat.one_le_two_pow N₀ X (Smith2.trunc N₀ X) hXY
    P Q hP hQ u hu E (hEb E hE) hD hdet
  exact ⟨P', Q', hP', hQ', E, hE, hD'⟩

/-- **(V6)** of `C49c_smith_form_and_cokernel_at_zero.md`: for `1 ≤ ds.length`, `1 ≤ α`,
`Ids ds ≠ ∅` (any `ds`, no dance needed), there are `P Q` over `ℤ_[2]` with unit determinants and
`E : ℕ → ℕ` with `(E j : ℤ) = α 2^k + yHatS ds α (2^m − 2 − j)` for `j < 2^m − 1`, such that
`P * (finalMatrix ℤ ds α 0).map (Int.castRingHom ℤ_[2]) * Q =
diagonal (fun j => if j < 2^m − 1 then (2 : ℤ_[2]) ^ E j else 0)` (C15 (Z3) mapped to `ℤ_[2]`). -/
theorem V6 (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧ ∃ E : ℕ → ℕ, (∀ j < 2 ^ Dance.mCount ds - 1,
          (E j : ℤ) = (α : ℤ) * 2 ^ ds.length + yHatS ds α (2 ^ Dance.mCount ds - 2 - j)) ∧
        P * (finalMatrix ℤ ds α 0).map (Int.castRingHom ℤ_[2]) * Q =
          diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
            if (j : ℕ) < 2 ^ Dance.mCount ds - 1 then (2 : ℤ_[2]) ^ E j else 0) := by
  obtain ⟨P, Q, hP, hQ, u, hu, E, hE, hD⟩ := DanceSmith.Z3 ds hk α hα hne
  set ι := Int.castRingHom ℤ_[2]
  have hDm : P.map ι * (finalMatrix ℤ ds α 0).map ι * Q.map ι = diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
      if (j : ℕ) < (2 ^ Dance.mCount ds) - 1 then ((u j : ℤ) : ℤ_[2]) * 2 ^ E j else 0) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hD, diagonal_map (map_zero _)]
    congr 1; funext j; split_ifs <;> simp [ι]
  have hPd : IsUnit (P.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact FamilyGroup.U1 hP
  have hQd : IsUnit (Q.map ι).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact FamilyGroup.U1 hQ
  set U : Matrix (Fin (2 ^ Dance.mCount ds)) (Fin (2 ^ Dance.mCount ds)) ℤ_[2] := diagonal (fun j : Fin (2 ^ Dance.mCount ds) =>
    if (j : ℕ) < (2 ^ Dance.mCount ds) - 1 then Ring.inverse ((u j : ℤ) : ℤ_[2]) else 1)
  have hU : IsUnit U.det := by
    rw [det_diagonal]
    refine IsUnit.prod_univ_iff.mpr fun j => ?_
    split_ifs
    · exact (FamilyGroup.U1 (hu j)).ringInverse
    · exact isUnit_one
  refine ⟨U * P.map ι, Q.map ι, by rw [det_mul]; exact hU.mul hPd, hQd, E, hE, ?_⟩
  rw [Matrix.mul_assoc U, Matrix.mul_assoc U, hDm,
    diagonal_mul_diagonal]
  congr 1; funext j
  split_ifs
  · rw [← mul_assoc, Ring.inverse_mul_cancel _ (FamilyGroup.U1 (hu j)), one_mul]
  · rw [mul_zero]

/-- **(V7)** of `C49c_smith_form_and_cokernel_at_zero.md` (equivalence): under (H0) there are
`P Q` over `ℤ_[2]` with unit determinants and
`X = P * (finalMatrix ℤ ds α 0).map (Int.castRingHom ℤ_[2]) * Q`. -/
theorem V7 {l α : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) {η : ℤ_[2]} (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ) :
    ∃ P Q : Matrix (Fin (2 ^ Dance.mCount (Families.ds l)))
        (Fin (2 ^ Dance.mCount (Families.ds l))) ℤ_[2],
      IsUnit P.det ∧ IsUnit Q.det ∧
        (finalM GkZ).submatrix (Fin.cast (Smith2.slots_cast (Families.ds l)))
          (Fin.cast (Smith2.slots_cast (Families.ds l))) =
          P * (finalMatrix ℤ (Families.ds l) α 0).map (Int.castRingHom ℤ_[2]) * Q := by
  have hk := Stability.length_ds_pos hl
  by_cases hne : Ids (Families.ds l) = ∅
  · have hM0 := (DanceSmith.Z1 (Families.ds l) α (by omega)).2 hne
    refine ⟨1, 1, by simp, by simp, ?_⟩
    rw [hM0, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]
    ext s s'
    exact (ContZero.V2 hl hα hη z GkZ hG s s').2 (by rw [hM0]; rfl)
  · obtain ⟨P₅, Q₅, hP₅, hQ₅, E₅, hE₅, hD₅⟩ := V5 hl hα hη z GkZ hG hne
    obtain ⟨P₆, Q₆, hP₆, hQ₆, E₆, hE₆, hD₆⟩ := V6 (Families.ds l) hk α (by omega) hne
    have hEE : (fun j : Fin (2 ^ Dance.mCount (Families.ds l)) =>
        if (j : ℕ) < 2 ^ Dance.mCount (Families.ds l) - 1 then (2 : ℤ_[2]) ^ E₅ j else 0) =
        fun j : Fin (2 ^ Dance.mCount (Families.ds l)) =>
          if (j : ℕ) < 2 ^ Dance.mCount (Families.ds l) - 1 then (2 : ℤ_[2]) ^ E₆ j else 0 := by
      funext j
      split_ifs with hj
      · have : (E₅ j : ℤ) = E₆ j := (hE₅ j hj).trans (hE₆ j hj).symm
        rw [show E₅ j = E₆ j by exact_mod_cast this]
      · rfl
    rw [hEE] at hD₅
    exact Smith2.Z2 hD₆ hD₅ hP₆ hQ₆ hP₅ hQ₅

end ZeroSmith
