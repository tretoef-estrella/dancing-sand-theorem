module

public import RequestProject.Bend.Defs

/-!
# `C50d_the_bend.md`: Part N — the matrix `N`

* (N0) `N0`: as in the proof of C42 `C109`, from C40c (N2), `sysAct_mul`, (A1), `sysAct_one` and
  C42's `magree_const_mul`.
* (N1) `N1`: both sides are linear; they agree on the basis vectors.
* (N2) `N2`: C42's `entry_sysAct`, multiplied by `2 ^ k`.
-/

@[expose] public section

noncomputable section

namespace Bend

open FormalOps FormalDance FormalAct Filt

/-- **(N0)** of `C50d_the_bend.md` (`Y` acts as the inverse): for `x Y : Bf ℚ_[2]` with
`Agree (x * Y) 1`, `Agree (Y * x) 1` and `B ≥ l + 1`, `sysAct (fun _ _ => x) ∘ₗ
sysAct (fun _ _ => Y) = LinearMap.id`, and the same with `x`, `Y` exchanged (on `T ℚ_[2] l`,
`W = l`, one slot). -/
theorem N0 (l B : ℕ) (hB : l + 1 ≤ B) (x Y : Bf ℚ_[2]) (hxY : Agree (x * Y) 1)
    (hYx : Agree (Y * x) 1) :
    sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => x : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) ∘ₗ
        sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) = LinearMap.id ∧
      sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) ∘ₗ
        sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => x) = LinearMap.id := by
  obtain ⟨htop, hnil⟩ := FormalAct.N2 (A := ℚ_[2]) l
  refine ⟨?_, ?_⟩
  · rw [← sysAct_mul hnil hB, FormalAct.A1 htop
      (InvFloors.magree_const_mul hxY (fun _ _ => rfl) (fun _ _ => rfl)) B, sysAct_one (by omega)]
  · rw [← sysAct_mul hnil hB, FormalAct.A1 htop
      (InvFloors.magree_const_mul hYx (fun _ _ => rfl) (fun _ _ => rfl)) B, sysAct_one (by omega)]

/-- **(N1)** of `C50d_the_bend.md` (`N` is `2^k out ∘ Y ∘ in`): for every `Y` and `B`,
`Matrix.mulVecLin (Nmat l B Y) = 2 ^ k • (outH l 1 ∘ₗ sysAct (fun _ _ => Y) ∘ₗ inH l 1)`. -/
theorem N1 (l B : ℕ) (Y : Bf ℚ_[2]) :
    Matrix.mulVecLin (Nmat l B Y) = (2 : ℚ_[2]) ^ (Families.ds l).length •
      (InvBlock.outH l 1 ∘ₗ sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) ∘ₗ
        InvBlock.inH l 1) := by
  refine LinearMap.pi_ext' fun X => LinearMap.ext_ring ?_
  funext Y'
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    LinearMap.smul_apply, Pi.smul_apply, LinearMap.coe_single, smul_eq_mul]
  rfl

/-- **(N2)** of `C50d_the_bend.md` (the entries): for `B ≥ l + 1`, every `Y` and all `X Y'`,
with `o_X = Rulers.oE (Windows.Dset (Families.ds l) X)`, `o_{Y'}` likewise and
`k = (Families.ds l).length`:
`Nmat l B Y Y' X = if o_X ≤ o_{Y'} + 2^k − 1 then 2 ^ k * gamma l X Y' *
Y.coef (o_{Y'} + 2^k − 1 − o_X) ((o_{Y'} + 2^k − 1 : ℕ) : ℤ) else 0`. -/
theorem N2 (l B : ℕ) (hB : l + 1 ≤ B) (Y : Bf ℚ_[2])
    (X Y' : Fin (Dance.slots (Families.ds l) 1)) :
    Nmat l B Y Y' X =
      if Rulers.oE (Windows.Dset (Families.ds l) X) ≤
          Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 then
        2 ^ (Families.ds l).length * InvFloors.gamma l X Y' *
          Y.coef (Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 -
            Rulers.oE (Windows.Dset (Families.ds l) X))
            ((Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 :
              ℕ) : ℤ)
      else 0 := by
  rw [Nmat_apply, InvFloors.entry_sysAct l B hB Y X Y']
  split_ifs
  · ring
  · rw [mul_zero]

end Bend
