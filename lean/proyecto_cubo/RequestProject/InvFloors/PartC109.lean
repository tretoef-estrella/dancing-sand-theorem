module

public import RequestProject.InvFloors.PartC

/-!
# `C42_floors_and_corollary_10_9.md`: (C109) Corollary 10.9

* `entry_sysAct` (auxiliary, over any `A`): for a single formal operator `Y` acting on the single
  slot, `outH l 1 (sysAct (T A l) l B (fun _ _ => Y) (inH l 1 (Pi.single X 1))) Y'` is
  `γ l X Y' · Y.coef L (oY' + 2^k − 1)` if `oX ≤ oY' + 2^k − 1` (`L = oY' + 2^k − 1 − oX`) and `0`
  otherwise: by (F1), (F2) it is `Σ_{m < B} Y.coef m (floor of outIdx Y') · F^{(m)}(δ_{inIdx X})`
  read at `outIdx Y'`; by (W) of C18 and the floors (F4), (F5) only `m = L` can contribute, and
  `L < B` by (F6).
* `C109`: C40c (A1), (A2), (N2) make `sysAct (fun _ _ => Ξ)` a linear equivalence with inverse
  `sysAct (fun _ _ => Y)`; C41 (V5) then gives `IsUnit` and the inverse, whose entries are
  computed by `entry_sysAct`.
-/

@[expose] public section

noncomputable section

namespace InvFloors

open DPLattice Doubling Filt FormalOps FormalDance FormalAct InvBlock

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- (C109) of `C42_floors_and_corollary_10_9.md`, the entry computation (auxiliary, over any
`A`). -/
theorem entry_sysAct (l B : ℕ) (hB : l + 1 ≤ B) (Y : Bf A)
    (X Y' : Fin (Dance.slots (Families.ds l) 1)) :
    InvBlock.outH l 1 (sysAct (T A l) (l : ℤ) B (fun _ _ => Y)
        (InvBlock.inH l 1 (Pi.single X 1))) Y' =
      if Rulers.oE (Windows.Dset (Families.ds l) X) ≤
          Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 then
        gamma l X Y' * Y.coef (Rulers.oE (Windows.Dset (Families.ds l) Y') +
          2 ^ (Families.ds l).length - 1 - Rulers.oE (Windows.Dset (Families.ds l) X))
          ((Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 : ℕ) : ℤ)
      else 0 := by
  -- the floors of the two basis indices
  have h4 := F4 (A := A) l 1 X
  have h5 := F5 (A := A) l 1 Y'
  have h6 := F6 l 1 Y'
  set iX := inIdx (A := A) l 1 X with hiX
  set iY := outIdx (A := A) l 1 Y' with hiY
  set oX := Rulers.oE (Windows.Dset (Families.ds l) X) with hoX
  set oY := Rulers.oE (Windows.Dset (Families.ds l) Y') with hoY
  have hPz : (2 : ℤ) ^ (Families.ds l).length = ((2 ^ (Families.ds l).length : ℕ) : ℤ) := by
    push_cast; rfl
  have hP1 : 1 ≤ 2 ^ (Families.ds l).length := Nat.one_le_two_pow
  rw [hPz] at h5
  set P := 2 ^ (Families.ds l).length with hP
  have hs : slotOf l 1 Y' = slotOf l 1 X := Subsingleton.elim _ _
  have hfl : ((l : ℤ) - (T A l).wt iY) / 2 = ((oY + P - 1 : ℕ) : ℤ) := by
    rw [h5]
    have : ((oY + P - 1 : ℕ) : ℤ) = (oY : ℤ) + P - 1 := by omega
    rw [this]
    omega
  -- the value as a sum over `m < B`
  have hval : InvBlock.outH l 1 (sysAct (T A l) (l : ℤ) B (fun _ _ => Y)
      (InvBlock.inH l 1 (Pi.single X 1))) Y' =
      ∑ m ∈ Finset.range B, Y.coef m ((oY + P - 1 : ℕ) : ℤ) *
        (T A l).Fd m (Pi.single iX 1) iY := by
    rw [F1, F2, sysAct_apply, Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) (slotOf l 1 X),
      Pi.single_eq_same, act]
    rw [← hiX, ← hiY]
    simp only [LinearMap.coe_sum, Finset.sum_apply, Module.End.mul_apply, flD_apply]
    rw [hfl]
  -- the weight condition (W)
  have hW : ∀ m : ℕ, (T A l).Fd m (Pi.single iX 1) iY ≠ 0 → oY + P - 1 = oX + m := by
    intro m hm
    by_contra hne
    apply hm
    apply (T A l).isDP.W_F iX m iY
    intro heq
    apply hne
    omega
  rw [hval]
  split_ifs with hle
  · rw [Finset.sum_eq_single (oY + P - 1 - oX)]
    · rw [gamma, if_pos hle, F1, F2, hs, Pi.single_eq_same, ← hiX, ← hiY]
      ring
    · intro m _ hm
      by_cases h0 : (T A l).Fd m (Pi.single iX 1) iY = 0
      · rw [h0, mul_zero]
      · exact absurd (hW m h0) (by omega)
    · intro hnot
      exact absurd (Finset.mem_range.2 (by omega)) hnot
  · refine Finset.sum_eq_zero fun m _ => ?_
    by_cases h0 : (T A l).Fd m (Pi.single iX 1) iY = 0
    · rw [h0, mul_zero]
    · exact absurd (hW m h0) (by omega)


/-- Auxiliary for (C109) of `C42_floors_and_corollary_10_9.md`: on the single slot `Fin 1`, the
product of two constant systems is the constant system of the product. -/
lemma magree_const_mul {K : Type*} [CommRing K] {x y : Bf K} (h : Agree (x * y) 1)
    {G H : Matrix (Fin 1) (Fin 1) (Bf K)} (hG : ∀ s s', G s s' = x) (hH : ∀ s s', H s s' = y) :
    MAgree (G * H) 1 := by
  intro s s'
  obtain rfl : s = s' := Subsingleton.elim _ _
  rw [Matrix.one_apply_eq, Matrix.mul_apply, Fin.sum_univ_one, hG, hH]
  exact h

/-- **(C109) Corollary 10.9** of `C42_floors_and_corollary_10_9.md`. Let `K` be a field with
`[CharZero K] [OddUnits K]`, `l : ℕ`, `B ≥ l + 1`, `Ξ Y : Bf K` with `Agree (Ξ * Y) 1` and
`Agree (Y * Ξ) 1`, and `Gk` with `DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Gk`. Then
`IsUnit (finalM Gk).det`, and for all final slots `X Y'`, with `oX = oE (Dset ds X)`,
`oY' = oE (Dset ds Y')`, `k = ds.length` (`ds = Families.ds l`):
* if `oX ≤ oY' + 2^k − 1`:
  `(finalM Gk)⁻¹ Y' X = 2 ^ k * γ l X Y' * Y.coef (oY' + 2^k − 1 − oX) ((oY' + 2^k − 1 : ℕ) : ℤ)`;
* if `oX > oY' + 2^k − 1`: `(finalM Gk)⁻¹ Y' X = 0`.
(`γ l X Y'` is `gamma l X Y'`.) -/
theorem C109 {K : Type*} [Field K] [CharZero K] [OddUnits K] (l B : ℕ) (hB : l + 1 ≤ B)
    (Ξ Y : Bf K) (hΞY : Agree (Ξ * Y) 1) (hYΞ : Agree (Y * Ξ) 1)
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf K))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Gk) :
    IsUnit (finalM Gk).det ∧
      ∀ X Y' : Fin (Dance.slots (Families.ds l) 1),
        (Rulers.oE (Windows.Dset (Families.ds l) X) ≤
            Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 →
          (finalM Gk)⁻¹ Y' X = 2 ^ (Families.ds l).length * gamma l X Y' *
            Y.coef (Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 -
              Rulers.oE (Windows.Dset (Families.ds l) X))
              ((Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 :
                ℕ) : ℤ)) ∧
        (Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 <
            Rulers.oE (Windows.Dset (Families.ds l) X) →
          (finalM Gk)⁻¹ Y' X = 0) := by
  obtain ⟨htop, hnil⟩ := N2 (A := K) l
  have h1 : sysAct (T K l) (l : ℤ) B (fun _ _ => Ξ : Matrix (Fin 1) (Fin 1) (Bf K)) ∘ₗ
      sysAct (T K l) (l : ℤ) B (fun _ _ => Y) = LinearMap.id := by
    rw [← sysAct_mul hnil hB, A1 htop (magree_const_mul hΞY (fun _ _ => rfl) (fun _ _ => rfl)) B, sysAct_one (by omega)]
  have h2 : sysAct (T K l) (l : ℤ) B (fun _ _ => Y : Matrix (Fin 1) (Fin 1) (Bf K)) ∘ₗ
      sysAct (T K l) (l : ℤ) B (fun _ _ => Ξ) = LinearMap.id := by
    rw [← sysAct_mul hnil hB, A1 htop (magree_const_mul hYΞ (fun _ _ => rfl) (fun _ _ => rfl)) B, sysAct_one (by omega)]
  let e : (Fin 1 → (T K l).ι → K) ≃ₗ[K] (Fin 1 → (T K l).ι → K) := LinearEquiv.ofLinear _ _ h1 h2
  obtain ⟨hdet, hinv⟩ := V5 l 1 (fun _ _ => Ξ) Gk hG B hB e rfl
  refine ⟨hdet, fun X Y' => ?_⟩
  have key : (finalM Gk)⁻¹ Y' X = 2 ^ (Families.ds l).length *
      InvBlock.outH l 1 (sysAct (T K l) (l : ℤ) B (fun _ _ => Y)
        (InvBlock.inH l 1 (Pi.single X 1))) Y' := by
    have := congrFun (LinearMap.congr_fun hinv (Pi.single X 1)) Y'
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    rfl
  rw [key, entry_sysAct l B hB Y X Y']
  constructor
  · intro hle
    rw [if_pos hle, mul_assoc]
  · intro hlt
    rw [if_neg (by omega), mul_zero]

end InvFloors
