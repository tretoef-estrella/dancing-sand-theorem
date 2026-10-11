module

public import RequestProject.InvFloors.PartF

/-!
# `C42_floors_and_corollary_10_9.md`: (F1)–(F6) and Corollary 10.9 (C109)

* (F1)–(F6): `F1`, …, `F6`, from the inductions of `PartF.lean`.
* The constants of the word: `gamma l X Y` (written `γ l X Y` in the file).
* (C109) `C109`: the action `sysAct (fun _ _ => Ξ)` is a linear equivalence with inverse
  `sysAct (fun _ _ => Y)` (C40c (A1), (A2), (N2)); C41 (V5) gives `IsUnit` and
  `M⁻¹ = 2^k outH ∘ sysAct Y ∘ inH`; by (F1), (F2) the entry `(Y', X)` is
  `Σ_{m < B} Y.coef m (floor of outIdx Y') · F^{(m)}(δ_{inIdx X})_{outIdx Y'}`, and by (W) and
  (F4), (F5), (F6) only `m = oY' + 2^k − 1 − oX` survives, and none if `oX > oY' + 2^k − 1`.
-/

@[expose] public section

noncomputable section

namespace InvFloors

open DPLattice Doubling Filt FormalOps FormalDance FormalAct InvBlock

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- **(F1)** of `C42_floors_and_corollary_10_9.md` (`inH` is a basis injection): for every `j`,
`InvBlock.inH l r (Pi.single j 1) = Pi.single (slotOf l r j) (Pi.single (inIdx l r j) 1)`. -/
theorem F1 (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    InvBlock.inH (A := A) l r (Pi.single j 1) =
      Pi.single (slotOf l r j) (Pi.single (inIdx l r j) 1) :=
  F1_aux l r j

/-- **(F2)** of `C42_floors_and_corollary_10_9.md` (`outH` is a basis reading): for every `w`
and `j`, `InvBlock.outH l r w j = w (slotOf l r j) (outIdx l r j)`. -/
theorem F2 (l r : ℕ) (w : Fin r → (T A l).ι → A) (j : Fin (Dance.slots (Families.ds l) r)) :
    InvBlock.outH l r w j = w (slotOf l r j) (outIdx l r j) :=
  F2_aux l r w j

/-- **(F3)** of `C42_floors_and_corollary_10_9.md` (the slot):
`((slotOf l r j : Fin r) : ℕ) = (j : ℕ) / 2 ^ m`, `m = Dance.mCount (Families.ds l)`. -/
theorem F3 (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    ((slotOf l r j : Fin r) : ℕ) = (j : ℕ) / 2 ^ Dance.mCount (Families.ds l) :=
  F3_aux l r j

/-- **(F4)** of `C42_floors_and_corollary_10_9.md` (the coordinate floor):
`(l : ℤ) − (T A l).wt (inIdx l r j) = 2 * (Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ)`. -/
theorem F4 (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    (l : ℤ) - (T A l).wt (inIdx l r j) =
      2 * (Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) := by
  have := floor_ioIdx (A := A) 0 l r j
  simpa using this

/-- **(F5)** of `C42_floors_and_corollary_10_9.md` (the source floor):
`(l : ℤ) − (T A l).wt (outIdx l r j) =
2 * ((Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) + 2 ^ k − 1)`, `k = (Families.ds l).length`. -/
theorem F5 (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    (l : ℤ) - (T A l).wt (outIdx l r j) =
      2 * ((Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) + 2 ^ (Families.ds l).length - 1) := by
  have := floor_ioIdx (A := A) 1 l r j
  rw [outIdx, this]
  simp only [Fin.isValue, Fin.val_one, Nat.cast_one, one_mul]
  ring

/-- **(F6)** of `C42_floors_and_corollary_10_9.md` (the word bound):
`Rulers.oE (Windows.Dset (Families.ds l) j) + 2 ^ k − 1 ≤ l`, `k = (Families.ds l).length`
(it holds for every natural number in place of `j`, `F6_nat`). -/
theorem F6 (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    Rulers.oE (Windows.Dset (Families.ds l) j) + 2 ^ (Families.ds l).length - 1 ≤ l :=
  F6_nat l j

/-- **The constants of the word** (`C42_floors_and_corollary_10_9.md`, before (C109)), written
`γ l X Y` in the file: with `oX = oE (Dset ds X)`, `oY = oE (Dset ds Y)`, `k = ds.length`
(`ds = Families.ds l`), if `oX ≤ oY + 2^k − 1` and `L = oY + 2^k − 1 − oX`,
`γ l X Y = InvBlock.outH l 1 (fun s => (T A l).Fd L (InvBlock.inH l 1 (Pi.single X 1) s)) Y`
(`F^{(L)}` applied to the coordinate vector of `X`, read at the source `Y`), and `γ l X Y = 0` if
`oX > oY + 2^k − 1`. It depends only on `l` (and the ring `A`). -/
def gamma (l : ℕ) (X Y : Fin (Dance.slots (Families.ds l) 1)) : A :=
  if Rulers.oE (Windows.Dset (Families.ds l) X) ≤
      Rulers.oE (Windows.Dset (Families.ds l) Y) + 2 ^ (Families.ds l).length - 1 then
    InvBlock.outH l 1 (fun s => (T A l).Fd
      (Rulers.oE (Windows.Dset (Families.ds l) Y) + 2 ^ (Families.ds l).length - 1 -
        Rulers.oE (Windows.Dset (Families.ds l) X))
      (InvBlock.inH l 1 (Pi.single X 1) s)) Y
  else 0

end InvFloors
