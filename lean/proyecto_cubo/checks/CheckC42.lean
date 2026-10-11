import RequestProject.InvFloors.All

/-! Auditor's check file for Lean piece C42, the floors of inH, outH and Corollary 10.9 (Grepy
Escribano, 9 Oct 2026). Restated by hand from `C42_floors_and_corollary_10_9.md`; then
`#print axioms`. -/

open DPLattice Doubling Filt FormalOps FormalDance FormalAct InvBlock InvFloors
open scoped Pointwise

section main
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

-- the constants of the word, by `rfl`
example (l : ℕ) (X Y : Fin (Dance.slots (Families.ds l) 1)) :
    gamma (A := A) l X Y =
      if Rulers.oE (Windows.Dset (Families.ds l) X) ≤
          Rulers.oE (Windows.Dset (Families.ds l) Y) + 2 ^ (Families.ds l).length - 1 then
        InvBlock.outH l 1 (fun s => (T A l).Fd
          (Rulers.oE (Windows.Dset (Families.ds l) Y) + 2 ^ (Families.ds l).length - 1 -
            Rulers.oE (Windows.Dset (Families.ds l) X))
          (InvBlock.inH l 1 (Pi.single X 1) s)) Y
      else 0 := rfl

-- (F1)
example (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    InvBlock.inH (A := A) l r (Pi.single j 1) =
      Pi.single (slotOf l r j) (Pi.single (inIdx l r j) 1) := F1 l r j
-- (F2)
example (l r : ℕ) (w : Fin r → (T A l).ι → A) (j : Fin (Dance.slots (Families.ds l) r)) :
    InvBlock.outH l r w j = w (slotOf l r j) (outIdx l r j) := F2 l r w j
-- (F3)
example (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    ((slotOf l r j : Fin r) : ℕ) = (j : ℕ) / 2 ^ Dance.mCount (Families.ds l) := F3 l r j
-- (F4)
example (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    (l : ℤ) - (T A l).wt (inIdx l r j) =
      2 * (Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) := F4 l r j
-- (F5)
example (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    (l : ℤ) - (T A l).wt (outIdx l r j) =
      2 * ((Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) + 2 ^ (Families.ds l).length - 1) :=
  F5 l r j
end main

-- (F6)
example (l r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)) :
    Rulers.oE (Windows.Dset (Families.ds l) j) + 2 ^ (Families.ds l).length - 1 ≤ l := F6 l r j

-- (C109)
example {K : Type} [Field K] [CharZero K] [OddUnits K] (l B : ℕ) (hB : l + 1 ≤ B)
    (Ξ Y : Bf K) (hΞY : Agree (Ξ * Y) 1) (hYΞ : Agree (Y * Ξ) 1)
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1)) (Bf K))
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
          (finalM Gk)⁻¹ Y' X = 0) :=
  C109 l B hB Ξ Y hΞY hYΞ Gk hG

#print axioms InvFloors.F1
#print axioms InvFloors.F2
#print axioms InvFloors.F3
#print axioms InvFloors.F4
#print axioms InvFloors.F5
#print axioms InvFloors.F6
#print axioms InvFloors.C109
