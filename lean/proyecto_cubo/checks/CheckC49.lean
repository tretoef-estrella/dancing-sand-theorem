import RequestProject.FoldOdd.All

/-! Auditor's check file for Lean piece C49: the fold law on the odd families, Corollary 10.17
for j ≥ 1 and for l = 0 (Grepy Escribano, 10 Oct 2026). Restated by hand from
`C49_the_fold_law_on_the_odd_families.md`; then `#print axioms`. -/

open FormalOps Doubling Finset FoldOdd

-- the definitions, by `rfl`
example {A : Type} [CommRing A] (a : ℕ → A) (m : ℕ) (f : ℤ) : (cst a).coef m f = a m := rfl
example (j : ℕ) : PsiF j = Bf.dg (fun f => 4 * (f : ℤ_[2]) + 2 * (j : ℤ_[2])) + KF j := rfl
example (c : ℕ) : SigF c = Bf.dg (fun f => 4 * ((f : ℤ_[2]) + c)) + Bf.fd 1 := rfl
example (j : ℕ) : KF j = (ChF - ((-1 : ℤ_[2]) ^ j) • (1 : Bf ℤ_[2])) * ShInvF := rfl
example (j m : ℕ) : kJ j m = (KF j).coef m 0 := rfl
example {A : Type} [CommRing A] : (ShF : Bf A) = cst (fun m => dfi (m + 1)) := rfl
example {A : Type} [CommRing A] : (ChF : Bf A) = cst (fun m => dfi m) := rfl
example {A : Type} [CommRing A] (m : ℕ) (hm : 1 ≤ m) :
    shInvC (A := A) m = -∑ b ∈ range m, (m.choose b : A) * shC (m - b) * shInvC b :=
  shInvC_eq m hm

-- (F2): Sh is a unit
example {A : Type} [CommRing A] : (ShF : Bf A) * ShInvF = 1 ∧ (ShInvF : Bf A) * ShF = 1 := F2

-- (F4): the formal operators act on T(l) as C39 Psi and C39b SigmaOp
example (l j c B : ℕ) (hB : l + 1 ≤ B) :
    act (Filt.T ℤ_[2] l) (l : ℤ) B (PsiF j) =
        FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1) ∧
      act (Filt.T ℤ_[2] l) (l : ℤ) B (SigF c) =
        FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (c : ℤ)) := F4 l j c B hB

-- (F5): both are of the form Ξ
example (j c : ℕ) :
    (PsiF j = Smith2.XiOpZ 2 ((j + 1) / 2) (kJ j 1) (fun m _ => kJ j m) ∧
      IsUnit (kJ j 1) ∧ (Even j → kJ j 1 = 1) ∧ (Odd j → 3 * kJ j 1 = 1)) ∧
    SigF c = Smith2.XiOpZ 2 c 1 (fun _ _ => 0) := F5 j c

-- (C1)
example (l j : ℕ) (h : 1 ≤ j ∨ l = 0) :
    Nonempty ((((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FoldHalf.Psi (Filt.T ℤ_[2] l) ((l : ℤ) + j) (l + 1))) ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range
        (FoldCube.SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ))))) :=
  C1 l j h

-- (C2): Corollary 10.17 for j ≥ 1
example (l j : ℕ) (hj : 1 ≤ j) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)) := C2 l j hj

-- (C3): Corollary 10.17 for l = 0
example (j : ℕ) :
    Nonempty (FoldGroup.XbarFam 1 j ≃+ FoldGroup.twoM (FamilyGroup.X (Families.ds 1) 1 j)) :=
  C3 j

#print axioms FoldOdd.F1
#print axioms FoldOdd.F2
#print axioms FoldOdd.F3
#print axioms FoldOdd.F4
#print axioms FoldOdd.F5
#print axioms FoldOdd.F6
#print axioms FoldOdd.C1
#print axioms FoldOdd.C2
#print axioms FoldOdd.C3
