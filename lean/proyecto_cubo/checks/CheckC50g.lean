import RequestProject.EvenFold.All
import RequestProject.ZeroSmith.All

/-! Auditor's check file for Lean piece C50g: Theorem 10.22 for `i ≥ 1`
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50g_theorem_10_22_for_i_positive.md`;
then `#print axioms`. -/

open FormalOps FormalDance EvenFold

-- (P0)
example (j : ℕ) :
    Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) (FoldOdd.PsiF j) =
      PathSum.XiOp 2 ((j + 1) / 2) ((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2])
        (fun m _ => ((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2])) ∧
    ‖((FoldOdd.kJ j 1 : ℤ_[2]) : ℚ_[2])‖ = 1 ∧
    ∀ m, ‖((FoldOdd.kJ j m : ℤ_[2]) : ℚ_[2])‖ ≤ 1 := P0 j

-- (P1)
example (X V : Bf ℤ_[2]) (t : ℤ_[2])
    (h : (2 : ℤ_[2]) • V = X * (X + t • (1 : Bf ℤ_[2]))) :
    Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) V =
      BendCor.UOp (Smith2.Bf.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) X)
        ((t : ℤ_[2]) : ℚ_[2]) := P1 X V t h

-- (M1) one arm
example (l j : ℕ) (hj : 1 ≤ j) (t : ℤ_[2]) (ht : t = 2 ∨ t = -2) (V : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = FoldOdd.PsiF j * (FoldOdd.PsiF j + t • (1 : Bf ℤ_[2])))
    (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hXk : DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF j) Xk)
    (hVk : DanceRel (Families.ds l) 1 (fun _ _ => V) Vk) :
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit W'.det ∧ (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
        finalM Vk = W' * finalM Xk := M1 l j hj t ht V hV Xk Vk hXk hVk

-- (M2) the glue
example (h21 : (2 : ℕ) = 2 * 1) (l : ℕ)
    (Xk Yk Zk Uk U'k ZUk : Matrix (Fin (Dance.slots (Families.ds l) 1))
      (Fin (Dance.slots (Families.ds l) 1)) (Bf ℤ_[2]))
    (hZ : MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)) (hZU : MAgree (U'k - Uk) ((2 : ℤ_[2]) • ZUk))
    (Wm Wp : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      ℤ_[2])
    (hWm : IsUnit Wm.det) (hWp : IsUnit Wp.det)
    (hWm1 : ∀ s s', ‖(((Wm - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2)
    (hWp1 : ∀ s s', ‖(((Wp - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2)
    (hU : finalM Uk = Wm * finalM Xk) (hU' : finalM U'k = Wp * finalM Yk) :
    ∃ P : Matrix (Fin (Dance.slots (Families.ds l) 2)) (Fin (Dance.slots (Families.ds l) 2))
        ℤ_[2],
      IsUnit P.det ∧
        finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Uk U'k ZUk) =
          P * finalM (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk) :=
  M2 h21 l Xk Yk Zk Uk U'k ZUk hZ hZU Wm Wp hWm hWp hWm1 hWp1 hU hU'

-- (A) associates
example {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M P : Matrix n n R) (hP : IsUnit P.det) (c : R) :
    Nonempty (((n → R) ⧸ LinearMap.range (c • Matrix.mulVecLin (P * M))) ≃ₗ[R]
      ((n → R) ⧸ LinearMap.range (c • Matrix.mulVecLin M))) := A M P hP c

-- (T) Theorem 10.22 for i ≥ 1 (same form as ZeroSmith.C5 for the odd families)
example (l i : ℕ) (hi : 1 ≤ i) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i)) := T l i hi

-- the odd families, for comparison of the form
example (l j : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j)) := ZeroSmith.C5 l j

#print axioms EvenFold.P0
#print axioms EvenFold.P1
#print axioms EvenFold.M1
#print axioms EvenFold.M2
#print axioms EvenFold.A
#print axioms EvenFold.T
