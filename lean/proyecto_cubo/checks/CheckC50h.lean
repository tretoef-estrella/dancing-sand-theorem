import RequestProject.EvenZero.All
import RequestProject.EvenFold.All

/-! Auditor's check file for Lean piece C50h: Theorem 10.22 at `i = 0`, and for every `i`
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50h_theorem_10_22_at_zero.md`;
then `#print axioms`. -/

open FormalOps FormalDance EvenZero

-- the new definition, by rfl
example (c : ℕ) :
    PsiC c = Smith2.XiOpZ 2 c (FoldOdd.kJ 0 1) (fun m _ => FoldOdd.kJ 0 m) := rfl

-- (M0)
example : PsiC 0 = FoldOdd.PsiF 0 ∧ IsUnit (FoldOdd.kJ 0 1) := M0

-- (M1′) one arm, any shift c ≥ 1
example (l c : ℕ) (hc : 1 ≤ c) (η : ℤ_[2]) (hηu : IsUnit η) (z : ℕ → ℤ_[2]) (t : ℤ_[2])
    (ht : t = 2 ∨ t = -2) (V : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = Smith2.XiOpZ 2 c η (fun m _ => z m) *
      (Smith2.XiOpZ 2 c η (fun m _ => z m) + t • (1 : Bf ℤ_[2])))
    (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hXk : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ 2 c η (fun m _ => z m)) Xk)
    (hVk : DanceRel (Families.ds l) 1 (fun _ _ => V) Vk) :
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit W'.det ∧ (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
        finalM Vk = W' * finalM Xk :=
  M1' l c hc η hηu z t ht V hV Xk Vk hXk hVk

-- (K1)
example (n : ℕ) :
    ContZero.MCong (n + 2) (fun _ _ : Fin 1 => PsiC (2 ^ n)) (fun _ _ : Fin 1 => PsiC 0) :=
  K1 n

-- (K2)
example (n : ℕ) (V V₀ : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hV₀ : (2 : ℤ_[2]) • V₀ = PsiC 0 * (PsiC 0 + (2 : ℤ_[2]) • (1 : Bf ℤ_[2]))) :
    ContZero.MCong (n + 1) (fun _ _ : Fin 1 => V) (fun _ _ : Fin 1 => V₀) :=
  K2 n V V₀ hV hV₀

-- (K3) the approximants exist
example (l n : ℕ) :
    ∃ (V : Bf ℤ_[2]) (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) (Bf ℤ_[2])),
      (2 : ℤ_[2]) • V = PsiC (2 ^ n) * (PsiC (2 ^ n) + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      DanceRel (Families.ds l) 1 (fun _ _ => PsiC (2 ^ n)) Xk ∧
      DanceRel (Families.ds l) 1 (fun _ _ => V) Vk := K3 l n

-- (L) the singular arm U′ at i = 0
example (l : ℕ) (V : Bf ℤ_[2])
    (hV : (2 : ℤ_[2]) • V = FoldOdd.PsiF 0 * (FoldOdd.PsiF 0 + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (Xk Vk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hXk : DanceRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF 0) Xk)
    (hVk : DanceRel (Families.ds l) 1 (fun _ _ => V) Vk) :
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      IsUnit W'.det ∧ (∀ s s', ‖(((W' - 1) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) ∧
        finalM Vk = W' * finalM Xk := L l V hV Xk Vk hXk hVk

-- (T0) i = 0
example (l : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) 0 ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 0)) := T0 l

-- (TT) Theorem 10.22, every i
example (l i : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i)) := TT l i

-- consistency: TT restricted to i ≥ 1 is C50g's T
example (l i : ℕ) (hi : 1 ≤ i) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i)) := EvenFold.T l i hi

#print axioms EvenZero.M0
#print axioms EvenZero.M1'
#print axioms EvenZero.K1
#print axioms EvenZero.K2
#print axioms EvenZero.K3
#print axioms EvenZero.L
#print axioms EvenZero.T0
#print axioms EvenZero.TT
