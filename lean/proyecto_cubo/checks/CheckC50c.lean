import RequestProject.ArmsEven.All

/-! Auditor's check file for Lean piece C50c: the arms of the even families
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50c_the_arms_of_the_even_families.md`;
then `#print axioms`. -/

open Finset RingK Cleanliness FoldOdd FormalOps DanceMod2 ArmsEven

-- the new definitions, by `rfl`
example (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    uSys Δ m y = if Δ = ∅ ∧ m = 0 then 1 else 0 := rfl
example (i : ℕ) : eI i = (i + 2) / 2 - (i + 1) / 2 := rfl
example (e j : ℕ) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    GPsi e j Δ m y = if Δ = ∅ then (if m = 0 then 4 * (y + (e : ℤ_[2])) else kJ j m) else 0 := rfl
example : eI 0 = 1 ∧ eI 1 = 0 ∧ eI 6 = 1 ∧ eI 7 = 0 := by decide

-- (P1)
example (c e j : ℕ) :
    covSys ∅ 0 (c : ℤ_[2]) (GPsi e j) ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ =
      Smith2.XiOpZ 2 (c + e) (kJ j 1) (fun m _ => kJ j m) := P1 c e j

-- (P2)
example (i : ℕ) :
    covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) (GPsi 0 i) ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ = PsiF i ∧
    covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) (GPsi (eI i) (i + 1)) ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ = PsiF (i + 1) := P2 i

-- (P3)
example (e j : ℕ) : Good (GPsi e j) := P3 e j

-- (A1)
example (i : ℕ) : Cong2 (GPsi (eI i) (i + 1)) (GPsi 0 i) := A1 i

-- (H1)
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (h : ℕ) (ε : ℤ_[2])
    (hε : ε = 1 ∨ ε = -1) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      ∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y := H1 Γ hΓ h ε hε

-- (H2)
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (h : ℕ) (ε : ℤ_[2])
    (hε : ε = 1 ∨ ε = -1) (Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hΓ' : ∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y)
    (P : Finset ℕ) (c : ℤ_[2]) :
    (2 : ℤ_[2]) • covSys P h c Γ' =
      covSys P h c Γ * (covSys P h c Γ + (2 * ε) • (1 : Matrix (Dn P) (Dn P) (Bf ℤ_[2]))) :=
  H2 Γ hΓ h ε hε Γ' hΓ' P c

-- (C1)
example (Γ₀ Γ₁ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (h₀ : InK Γ₀) (h₁ : InK Γ₁)
    (hc : Cong2 Γ₁ Γ₀) (h : ℕ) (U U' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hU : ∀ Δ m y, 2 * U Δ m y = prodFun h Γ₁ (Γ₁ + (-2 : ℤ_[2]) • uSys) Δ m y)
    (hU' : ∀ Δ m y, 2 * U' Δ m y = prodFun h Γ₀ (Γ₀ + (2 : ℤ_[2]) • uSys) Δ m y) :
    Cong2 U U' := C1 Γ₀ Γ₁ h₀ h₁ hc h U U' hU hU'

-- (E1)
example (i : ℕ) :
    ∃ U U' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good U ∧ Good U' ∧
      Cong2 (GPsi (eI i) (i + 1)) (GPsi 0 i) ∧ Cong2 U U' ∧
      (∀ Δ m y, 2 * U Δ m y = prodFun 0 (GPsi (eI i) (i + 1))
        (GPsi (eI i) (i + 1) + (-2 : ℤ_[2]) • uSys) Δ m y) ∧
      (∀ Δ m y, 2 * U' Δ m y = prodFun 0 (GPsi 0 i) (GPsi 0 i + (2 : ℤ_[2]) • uSys) Δ m y) ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF (i + 1) * (PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U' ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF i * (PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) := E1 i

-- (E2)
example (i : ℕ) (ds : List Bool) :
    ∃ U U' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good U ∧ Good U' ∧ Cong2 U U' ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF (i + 1) * (PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (2 : ℤ_[2]) • covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U' ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩ =
        PsiF i * (PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (∃ Xk Yk, GlueDance.PairRel ds 1 (fun _ _ => PsiF (i + 1)) (fun _ _ => PsiF i) Xk Yk) ∧
      ∃ Uk U'k, GlueDance.PairRel ds 1
        (fun _ _ => covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩)
        (fun _ _ => covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U' ⟨∅, Finset.empty_subset _⟩
          ⟨∅, Finset.empty_subset _⟩) Uk U'k := E2 i ds

#print axioms ArmsEven.P1
#print axioms ArmsEven.P2
#print axioms ArmsEven.P3
#print axioms ArmsEven.A1
#print axioms ArmsEven.H1
#print axioms ArmsEven.H2
#print axioms ArmsEven.C1
#print axioms ArmsEven.E1
#print axioms ArmsEven.E2
