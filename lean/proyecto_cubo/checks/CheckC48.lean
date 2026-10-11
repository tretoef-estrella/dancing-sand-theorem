import RequestProject.Cleanliness.All

/-! Auditor's check file for Lean piece C48: cleanliness, one move of the dance keeps the class
(Grepy Escribano, 9 Oct 2026). Restated by hand from `C48_cleanliness_one_move.md`; then
`#print axioms`. -/

open RingK FormalOps FormalDance Doubling Finset Cleanliness

-- the definitions, by `rfl`
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : PayA Γ = ∀ y, ∃ z, Γ ∅ 0 y = 4 * z := rfl
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : CoefB Γ = ∀ y, IsUnit (Γ ∅ 1 y) := rfl
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Good Γ = (InK Γ ∧ PayA Γ ∧ CoefB Γ) := rfl
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (q : ℕ) (y : ℤ_[2]) :
    GB Γ Δ q y = dfi q * Γ Δ (2 * q) y := rfl
example (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (q : ℕ) (y : ℤ_[2]) :
    GC h Γ Δ q y = dfi q * Γ Δ (2 * q) (y + 2 ^ h) := rfl
example (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (q : ℕ) (y : ℤ_[2]) :
    GP h Γ Δ q y = dfi (q + 1) * Γ Δ (2 * q + 1) (y + 2 ^ h) := rfl
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (y : ℤ_[2]) : GD Γ Δ 0 y = 0 := rfl
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (q : ℕ) (y : ℤ_[2]) :
    GD Γ Δ (q + 1) y = ((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1) * Γ Δ (2 * q + 1) y := rfl
example (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    vsplitG h Γ Δ m y = if h ∈ Δ then Γ (Δ.erase h) (m + 1) y else Γ Δ m y := rfl
example (α : ℕ) (η : ℤ_[2]) (z : ℕ → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    G0 α η z Δ m y = if Δ = ∅ then (if m = 0 then 2 ^ α * y else if m = 1 then η else z m)
      else 0 := rfl

-- (W5): the twist move keeps the class, with the exact new payment
example (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hG : Good Γ) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') ∧
      ∀ y, 2 * Γ' ∅ 0 y = -(Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * Γ ∅ 0 (y + 2 ^ h)) ∧
        ∃ z, Γ' ∅ 0 y = 8 * z :=
  W5 P h c Γ hG

-- (V3): the split move keeps the class
example (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hP : h ∉ P)
    (hG : Good Γ) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      CleanStep (vsplit (covSys P h c Γ))
        (fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q')) :=
  V3 P h c Γ hP hG

-- (O1), (O2): level 0 is good and is XiOpZ
example (α : ℕ) (η : ℤ_[2]) (hα : 2 ≤ α) (hη : IsUnit η) (z : ℕ → ℤ_[2]) : Good (G0 α η z) :=
  O1 α η hα hη z
example (α c : ℕ) (η : ℤ_[2]) (z : ℕ → ℤ_[2]) :
    covSys ∅ 0 (c : ℤ_[2]) (G0 α η z) ⟨∅, Finset.empty_subset _⟩ ⟨∅, Finset.empty_subset _⟩ =
      Smith2.XiOpZ α c η (fun m _ => z m) :=
  O2 α c η z

-- (L1): reindexing over any commutative ring
example {A : Type} [CommRing A] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G G' : Matrix n' n' (Bf A)) (hC : CleanStep G G') :
    CleanStep (fun j j' => G (e j) (e j')) (fun j j' => G' (e j) (e j')) :=
  L1 e G G' hC

#print axioms Cleanliness.W1
#print axioms Cleanliness.W2
#print axioms Cleanliness.W3
#print axioms Cleanliness.W4
#print axioms Cleanliness.W5
#print axioms Cleanliness.V0
#print axioms Cleanliness.V1
#print axioms Cleanliness.V2
#print axioms Cleanliness.V3
#print axioms Cleanliness.L1
#print axioms Cleanliness.O1
#print axioms Cleanliness.O2
