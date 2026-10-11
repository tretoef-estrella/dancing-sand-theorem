import RequestProject.PathSum.All

/-! Auditor's check file for Lean piece C43, Lemma 10.10 (the path sum) and the relation of the
final inverses (Grepy Escribano, 9 Oct 2026). Restated by hand from `C43_path_sum.md`; then
`#print axioms`. -/

open FormalOps FormalDance PathSum Finset

-- the definitions, by `rfl`
example (α c : ℕ) (d : ℤ) : piF α c d = 2 ^ α * ((d : ℚ_[2]) + c) := rfl
example (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) (f : ℤ) : (XiOp α c η ζ).coef 0 f = piF α c f := rfl
example (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) (f : ℤ) : (XiOp α c η ζ).coef 1 f = η := rfl
example (α c : ℕ) (η : ℚ_[2]) (ζ : ℕ → ℤ → ℚ_[2]) (m : ℕ) (hm : 2 ≤ m) (f : ℤ) :
    (XiOp α c η ζ).coef m f = ζ m f := XiOp_coef_ge_two α c η ζ hm f
example (α c : ℕ) (η : ℚ_[2]) : SigOp α c η = XiOp α c η (fun _ _ => 0) := rfl
example (α c : ℕ) (η : ℚ_[2]) (L : ℕ) (f : ℤ) :
    sL α c η L f = (-1) ^ L * (L.factorial : ℚ_[2]) * η ^ L /
      ∏ i ∈ range (L + 1), piF α c (f - i) := rfl

-- (P0)
example (x Y₁ Y₂ : Bf ℚ_[2]) (hx : ∀ f : ℤ, 0 ≤ f → x.coef 0 f ≠ 0)
    (h₁ : Agree (x * Y₁) 1) (h₂ : Agree (x * Y₂) 1) : Agree Y₁ Y₂ := P0 x Y₁ Y₂ hx h₁ h₂
-- (P1)
example (α c : ℕ) (hc : 1 ≤ c) (η : ℚ_[2]) (Y : Bf ℚ_[2]) (hY : Agree (SigOp α c η * Y) 1)
    (L : ℕ) (f : ℤ) (hf : (L : ℤ) ≤ f) : Y.coef L f = sL α c η L f := P1 hc η Y hY L f hf
-- (P2)
example (α c : ℕ) (hα : 2 ≤ α) (hc : 1 ≤ c) (η : ℚ_[2]) (hη : ‖η‖ = 1)
    (ζ : ℕ → ℤ → ℚ_[2]) (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (Y : Bf ℚ_[2])
    (hY : Agree (XiOp α c η ζ * Y) 1) (L : ℕ) (f : ℤ) (hf : (L : ℤ) ≤ f) :
    sL α c η L f ≠ 0 ∧ ∃ e : ℚ_[2], Y.coef L f = sL α c η L f * (1 + e) ∧
      ‖e‖ ≤ (2 : ℝ) ^ (-((α : ℤ) - 1)) := P2 hα hc hη hζ Y hY L f hf
-- (R)
example (α c : ℕ) (hα : 2 ≤ α) (hc : 1 ≤ c) (η : ℚ_[2]) (hη : ‖η‖ = 1)
    (ζ : ℕ → ℤ → ℚ_[2]) (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (l B : ℕ) (hB : l + 1 ≤ B)
    (YX YS : Bf ℚ_[2])
    (h1 : Agree (XiOp α c η ζ * YX) 1) (h2 : Agree (YX * XiOp α c η ζ) 1)
    (h3 : Agree (SigOp α c η * YS) 1) (h4 : Agree (YS * SigOp α c η) 1)
    (GX GS : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGX : DanceRel (Families.ds l) 1 (fun _ _ => XiOp α c η ζ) GX)
    (hGS : DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GS)
    (X Y' : Fin (Dance.slots (Families.ds l) 1)) :
    ((finalM GS)⁻¹ Y' X = 0 → (finalM GX)⁻¹ Y' X = 0) ∧
      ((finalM GS)⁻¹ Y' X ≠ 0 → ∃ e : ℚ_[2],
        (finalM GX)⁻¹ Y' X = (finalM GS)⁻¹ Y' X * (1 + e) ∧
          ‖e‖ ≤ (2 : ℝ) ^ (-((α : ℤ) - 1))) :=
  R hα hc hη hζ l B hB YX YS h1 h2 h3 h4 GX GS hGX hGS X Y'

#print axioms PathSum.instOddUnitsPadicTwo
#print axioms PathSum.P0
#print axioms PathSum.P1
#print axioms PathSum.P2
#print axioms PathSum.R
