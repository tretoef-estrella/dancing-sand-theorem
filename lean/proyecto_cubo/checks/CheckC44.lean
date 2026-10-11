import RequestProject.Stability.All

/-! Auditor's check file for Lean piece C44, Lemma 10.11 (stability) and Theorem 10.12 first half
(rigidity, eta = 1) (Grepy Escribano, 9 Oct 2026). Restated by hand from
`C44_stability_and_rigidity.md`; then `#print axioms`. -/

open Matrix Finset FormalOps FormalDance Stability

-- the definitions, by `rfl`
example {n : Type} (B E : Matrix n n ℚ_[2]) (i j : n) : hadOne B E i j = B i j * (1 + E i j) := rfl
example {n : Type} (S : n → n → Prop) (ν : n → n → ℕ) (s : ℕ) (X : Matrix n n ℚ_[2]) :
    X ∈ Wt S ν s ↔ ∀ i j, (¬ S i j → X i j = 0) ∧
      ‖X i j‖ ≤ (2 : ℝ) ^ (-((ν i j + s : ℕ) : ℤ)) := Iff.rfl
example (ds : List Bool) (s s' : Fin (Dance.slots ds 1)) :
    nest ds s s' ↔ Windows.Dset ds s' ⊆ Windows.Dset ds s := Iff.rfl
example (ds : List Bool) (s s' : Fin (Dance.slots ds 1)) :
    Amat ds s s' = if Windows.Dset ds s' ⊆ Windows.Dset ds s then
      ((Deficit.a (Windows.Ids ds) ds.length (Windows.Dset ds s \ Windows.Dset ds s') : ℤ) : ℚ_[2])
      else 0 := rfl
example (ds : List Bool) (s s' : Fin (Dance.slots ds 1)) :
    nuA ds s s' = (Rulers.delta ds.length (Windows.Dset ds s \ Windows.Dset ds s')).toNat := rfl

section S
variable {n : Type} [Fintype n] [DecidableEq n] {S : n → n → Prop} {ν : n → n → ℕ}

-- (S1)
example (hrefl : ∀ i, S i i) (htrans : ∀ i u j, S i u → S u j → S i j)
    (hνd : ∀ i, ν i i = 0) (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j)
    (s : ℕ) (hs : 1 ≤ s) (A B E : Matrix n n ℚ_[2]) (hA : A ∈ Wt S ν 0)
    (hAn : ∀ i j, S i j → ‖A i j‖ = (2 : ℝ) ^ (-(ν i j : ℤ))) (hB : B ∈ Wt S ν 0)
    (hAB : A * B = 1) (hE : ∀ i j, ‖E i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ))) :
    IsUnit (hadOne B E).det ∧ ∃ E' : Matrix n n ℚ_[2], (hadOne B E)⁻¹ = hadOne A E' ∧
      ∀ i j, ‖E' i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ)) :=
  S1 hrefl htrans hνd htri hs hA hAn hB hAB hE

-- (S2)
example (hrefl : ∀ i, S i i) (htrans : ∀ i u j, S i u → S u j → S i j)
    (hνd : ∀ i, ν i i = 0) (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j)
    (s : ℕ) (hs : 1 ≤ s) (A B E : Matrix n n ℚ_[2]) (hA : A ∈ Wt S ν 0)
    (hAn : ∀ i j, S i j → ‖A i j‖ = (2 : ℝ) ^ (-(ν i j : ℤ))) (hB : B ∈ Wt S ν 0)
    (hAB : A * B = 1) (hE : ∀ i j, ‖E i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ)))
    (d₁ d₂ : n → ℚ_[2]) (hd₁ : ∀ i, d₁ i ≠ 0) (hd₂ : ∀ i, d₂ i ≠ 0) :
    IsUnit (diagonal d₁ * A * diagonal d₂).det ∧
      IsUnit (hadOne (diagonal d₁ * A * diagonal d₂)⁻¹ E).det ∧
      ∃ E' : Matrix n n ℚ_[2],
        (hadOne (diagonal d₁ * A * diagonal d₂)⁻¹ E)⁻¹ = hadOne (diagonal d₁ * A * diagonal d₂) E' ∧
        ∀ i j, ‖E' i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ)) :=
  S2 hrefl htrans hνd htri hs hA hAn hB hAB hE d₁ d₂ hd₁ hd₂
end S

-- (A2), (A3)
example (ds : List Bool) (hk : 1 ≤ ds.length) :
    (∀ s s', nest ds s s' → ‖Amat ds s s'‖ = (2 : ℝ) ^ (-(nuA ds s s' : ℤ))) ∧
    (∀ s, Amat ds s s = 1) := A2 hk
example (ds : List Bool) (hk : 1 ≤ ds.length) :
    Amat ds ∈ Wt (nest ds) (nuA ds) 0 ∧ ∃ B ∈ Wt (nest ds) (nuA ds) 0, Amat ds * B = 1 := A3 hk

-- (F1)
example (l α c : ℕ) (hα : 1 ≤ α)
    (GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GSig)
    (s s' : Fin (Dance.slots (Families.ds l) 1)) :
    finalM GSig s s' = if Windows.Dset (Families.ds l) s' ⊆ Windows.Dset (Families.ds l) s then
      ((Deficit.Mc (Windows.Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
        (Windows.Dset (Families.ds l) s) (Windows.Dset (Families.ds l) s') : ℚ) : ℚ_[2])
      else 0 := F1 hα GSig hG s s'

-- (T1), (T2)
example (l α c : ℕ) (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c)
    (ζ : ℕ → ℤ → ℚ_[2]) (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (B : ℕ) (hB : l + 1 ≤ B)
    (YX YS : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c 1 ζ * YX) 1) (h2 : Agree (YX * PathSum.XiOp α c 1 ζ) 1)
    (h3 : Agree (PathSum.SigOp α c 1 * YS) 1) (h4 : Agree (YS * PathSum.SigOp α c 1) 1)
    (GX GS : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGX : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c 1 ζ) GX)
    (hGS : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c 1) GS) :
    (IsUnit (finalM GX).det ∧ IsUnit (finalM GS).det ∧
      ∃ E' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
          ℚ_[2],
        finalM GX = hadOne (finalM GS) E' ∧
        ∀ s s', ‖E' s s'‖ ≤ (2 : ℝ) ^ (-((α : ℤ) - 1))) ∧
    (∀ s s', (finalM GX s s' = 0 ↔ finalM GS s s' = 0) ∧ ‖finalM GX s s'‖ = ‖finalM GS s s'‖) :=
  ⟨T1 hl hα hc hζ B hB YX YS h1 h2 h3 h4 GX GS hGX hGS,
   T2 hl hα hc hζ B hB YX YS h1 h2 h3 h4 GX GS hGX hGS⟩

#print axioms Stability.S0
#print axioms Stability.S1
#print axioms Stability.S2
#print axioms Stability.A1
#print axioms Stability.A2
#print axioms Stability.A3
#print axioms Stability.F1
#print axioms Stability.F2
#print axioms Stability.T1
#print axioms Stability.T2
