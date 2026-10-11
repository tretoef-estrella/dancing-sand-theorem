import RequestProject.BendCor.All

/-! Auditor's check file for Lean piece C50e: Corollary 10.21
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50e_corollary_10_21.md`;
then `#print axioms`. -/

open FormalOps FormalDance BendCor

-- the new definitions, by `rfl`
example (Ψ : Bf ℚ_[2]) (t : ℚ_[2]) :
    UOp Ψ t = (1 / 2 : ℚ_[2]) • (Ψ * (Ψ + t • (1 : Bf ℚ_[2]))) := rfl
example {R : Type*} [Ring R] {n : Type*} (X Y Z : Matrix n n R) (p p' : Fin 2 × n) :
    gS X Y Z p p' = if p.1 = 0 ∧ p'.1 = 0 then X p.2 p'.2
      else if p.1 = 1 ∧ p'.1 = 0 then Z p.2 p'.2
      else if p.1 = 1 ∧ p'.1 = 1 then Y p.2 p'.2 else 0 := rfl

-- (A0)
example (t : ℚ_[2]) :
    (∀ x : Bf ℚ_[2], (t • (1 : Bf ℚ_[2])) * x = x * (t • (1 : Bf ℚ_[2]))) ∧
      ∀ Ψ : Bf ℚ_[2], Ψ * (Ψ + t • (1 : Bf ℚ_[2])) = (Ψ + t • (1 : Bf ℚ_[2])) * Ψ := A0 t

-- (A1)
example (Ψ Y Yt : Bf ℚ_[2]) {t : ℚ_[2]} (ht : t ≠ 0) (h1 : Agree (Ψ * Y) 1)
    (h2 : Agree (Y * Ψ) 1) (h3 : Agree ((Ψ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (Ψ + t • (1 : Bf ℚ_[2]))) 1) :
    Agree (UOp Ψ t * ((2 / t) • (Y - Yt))) 1 ∧ Agree (((2 / t) • (Y - Yt)) * UOp Ψ t) 1 :=
  A1 Ψ Y Yt ht h1 h2 h3 h4

-- (A2), with no condition on B
example (l B : ℕ) (Y Y' : Bf ℚ_[2]) (a : ℚ_[2]) :
    Bend.Nmat l B (Y + Y') = Bend.Nmat l B Y + Bend.Nmat l B Y' ∧
      Bend.Nmat l B (Y - Y') = Bend.Nmat l B Y - Bend.Nmat l B Y' ∧
      Bend.Nmat l B (a • Y) = a • Bend.Nmat l B Y := A2 l B Y Y' a

-- (F1)
example {l B : ℕ} (hB : l + 1 ≤ B) (Ψ Y Yt : Bf ℚ_[2]) {t : ℚ_[2]} (ht : t ≠ 0)
    (h1 : Agree (Ψ * Y) 1) (h2 : Agree (Y * Ψ) 1)
    (h3 : Agree ((Ψ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (Ψ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => Ψ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ t) GU) :
    (finalM GU)⁻¹ = (2 / t) • ((finalM GΨ)⁻¹ - Bend.Nmat l B Yt) :=
  F1 hB Ψ Y Yt ht h1 h2 h3 h4 GΨ GU hGΨ hGU

-- (F2)
example {l B : ℕ} (hB : l + 1 ≤ B) (Ψ Y Yt : Bf ℚ_[2]) {t : ℚ_[2]} (ht : t ≠ 0)
    (h1 : Agree (Ψ * Y) 1) (h2 : Agree (Y * Ψ) 1)
    (h3 : Agree ((Ψ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (Ψ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => Ψ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp Ψ t) GU) :
    IsUnit (1 - finalM GΨ * Bend.Nmat l B Yt).det ∧
      finalM GU = ((t / 2) • (1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹) * finalM GΨ :=
  F2 hB Ψ Y Yt ht h1 h2 h3 h4 GΨ GU hGΨ hGU

-- (W1)
example {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℚ_[2])
    (hE : ∀ i j, ‖E i j‖ ≤ 1 / 2) :
    ‖(1 - E).det‖ = 1 ∧ (∀ i j, ‖(1 - E)⁻¹ i j - (1 : Matrix n n ℚ_[2]) i j‖ ≤ 1 / 2) ∧
      ∀ i j, ‖(1 - E)⁻¹ i j‖ ≤ 1 := W1 E hE

-- (W2) Corollary 10.21
example {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y Yt : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c η ζ * Y) 1) (h2 : Agree (Y * PathSum.XiOp α c η ζ) 1)
    (h3 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) t) GU) :
    let W := (t / 2) • (1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹
    finalM GU = W * finalM GΨ ∧
      (∀ s s', ‖W s s' - (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2) ∧
      (∀ s s', ‖W s s'‖ ≤ 1) ∧ ‖W.det‖ = 1 :=
  W2 hB hα hc hη hζ ht Y Yt h1 h2 h3 h4 GΨ GU hGΨ hGU

-- (W3)
example {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y Yt : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c η ζ * Y) 1) (h2 : Agree (Y * PathSum.XiOp α c η ζ) 1)
    (h3 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Yt) 1)
    (h4 : Agree (Yt * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΨ GU : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΨ)
    (hGU : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) t) GU) :
    let W := (t / 2) • (1 - finalM GΨ * Bend.Nmat l B Yt)⁻¹
    ∃ W' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        ℤ_[2],
      W'.map (fun z : ℤ_[2] => (z : ℚ_[2])) = W ∧ IsUnit W'.det ∧
        ∀ s s', ‖((W' s s' : ℤ_[2]) : ℚ_[2]) - (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
          (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2 :=
  W3 hB hα hc hη hζ ht Y Yt h1 h2 h3 h4 GΨ GU hGΨ hGU

-- (W4) both signs, as in the paper
example {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    (Y Yp Ym : Bf ℚ_[2])
    (h1 : Agree (PathSum.XiOp α c η ζ * Y) 1) (h2 : Agree (Y * PathSum.XiOp α c η ζ) 1)
    (hp1 : Agree ((PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Yp) 1)
    (hp2 : Agree (Yp * (PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (hm1 : Agree ((PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Ym) 1)
    (hm2 : Agree (Ym * (PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (GΨ GUp GUm : Matrix (Fin (Dance.slots (Families.ds l) 1))
      (Fin (Dance.slots (Families.ds l) 1)) (Bf ℚ_[2]))
    (hGΨ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΨ)
    (hGUp : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) 2) GUp)
    (hGUm : DanceRel (Families.ds l) 1 (fun _ _ => UOp (PathSum.XiOp α c η ζ) (-2)) GUm) :
    let Wp := (1 - finalM GΨ * Bend.Nmat l B Yp)⁻¹
    let Wm := -(1 - finalM GΨ * Bend.Nmat l B Ym)⁻¹
    finalM GUp = Wp * finalM GΨ ∧ finalM GUm = Wm * finalM GΨ ∧
      (∀ s s', ‖Wp s s' - (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2) ∧
      ∀ s s', ‖Wm s s' + (1 : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) ℚ_[2]) s s'‖ ≤ 1 / 2 :=
  W4 hB hα hc hη hζ Y Yp Ym h1 h2 hp1 hp2 hm1 hm2 GΨ GUp GUm hGΨ hGUp hGUm

-- (G1)–(G5)
example {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]
    (X Y Z X' Y' Z' : Matrix n n R) :
    gS X Y Z * gS X' Y' Z' = gS (X * X') (Y * Y') (Z * X' + Y * Z') := G1 X Y Z X' Y' Z'
example {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X Y Z : Matrix n n R) : (gS X Y Z).det = X.det * Y.det := G2 X Y Z
example {n : Type*} [Fintype n] [DecidableEq n] (X Y Z : Matrix n n ℤ_[2])
    (hX : IsUnit X.det) (hY : IsUnit Y.det) : IsUnit (gS X Y Z).det := G3 X Y Z hX hY
example {n : Type*} [Fintype n] [DecidableEq n] (X Y Z Wm Wp ZW : Matrix n n ℤ_[2])
    (hZ : 2 • Z = Y - X) (hZW : 2 • ZW = Wp - Wm) :
    ∃ Z₁ : Matrix n n ℤ_[2], gS Wm Wp ZW * gS X Y Z = gS (Wm * X) (Wp * Y) Z₁ ∧
      2 • Z₁ = Wp * Y - Wm * X := G4 X Y Z Wm Wp ZW hZ hZW
example {n : Type*} (Wp Wm : Matrix n n ℤ_[2])
    (h : ∀ s s', ‖(((Wp - Wm) s s' : ℤ_[2]) : ℚ_[2])‖ ≤ 1 / 2) :
    ∃ ZW : Matrix n n ℤ_[2], 2 • ZW = Wp - Wm := G5 Wp Wm h

#print axioms BendCor.A0
#print axioms BendCor.A1
#print axioms BendCor.A2
#print axioms BendCor.F1
#print axioms BendCor.F2
#print axioms BendCor.W1
#print axioms BendCor.W2
#print axioms BendCor.W3
#print axioms BendCor.W4
#print axioms BendCor.G1
#print axioms BendCor.G2
#print axioms BendCor.G3
#print axioms BendCor.G4
#print axioms BendCor.G5
