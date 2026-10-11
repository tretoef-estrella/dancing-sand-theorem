import RequestProject.Bend.All

/-! Auditor's check file for Lean piece C50d: Lemma 10.20, the bend
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50d_the_bend.md`;
then `#print axioms`. -/

open FormalOps FormalDance FormalAct Filt Bend

-- the new definition, by `rfl`
example (l B : ℕ) (Y : Bf ℚ_[2]) (Y' X : Fin (Dance.slots (Families.ds l) 1)) :
    Nmat l B Y Y' X = 2 ^ (Families.ds l).length *
      InvBlock.outH l 1 (sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y)
        (InvBlock.inH l 1 (Pi.single X 1))) Y' := rfl

-- (N0)
example (l B : ℕ) (hB : l + 1 ≤ B) (x Y : Bf ℚ_[2]) (hxY : Agree (x * Y) 1)
    (hYx : Agree (Y * x) 1) :
    sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => x : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) ∘ₗ
        sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) = LinearMap.id ∧
      sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) ∘ₗ
        sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => x) = LinearMap.id := N0 l B hB x Y hxY hYx

-- (N1)
example (l B : ℕ) (Y : Bf ℚ_[2]) :
    Matrix.mulVecLin (Nmat l B Y) = (2 : ℚ_[2]) ^ (Families.ds l).length •
      (InvBlock.outH l 1 ∘ₗ sysAct (T ℚ_[2] l) (l : ℤ) B (fun _ _ => Y) ∘ₗ
        InvBlock.inH l 1) := N1 l B Y

-- (N2)
example (l B : ℕ) (hB : l + 1 ≤ B) (Y : Bf ℚ_[2])
    (X Y' : Fin (Dance.slots (Families.ds l) 1)) :
    Nmat l B Y Y' X =
      if Rulers.oE (Windows.Dset (Families.ds l) X) ≤
          Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 then
        2 ^ (Families.ds l).length * InvFloors.gamma l X Y' *
          Y.coef (Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 -
            Rulers.oE (Windows.Dset (Families.ds l) X))
            ((Rulers.oE (Windows.Dset (Families.ds l) Y') + 2 ^ (Families.ds l).length - 1 :
              ℕ) : ℤ)
      else 0 := N2 l B hB Y X Y'

-- (Y0)
example {α c : ℕ} (hα : 2 ≤ α) {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]}
    (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) :
    (∀ f : ℤ, ‖PathSum.piF α c f + t‖ = 1 / 2) ∧
      (∀ f : ℤ, (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])).coef 0 f = PathSum.piF α c f + t) ∧
      ∃ Y : Bf ℚ_[2], Agree ((PathSum.XiOp α c η ζ + t • 1) * Y) 1 ∧
        Agree (Y * (PathSum.XiOp α c η ζ + t • 1)) 1 := Y0 hα hη hζ ht

-- (Y1)
example {α c : ℕ} (hα : 2 ≤ α) {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]}
    (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y : Bf ℚ_[2])
    (hY : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Y) 1) :
    ∀ L : ℕ, ∀ f : ℤ, (L : ℤ) ≤ f →
      ‖Y.coef L f‖ ≤ ‖((L.factorial : ℕ) : ℚ_[2])‖ * 2 ^ (L + 1) :=
  Y1 hα hη hζ ht Y hY

-- (W)
example (ds : List Bool) (s s' : Fin (Dance.slots ds 1))
    (h : Windows.Dset ds s' ⊆ Windows.Dset ds s) :
    Rulers.oE (Windows.Dset ds s) =
        Rulers.oE (Windows.Dset ds s') + Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s') ∧
      Rulers.oE (Windows.Dset ds s \ Windows.Dset ds s') ≤ 2 ^ ds.length - 1 := W ds s s' h

-- (B1) Lemma 10.20
example {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y : Bf ℚ_[2])
    (hY1 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Y) 1)
    (hY2 : Agree (Y * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∀ s s' : Fin (Dance.slots (Families.ds l) 1),
      ‖(finalM GΞ * Nmat l B Y) s s'‖ ≤ 1 / 2 :=
  B1 hB hα hc hη hζ ht Y hY1 hY2 GΞ hGΞ

-- (B2)
example {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    (Yp Ym : Bf ℚ_[2])
    (hYp1 : Agree ((PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Yp) 1)
    (hYp2 : Agree (Yp * (PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (hYm1 : Agree ((PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Ym) 1)
    (hYm2 : Agree (Ym * (PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∀ s s' : Fin (Dance.slots (Families.ds l) 1),
      ‖(finalM GΞ * Nmat l B Yp) s s'‖ ≤ 1 / 2 ∧ ‖(finalM GΞ * Nmat l B Ym) s s'‖ ≤ 1 / 2 :=
  B2 hB hα hc hη hζ Yp Ym hYp1 hYp2 hYm1 hYm2 GΞ hGΞ

#print axioms Bend.N0
#print axioms Bend.N1
#print axioms Bend.N2
#print axioms Bend.Y0
#print axioms Bend.Y1
#print axioms Bend.W
#print axioms Bend.B1
#print axioms Bend.B2
