import RequestProject.Conjugation.All

/-! Auditor's check file for Lean piece C45: conjugation by eta^D along the dance, invertibility,
and Theorem 10.12 first half for every unit eta (Grepy Escribano, 9 Oct 2026). Restated by hand
from `C45_conjugation_and_general_eta.md`; then `#print axioms`. -/

open Matrix Finset FormalOps FormalDance Conjugation

-- the definitions, by `rfl`
example {A : Type} [CommRing A] (u : A) (x : Bf A) (j : ℕ) (f : ℤ) :
    (cj u x).coef j f = u ^ j * x.coef j f := rfl
example {A : Type} [CommRing A] {n : Type} (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A))
    (s s' : n) : cjSys c u w G s s' = ((c * w s * (w s')⁻¹ : Aˣ) : A) • cj (u : A) (G s s') := rfl
example (ds : List Bool) (r : ℕ) (j : Fin (Dance.slots ds r)) :
    ((qSlot ds r j : Fin r) : ℕ) = (j : ℕ) / 2 ^ Dance.mCount ds := rfl

-- (C4)
example {A : Type} [CommRing A] (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A))
    (hG : DanceRel ds r G Gk) (c u : Aˣ) (w : Fin r → Aˣ) :
    DanceRel ds r (cjSys c u w G)
      (cjSys (c * u⁻¹ ^ (2 ^ ds.length - 1)) (u ^ 2 ^ ds.length)
        (fun j => w (qSlot ds r j) * u ^ Rulers.oE (Windows.Dset ds j)) Gk) :=
  C4 ds r G Gk hG c u w

-- (C5)
example {A : Type} [CommRing A] {ds : List Bool} (u : Aˣ) (x : Bf A)
    {Gk : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf A)}
    (h : DanceRel ds 1 (fun _ _ => x) Gk) :
    ∃ Gk' : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf A),
      DanceRel ds 1 (fun _ _ => cj (u : A) x) Gk' ∧
      ∀ s s', finalM Gk' s s' =
        ((u : A) ^ Rulers.oE (Windows.Dset ds s) *
          ((u⁻¹ : Aˣ) : A) ^ Rulers.oE (Windows.Dset ds s') *
          ((u⁻¹ : Aˣ) : A) ^ (2 ^ ds.length - 1)) * finalM Gk s s' :=
  C5_one u x h

-- (D0)
example {A : Type} [CommRing A] (ds : List Bool) (r : ℕ) (G G' : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A))
    (h : DanceRel ds r G Gk) (hGG : MAgree G G') : DanceRel ds r G' Gk :=
  D0 ds r G G' Gk h hGG

-- (I)
example {K : Type} [Field K] (x : Bf K) (hx : ∀ f : ℤ, 0 ≤ f → x.coef 0 f ≠ 0) :
    ∃ Y : Bf K, Agree (x * Y) 1 ∧ Agree (Y * x) 1 := I x hx

-- (X1), (X2)
example (α c : ℕ) {η : ℚ_[2]} (hη : η ≠ 0) (ζ : ℕ → ℤ → ℚ_[2]) :
    PathSum.XiOp α c η ζ = cj η (PathSum.XiOp α c 1 (fun j f => η⁻¹ ^ j * ζ j f)) ∧
    PathSum.SigOp α c η = cj η (PathSum.SigOp α c 1) := X1 α c hη ζ
example {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1) :
    ∀ j, 2 ≤ j → ∀ f, ‖η⁻¹ ^ j * ζ j f‖ ≤ 1 := X2 hη hζ

-- (T1η), (T2η), (F1η) together
example {l α c : ℕ} (hl : 1 ≤ l) (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ j, 2 ≤ j → ∀ f, ‖ζ j f‖ ≤ 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∃ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
        (Bf ℚ_[2]),
      DanceRel (Families.ds l) 1 (fun _ _ => PathSum.SigOp α c η) GSig ∧
      (IsUnit (finalM GΞ).det ∧ IsUnit (finalM GSig).det ∧
        ∃ E' : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
            ℚ_[2],
          finalM GΞ = Stability.hadOne (finalM GSig) E' ∧
          ∀ s s', ‖E' s s'‖ ≤ (2 : ℝ) ^ (-((α : ℤ) - 1))) ∧
      (∀ s s', (finalM GΞ s s' = 0 ↔ finalM GSig s s' = 0) ∧
        ‖finalM GΞ s s'‖ = ‖finalM GSig s s'‖) ∧
      (∀ s s', finalM GSig s s' = if Windows.Dset (Families.ds l) s' ⊆ Windows.Dset (Families.ds l) s
        then η ^ ((Rulers.oE (Windows.Dset (Families.ds l) s) : ℤ) -
          Rulers.oE (Windows.Dset (Families.ds l) s') - (2 ^ (Families.ds l).length - 1)) *
        ((Deficit.Mc (Windows.Ids (Families.ds l)) (Families.ds l).length (α : ℤ) c
          (Windows.Dset (Families.ds l) s) (Windows.Dset (Families.ds l) s') : ℚ) : ℚ_[2])
        else 0) :=
  T_eta hl hα hc hη hζ GΞ hGΞ

-- (F1η) for every dance of Sigma
example (ds : List Bool) {α : ℕ} (hα : 1 ≤ α) (c : ℕ) {η : ℚ_[2]} (hη : η ≠ 0)
    (GSig : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]))
    (hG : DanceRel ds 1 (fun _ _ => PathSum.SigOp α c η) GSig) (s s' : Fin (Dance.slots ds 1)) :
    finalM GSig s s' = if Windows.Dset ds s' ⊆ Windows.Dset ds s then
      η ^ ((Rulers.oE (Windows.Dset ds s) : ℤ) - Rulers.oE (Windows.Dset ds s') -
        (2 ^ ds.length - 1)) *
      ((Deficit.Mc (Windows.Ids ds) ds.length (α : ℤ) c (Windows.Dset ds s)
        (Windows.Dset ds s') : ℚ) : ℚ_[2])
      else 0 := F1eta_gen ds hα c hη GSig hG s s'

#print axioms Conjugation.C1
#print axioms Conjugation.C2
#print axioms Conjugation.C3
#print axioms Conjugation.C4
#print axioms Conjugation.C5
#print axioms Conjugation.D0
#print axioms Conjugation.I
#print axioms Conjugation.X1
#print axioms Conjugation.X2
#print axioms Conjugation.T_eta
#print axioms Conjugation.T1eta
#print axioms Conjugation.T2eta
#print axioms Conjugation.F1eta
#print axioms Conjugation.F1eta_gen
