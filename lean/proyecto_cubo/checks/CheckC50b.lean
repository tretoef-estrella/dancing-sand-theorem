import RequestProject.DanceMod2.All

/-! Auditor's check file for Lean piece C50b: the dance modulo two, Lemma 10.18
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50b_the_dance_modulo_two.md`;
then `#print axioms`. -/

open Finset Cleanliness FormalOps FormalDance ContZero DanceMod2
open RingK (Kr prodFun covSys Dn oS)

-- the new definitions, by `rfl`
example (β γ : RA ℤ) (Δ : Finset ℕ) (q : ℕ) :
    (β * γ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
      (Nat.choose q a : ℤ) * β Δ₁ a * γ (Δ \ Δ₁) (q - a) := rfl
example (Δ : Finset ℕ) (q : ℕ) : (1 : RA ℤ) Δ q = if Δ = ∅ ∧ q = 0 then 1 else 0 := rfl
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) :
    kap Γ Δ m = PadicInt.toZModPow 2 (Γ Δ m 0) := rfl
example (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    Cong2 Γ Γ'' = ∀ Δ m y, ∃ z, Γ Δ m y - Γ'' Δ m y = 2 * z := rfl

-- (R1) a commutative ring
example (R : Type*) [CommRing R] : CommRing (RA R) := RA.instCommRing

-- (R2)
example {R : Type*} [CommRing R] (β : RA R) (Δ : Finset ℕ) (q : ℕ) :
    ∃ x : R, (β * β) Δ q = (if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0) + 2 * x := R2 β Δ q

-- (K1)
example {ϑ : ℤ_[2] → ℤ_[2]} (hϑ : ϑ ∈ Kr) (y : ℤ_[2]) :
    PadicInt.toZModPow 2 (ϑ y) = PadicInt.toZModPow 2 (ϑ 0) := K1 hϑ y

-- (K2) the product
example (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : InK Γ) (hΓ' : InK Γ') :
    kap (prodFun h Γ Γ') = kap Γ * kap Γ' := (K2 h Γ Γ' hΓ hΓ').1

-- (K4)
example (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hK : InK Γ) (hB : CoefB Γ) :
    kap (GP h Γ) * kap (rinv (h + 1) (GP h Γ)) = 1 ∧
      kap (schurG h Γ) =
        kap (GD Γ) - kap (GB Γ) * kap (rinv (h + 1) (GP h Γ)) * kap (GB Γ) := K4 h Γ hK hB

-- (M1)
example (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (h : ℕ) : kap (schurG h Γ) = kap (schurG h Γ'') := M1 Γ Γ'' hΓ hΓ'' hc h

-- (M2)
example (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (h : ℕ) :
    ∀ Δ m y, ∃ z, schurG h Γ Δ m y - schurG h Γ'' Δ m y = 4 * z := M2 Γ Γ'' hΓ hΓ'' hc h

-- (M3)
example (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hG : Good Γ) (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      (∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y) ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') := M3 Γ hG P h c

-- (M4)
example (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (h : ℕ) (Γ' Γ''' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (h1 : ∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y)
    (h2 : ∀ Δ m y, 2 * Γ''' Δ m y = schurG h Γ'' Δ m y) : Cong2 Γ' Γ''' :=
  M4 Γ Γ'' hΓ hΓ'' hc h Γ' Γ''' h1 h2

-- (D1) Lemma 10.18
example (ds : List Bool) (r h : ℕ) (P : Finset ℕ) (hP : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'') (hc : Cong2 Γ Γ'')
    (e : Fin r ≃ Dn P) (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hX : X = fun j j' => covSys P h c Γ (e j) (e j'))
    (hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j')) :
    ∃ Xk Yk, GlueDance.PairRel ds r X Y Xk Yk :=
  D1 ds r h P hP c Γ Γ'' hΓ hΓ'' hc e X Y hX hY

-- (D2) the glued dance
example (ds : List Bool) (r h : ℕ) (P : Finset ℕ) (hP : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'') (hc : Cong2 Γ Γ'')
    (e : Fin r ≃ Dn P) (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hX : X = fun j j' => covSys P h c Γ (e j) (e j'))
    (hY : Y = fun j j' => covSys P h c Γ'' (e j) (e j'))
    (r₂ : ℕ) (hr : r₂ = 2 * r) (Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z)) :
    ∃ Xk Yk Zk, DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧
      MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧
      DanceRel ds r₂ (GlueDance.glueC hr X Y Z)
        (GlueDance.glueC (GlueDance.S4 ds hr) Xk Yk Zk) :=
  D2 ds r h P hP c Γ Γ'' hΓ hΓ'' hc e X Y hX hY r₂ hr Z hZ

#print axioms DanceMod2.R1
#print axioms DanceMod2.R2
#print axioms DanceMod2.K1
#print axioms DanceMod2.K2
#print axioms DanceMod2.K3
#print axioms DanceMod2.K4
#print axioms DanceMod2.M1
#print axioms DanceMod2.M2
#print axioms DanceMod2.M3
#print axioms DanceMod2.M4
#print axioms DanceMod2.M5
#print axioms DanceMod2.M6
#print axioms DanceMod2.D0
#print axioms DanceMod2.D1
#print axioms DanceMod2.D2
#print axioms DanceMod2.D3
