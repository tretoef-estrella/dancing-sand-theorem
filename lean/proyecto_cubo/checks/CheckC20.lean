import RequestProject.Doubling.All

/-! Auditor's check file for Lean piece C20 (Grepy Escribano, 7 Oct 2026).
The setting, the weights and the seven closed formulas of `C20_the_doubling_functor.md`
restated by hand (with `⅟k!!` unfolded to `Ring.inverse` and `Π_c` unfolded to the polynomial in
`FE`); Φ(f) on `b_e n`; exactness unfolded; (B2) with factorials; the explicit maps of (D1), (D2)
on the basis vectors `e'_{2s}`, `e'_{2s+1}`; the recursion of `d_R`; (D3) unfolded; then
`#print axioms`. -/

open Finset Polynomial DPLattice WeylFilt Doubling

open scoped Nat

-- the setting: the class is exactly `hodd`, and ℤ_[2] satisfies it
example {A : Type} [CommRing A] [OddUnits A] : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : A) :=
  OddUnits.hodd
example : ∀ k : ℕ, IsUnit ((2 * k + 1 : ℕ) : ℤ_[2]) := padicInt_two_hodd
example : OddUnits ℤ_[2] := inferInstance
-- ⅟(2s−1)!! is the inverse of the double factorial, and ⅟(−1)!! = 1
example {A : Type} [CommRing A] [OddUnits A] (s : ℕ) :
    Ring.inverse (((2 * s - 1)‼ : ℕ) : A) * (((2 * s - 1)‼ : ℕ) : A) = 1 := dfi_mul s
example {A : Type} [CommRing A] : (dfi 0 : A) = 1 := dfi_zero

section
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A)

-- the lattice Φ(N): basis Fin 2 × N.ι, weights 2w+1, 2w−1
example : (phi N).ι = (Fin 2 × N.ι) := rfl
example (i : N.ι) : (phi N).wt ((0 : Fin 2), i) = 2 * N.wt i + 1 := by
  simp [phi, phiWt]
example (i : N.ι) : (phi N).wt ((1 : Fin 2), i) = 2 * N.wt i - 1 := by
  simp [phi, phiWt]; ring

-- the seven closed formulas
example (s : ℕ) (e : Fin 2) (i : N.ι) :
    (phi N).Fd (2 * s) (bvec e (Pi.single i 1)) =
      Ring.inverse (((2 * s - 1)‼ : ℕ) : A) • bvec e (N.Fd s (Pi.single i 1)) :=
  phiFd_even N s e i
example (s : ℕ) (i : N.ι) :
    (phi N).Fd (2 * s + 1) (bvec 0 (Pi.single i 1)) =
      Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A) • bvec 1 (N.Fd s (Pi.single i 1)) :=
  phiFd_odd_b0 N s i
example (s : ℕ) (i : N.ι) :
    (phi N).Fd (2 * s + 1) (bvec 1 (Pi.single i 1)) =
      (((2 * s + 2 : ℕ) : A) * Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A)) •
        bvec 0 (N.Fd (s + 1) (Pi.single i 1)) :=
  phiFd_odd_b1 N s i
example (s : ℕ) (i : N.ι) :
    (phi N).Ed (2 * s) (bvec 1 (Pi.single i 1)) =
      Ring.inverse (((2 * s - 1)‼ : ℕ) : A) • bvec 1
        (aeval (N.Fd 1 * N.Ed 1) (∏ j ∈ range s,
          (4 * X + C ((((N.wt i + 2 * s + 1) ^ 2 - (N.wt i + 2 * j) ^ 2 : ℤ)) : A)))
          (N.Ed s (Pi.single i 1))) :=
  phiEd_even_b1 N s i
example (s : ℕ) (i : N.ι) :
    (phi N).Ed (2 * s + 1) (bvec 1 (Pi.single i 1)) =
      Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A) • bvec 0
        (aeval (N.Fd 1 * N.Ed 1) (∏ j ∈ range (s + 1),
          (4 * X + C ((((N.wt i + 2 * s + 1) ^ 2 - (N.wt i + 2 * j) ^ 2 : ℤ)) : A)))
          (N.Ed s (Pi.single i 1))) :=
  phiEd_odd_b1 N s i
example (s : ℕ) (i : N.ι) :
    (phi N).Ed (2 * s) (bvec 0 (Pi.single i 1)) =
      Ring.inverse (((2 * s - 1)‼ : ℕ) : A) • bvec 0
        (aeval (N.Fd 1 * N.Ed 1) (∏ j ∈ Icc 1 s,
          (4 * X + C ((((N.wt i + 2 * s + 1) ^ 2 - (N.wt i + 2 * j) ^ 2 : ℤ)) : A)))
          (N.Ed s (Pi.single i 1))) :=
  phiEd_even_b0 N s i
example (s : ℕ) (i : N.ι) :
    (phi N).Ed (2 * s + 1) (bvec 0 (Pi.single i 1)) =
      (((2 * (s + 1) : ℕ) : A) * Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A)) • bvec 1
        (aeval (N.Fd 1 * N.Ed 1) (∏ j ∈ Icc 1 s,
          (4 * X + C ((((N.wt i + 2 * s + 3) ^ 2 - (N.wt i + 2 * j) ^ 2 : ℤ)) : A)))
          (N.Ed (s + 1) (Pi.single i 1))) :=
  phiEd_odd_b0 N s i

-- (A1)
example : IsDP (phiWt N) (phiFd N) (phiEd N) := A1 N
example : (phi N).Fd = phiFd N ∧ (phi N).Ed = phiEd N := ⟨rfl, rfl⟩

-- (B1) the r = 1 formulas, H included
example (n : N.ι → A) : (phi N).Fd 1 (bvec 0 n) = bvec 1 n := (B1 N).1 n
example (n : N.ι → A) : (phi N).Fd 1 (bvec 1 n) = (2 : A) • bvec 0 (N.Fd 1 n) := (B1 N).2.1 n
example (n : N.ι → A) : (phi N).Ed 1 (bvec 0 n) = (2 : A) • bvec 1 (N.Ed 1 n) := (B1 N).2.2.1 n
example (w : ℤ) (n : N.ι → A) (hn : ∀ j, N.wt j ≠ w → n j = 0) :
    (phi N).Ed 1 (bvec 1 n) = bvec 0 ((4 : A) • N.Fd 1 (N.Ed 1 n) + ((2 * w + 1 : ℤ) : A) • n) :=
  (B1 N).2.2.2.1 w n hn
example (w : ℤ) (n : N.ι → A) (hn : ∀ j, N.wt j ≠ w → n j = 0) :
    H (phi N) (bvec 0 n) = ((2 * w + 1 : ℤ) : A) • bvec 0 n := (B1 N).2.2.2.2.1 w n hn
example (w : ℤ) (n : N.ι → A) (hn : ∀ j, N.wt j ≠ w → n j = 0) :
    H (phi N) (bvec 1 n) = ((2 * w - 1 : ℤ) : A) • bvec 1 n := (B1 N).2.2.2.2.2 w n hn

-- (B2)
example (r : ℕ) : ((r ! : ℕ) : A) • (phi N).Fd r = (phi N).Fd 1 ^ r := (B2 N r).1
example (r : ℕ) : ((r ! : ℕ) : A) • (phi N).Ed r = (phi N).Ed 1 ^ r := (B2 N r).2

-- (B3) for every vector n
example (s : ℕ) (e : Fin 2) (n : N.ι → A) :
    (phi N).Fd (2 * s) (bvec e n) = Ring.inverse (((2 * s - 1)‼ : ℕ) : A) • bvec e (N.Fd s n) :=
  (B3 N s n).1 e
example (s : ℕ) (n : N.ι → A) :
    (phi N).Fd (2 * s + 1) (bvec 0 n) =
      Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A) • bvec 1 (N.Fd s n) := (B3 N s n).2.1
example (s : ℕ) (n : N.ι → A) :
    (phi N).Fd (2 * s + 1) (bvec 1 n) =
      (((2 * s + 2 : ℕ) : A) * Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A)) •
        bvec 0 (N.Fd (s + 1) n) := (B3 N s n).2.2
end

-- (A2): Φ(f) = 1 ⊗ f, Φ(id) = id, Φ(g ∘ f) = Φ(g) ∘ Φ(f)
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] {N M : DPLattice A}
    (f : Hom N M) (e : Fin 2) (n : N.ι → A) :
    (phiHom f).toLin (bvec e n) = bvec e (f.toLin n) := A2.1 f e n
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) :
    phiHom (Hom.id N) = Hom.id (phi N) := A2.2.1 N
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] {N M P : DPLattice A}
    (g : Hom M P) (f : Hom N M) : phiHom (Hom.comp g f) = Hom.comp (phiHom g) (phiHom f) :=
  A2.2.2 g f

-- (A3) with short exactness unfolded
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] {X Y Z : DPLattice A}
    (f : Hom X Y) (g : Hom Y Z) (hi : Function.Injective f.toLin)
    (hs : Function.Surjective g.toLin) (he : LinearMap.range f.toLin = LinearMap.ker g.toLin) :
    Function.Injective (phiHom f).toLin ∧ Function.Surjective (phiHom g).toLin ∧
      LinearMap.range (phiHom f).toLin = LinearMap.ker (phiHom g).toLin := by
  have h := A3 (⟨hi, hs, he⟩ : ShortExact f g)
  exact ⟨h.inj, h.surj, h.exact⟩

-- (D1): δ_μ on e'_{2s} and e'_{2s+1}, with c_{2s} = ⅟(2s−1)!!, c_{2s+1} = ⅟(2s+1)!!
example {A : Type} [CommRing A] (μ s : ℕ) (hs : s ≤ μ) :
    deltaMap (A := A) μ (Pi.single (⟨2 * s, by omega⟩ : Fin (2 * μ + 1 + 1)) 1) =
      Ring.inverse (((2 * s - 1)‼ : ℕ) : A) •
        bvec 0 (Pi.single (⟨s, by omega⟩ : Fin (μ + 1)) (1 : A)) := by
  rw [show (Pi.single (⟨2 * s, by omega⟩ : Fin (2 * μ + 1 + 1)) (1 : A)) = eD (2 * μ + 1) ⟨2 * s, by omega⟩
    from rfl, deltaMap_eD, cD_even _ s rfl, xD_even μ _ ⟨s, by omega⟩ rfl]
  rfl
example {A : Type} [CommRing A] (μ s : ℕ) (hs : s ≤ μ) :
    deltaMap (A := A) μ (Pi.single (⟨2 * s + 1, by omega⟩ : Fin (2 * μ + 1 + 1)) 1) =
      Ring.inverse (((2 * (s + 1) - 1)‼ : ℕ) : A) •
        bvec 1 (Pi.single (⟨s, by omega⟩ : Fin (μ + 1)) (1 : A)) := by
  rw [show (Pi.single (⟨2 * s + 1, by omega⟩ : Fin (2 * μ + 1 + 1)) (1 : A)) =
    eD (2 * μ + 1) ⟨2 * s + 1, by omega⟩ from rfl, deltaMap_eD, cD_odd _ s rfl,
    xD_odd μ _ ⟨s, by omega⟩ rfl]
  rfl
-- (D1): a morphism, bijective, inverse a morphism, composites the identities
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (μ : ℕ) :
    ∃ (f : Hom (delta A (2 * μ + 1)) (phi (delta A μ)))
      (g : Hom (phi (delta A μ)) (delta A (2 * μ + 1))),
      f.toLin = deltaMap μ ∧ g.toLin = deltaInv μ ∧ Function.Bijective f.toLin ∧
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := (D1 μ).2.2.2

-- (D2): the recursion of d_R and ν_μ on e'_{2s}, e'_{2s+1}
example {A : Type} [CommRing A] (μ : ℕ) :
    dN (A := A) μ 0 = 1 ∧
    (∀ s : ℕ, dN (A := A) μ (2 * s + 1) = dN μ (2 * s) * Ring.inverse (((2 * μ + 1 - 2 * s : ℕ)) : A)) ∧
    (∀ s : ℕ, dN (A := A) μ (2 * s + 2) = dN μ (2 * s + 1)) := dN_rec μ
example {A : Type} [CommRing A] (μ s : ℕ) (hs : s ≤ μ) :
    nablaMap (A := A) μ (Pi.single (⟨2 * s, by omega⟩ : Fin (2 * μ + 1 + 1)) 1) =
      dN (A := A) μ (2 * s) • bvec 0 (Pi.single (⟨s, by omega⟩ : Fin (μ + 1)) (1 : A)) := by
  rw [show (Pi.single (⟨2 * s, by omega⟩ : Fin (2 * μ + 1 + 1)) (1 : A)) = eN (2 * μ + 1) ⟨2 * s, by omega⟩
    from rfl, nablaMap_eN, xN_even μ _ ⟨s, by omega⟩ rfl]
  rfl
example {A : Type} [CommRing A] (μ s : ℕ) (hs : s ≤ μ) :
    nablaMap (A := A) μ (Pi.single (⟨2 * s + 1, by omega⟩ : Fin (2 * μ + 1 + 1)) 1) =
      dN (A := A) μ (2 * s + 1) • bvec 1 (Pi.single (⟨s, by omega⟩ : Fin (μ + 1)) (1 : A)) := by
  rw [show (Pi.single (⟨2 * s + 1, by omega⟩ : Fin (2 * μ + 1 + 1)) (1 : A)) =
    eN (2 * μ + 1) ⟨2 * s + 1, by omega⟩ from rfl, nablaMap_eN, xN_odd μ _ ⟨s, by omega⟩ rfl]
  rfl
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] (μ : ℕ) :
    ∃ (f : Hom (nabla A (2 * μ + 1)) (phi (nabla A μ)))
      (g : Hom (phi (nabla A μ)) (nabla A (2 * μ + 1))),
      f.toLin = nablaMap μ ∧ g.toLin = nablaInv μ ∧ Function.Bijective f.toLin ∧
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := (D2 μ).2.2.2

-- (D3): Φ(𝟙) ≅ V, morphisms both ways whose composites are the identities
example {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A] :
    ∃ (f : Hom (phi (one A)) (V A)) (g : Hom (V A) (phi (one A))),
      Hom.comp g f = Hom.id _ ∧ Hom.comp f g = Hom.id _ := D3'

#print axioms padicInt_two_hodd
#print axioms phiFd_even
#print axioms phiEd_odd_b0
#print axioms A1
#print axioms A2
#print axioms A3
#print axioms B1
#print axioms B2
#print axioms B3
#print axioms isDP_of_rec
#print axioms homOfOne
#print axioms D1
#print axioms D1_iso
#print axioms dN_rec
#print axioms D2
#print axioms D2_iso
#print axioms D3
#print axioms D3'
