import RequestProject.Twist.All

/-! Auditor's check file for Lean piece C21 (Grepy Escribano, 7 Oct 2026).
Restated by hand from `C21_reduction_mod_2_and_the_twist.md`: base change entrywise and its
data; (R1)–(R3) with the identity maps; Lucas at 2 at negative tops; the twist's data and `H`;
the six formulas of (C1); (C2) with the identity maps both ways; (C3) with `PadicInt.toZMod`;
then `#print axioms`. -/

open Finset DPLattice WeylFilt Doubling Twist

section R
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)

-- f^φ is the matrix with φ applied entrywise
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : Module.End A (ι → A)) :
    bc φ f = Matrix.toLin' ((LinearMap.toMatrix' f).map φ) := rfl
example {ι : Type} [Fintype ι] [DecidableEq ι] (f : Module.End A (ι → A)) (i j : ι) :
    bc φ f (Pi.single i 1) j = φ (f (Pi.single i 1) j) := bc_single_apply φ f i j
-- M^φ: same basis and weights, F^{(r)} = (M.Fd r)^φ, E^{(r)} = (M.Ed r)^φ
example (M : DPLattice A) : (baseChange φ M).ι = M.ι := rfl
example (M : DPLattice A) : (baseChange φ M).wt = M.wt := rfl
example (M : DPLattice A) (r : ℕ) : (baseChange φ M).Fd r = bc φ (M.Fd r) := rfl
example (M : DPLattice A) (r : ℕ) : (baseChange φ M).Ed r = bc φ (M.Ed r) := rfl
example (M : DPLattice A) :
    IsDP M.wt (fun r => bc φ (M.Fd r)) (fun r => bc φ (M.Ed r)) := R1 φ M
-- (R2)
example {M N : DPLattice A} (f : Hom M N) : (bcHom φ f).toLin = bc φ f.toLin := rfl
example (M : DPLattice A) : bcHom φ (Hom.id M) = Hom.id (baseChange φ M) := (R2 φ).2.1 M
-- (R3) with identity maps
example : ∃ u : Iso (baseChange φ (V A)) (V B),
    u.hom.toLin = LinearMap.id ∧ u.inv.toLin = LinearMap.id := (R3 φ).1
example (M : DPLattice A) : ∃ u : Iso (baseChange φ (tensorV M)) (tensorV (baseChange φ M)),
    u.hom.toLin = LinearMap.id ∧ u.inv.toLin = LinearMap.id := (R3 φ).2 M
end R

section T
variable {B : Type} [CommRing B] (h2 : (2 : B) = 0)

-- (T0) at a negative top
example : ((Ring.choose (2 * (-5 : ℤ)) (2 * 3) : ℤ) : B) = ((Ring.choose (-5 : ℤ) 3 : ℤ) : B) :=
  (T0 h2 (-5) 3).1
example (x : ℤ) (j : ℕ) : ((Ring.choose (2 * x) (2 * j + 1) : ℤ) : B) = 0 := (T0 h2 x j).2
-- the twist: same basis, weights 2·wt, even powers halved, odd powers zero
example (M : DPLattice B) : (frob h2 M).ι = M.ι := rfl
example (M : DPLattice B) (i : M.ι) : (frob h2 M).wt i = 2 * M.wt i := rfl
example (M : DPLattice B) (s : ℕ) : (frob h2 M).Fd (2 * s) = M.Fd s := (frob_data h2 M s).1
example (M : DPLattice B) (s : ℕ) : (frob h2 M).Fd (2 * s + 1) = 0 := (frob_data h2 M s).2.1
example (M : DPLattice B) (s : ℕ) : (frob h2 M).Ed (2 * s) = M.Ed s := (frob_data h2 M s).2.2.1
example (M : DPLattice B) (s : ℕ) : (frob h2 M).Ed (2 * s + 1) = 0 := (frob_data h2 M s).2.2.2.1
-- (T2) same linear map
example {M N : DPLattice B} (f : Hom M N) : (frobHom h2 f).toLin = f.toLin := rfl
end T

section C
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (h2 : (2 : B) = 0)

-- (C0)
example [OddUnits A] (s : ℕ) : φ (dfi s) = 1 := (C0 (φ := φ) h2).1 s
example [OddUnits A] (s : ℕ) : φ ((2 * s + 2 : ℕ) : A) = 0 := (C0 (φ := φ) h2).2.1 s

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A)

-- (C1), the six formulas, for every vector n
example (s : ℕ) (e : Fin 2) (n : N.ι → B) :
    (baseChange φ (phi N)).Fd (2 * s) (bvec e n) = bvec e ((baseChange φ N).Fd s n) :=
  (C1 h2 N s e n).1
example (s : ℕ) (n : N.ι → B) :
    (baseChange φ (phi N)).Fd (2 * s + 1) (bvec 0 n) = bvec 1 ((baseChange φ N).Fd s n) :=
  (C1 h2 N s 0 n).2.1
example (s : ℕ) (n : N.ι → B) : (baseChange φ (phi N)).Fd (2 * s + 1) (bvec 1 n) = 0 :=
  (C1 h2 N s 0 n).2.2.1
example (s : ℕ) (e : Fin 2) (n : N.ι → B) :
    (baseChange φ (phi N)).Ed (2 * s) (bvec e n) = bvec e ((baseChange φ N).Ed s n) :=
  (C1 h2 N s e n).2.2.2.1
example (s : ℕ) (n : N.ι → B) :
    (baseChange φ (phi N)).Ed (2 * s + 1) (bvec 1 n) = bvec 0 ((baseChange φ N).Ed s n) :=
  (C1 h2 N s 0 n).2.2.2.2.1
example (s : ℕ) (n : N.ι → B) : (baseChange φ (phi N)).Ed (2 * s + 1) (bvec 0 n) = 0 :=
  (C1 h2 N s 0 n).2.2.2.2.2
-- (C2) Proposition 3.1 (c), identity maps both ways
example : ∃ u : Iso (baseChange φ (phi N)) (tensorV (frob h2 (baseChange φ N))),
    u.hom.toLin = LinearMap.id ∧ u.inv.toLin = LinearMap.id := C2 φ h2 N
end C

-- (C3) the case of the paper
example : PadicInt.toZMod (2 : ℤ_[2]) = 0 := C3_hyp.2.2.2.2.2
example (N : DPLattice ℤ_[2]) :
    Nonempty (Iso (baseChange PadicInt.toZMod (phi N))
      (tensorV (frob (show (2 : ZMod 2) = 0 from rfl) (baseChange PadicInt.toZMod N)))) := C3 N

#print axioms Twist.R0
#print axioms Twist.R1
#print axioms Twist.R2
#print axioms Twist.R3
#print axioms Twist.T0
#print axioms Twist.T1
#print axioms Twist.T2
#print axioms Twist.frob_data
#print axioms Twist.H_frob
#print axioms Twist.C0
#print axioms Twist.C1
#print axioms Twist.C2
#print axioms Twist.C3_hyp
#print axioms Twist.C3
