module

public import RequestProject.FormalOps.Bf

/-!
# `C47_the_ring_K_and_covariant_systems.md`: Definitions (new)

Namespace `RingK`. Nothing of the project is redefined: `Bf` is C40's `FormalOps.Bf`
(`x.coef m f` = coefficient of `F^{(m)}` at the target floor `f : ℤ`), with its ring structure.

Definitions 1–11 of the file, written as there:

* `KRep` (fields `a`, `p`, `q`, `hp : p.coeff 0 = 0`, `hq : IsUnit (q.coeff 0)`) and
  `KRep.eval r y = r.a + 2 * r.p.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))`;
* `Kr = Set.range KRep.eval` (the rational class `𝒦_r`);
* `S = TrivSqZeroExt (ZMod 2) (PowerSeries (ZMod 2))`, `red = PadicInt.toZMod`;
* `thetaRep r = inl (red r.a) + inr (p̄ * q̄⁻¹)` and `theta ϑ` (via `Classical.choose` on `Kr`,
  `0` outside `Kr`);
* `RS = Finset ℕ → ℕ → S`, a type synonym: addition, zero, negation are pointwise (those of
  the function type), while `1` and `*` are the new ones of Definition 7 (`RS.one`, `RS.mul`);
  the ring structure is (R1), in `PartR.lean`;
* `oS D = Σ_{t ∈ D} 2^t`, `Dn P = {D // D ⊆ P}`, `covSys`, `thetaSys`, `prodFun`.
-/

@[expose] public section

noncomputable section

namespace RingK

open FormalOps Finset

/-- Definitions (new) 1 of `C47_the_ring_K_and_covariant_systems.md`: a representation
`(a, p, q)` of an element `a + 2 p(2y)/q(2y)` of the class `𝒦_r`. -/
structure KRep where
  /-- the constant term -/
  a : ℤ_[2]
  /-- the numerator -/
  p : Polynomial ℤ_[2]
  /-- the denominator -/
  q : Polynomial ℤ_[2]
  hp : p.coeff 0 = 0
  hq : IsUnit (q.coeff 0)

/-- Definitions (new) 2 of `C47_the_ring_K_and_covariant_systems.md`: the function represented
by `r`, `y ↦ a + 2 p(2y) · q(2y)⁻¹`. -/
def KRep.eval (r : KRep) (y : ℤ_[2]) : ℤ_[2] :=
  r.a + 2 * r.p.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))

/-- Definitions (new) 3 of `C47_the_ring_K_and_covariant_systems.md`: the class `𝒦_r`. -/
def Kr : Set (ℤ_[2] → ℤ_[2]) := Set.range KRep.eval

/-- Definitions (new) 4 of `C47_the_ring_K_and_covariant_systems.md` (instance needed for `𝒮`
to be a commutative ring): the left and right actions of `ZMod 2` on `PowerSeries (ZMod 2)`
agree. -/
instance instIsCentralScalarPS : IsCentralScalar (ZMod 2) (PowerSeries (ZMod 2)) :=
  ⟨fun r m => by ext n; simp [mul_comm]⟩

/-- Definitions (new) 4 of `C47_the_ring_K_and_covariant_systems.md`: the ring `𝒮`. -/
abbrev S := TrivSqZeroExt (ZMod 2) (PowerSeries (ZMod 2))

/-- Definitions (new) 4 of `C47_the_ring_K_and_covariant_systems.md`: `𝒮` is a commutative ring
(the structure of `TrivSqZeroExt`, recorded as an instance for faster elaboration). -/
instance instCommRingS : CommRing S := inferInstance

/-- Setting of `C47_the_ring_K_and_covariant_systems.md`: `red = PadicInt.toZMod`. -/
abbrev red : ℤ_[2] →+* ZMod 2 := PadicInt.toZMod

/-- Definitions (new) 5 of `C47_the_ring_K_and_covariant_systems.md`: `Θ` on a representation. -/
def thetaRep (r : KRep) : S :=
  TrivSqZeroExt.inl (red r.a) +
    TrivSqZeroExt.inr ((r.p.map red : PowerSeries (ZMod 2)) *
      ((r.q.map red : PowerSeries (ZMod 2)))⁻¹)

open Classical in
/-- Definitions (new) 6 of `C47_the_ring_K_and_covariant_systems.md`: `Θ` on functions. -/
def theta (ϑ : ℤ_[2] → ℤ_[2]) : S :=
  if h : ϑ ∈ Kr then thetaRep (Classical.choose h) else 0

/-- Definitions (new) 7 of `C47_the_ring_K_and_covariant_systems.md`: the carrier of `R_𝒮`. -/
def RS := Finset ℕ → ℕ → S

namespace RS

instance : AddCommGroup RS := inferInstanceAs (AddCommGroup (Finset ℕ → ℕ → S))

instance : CoeFun RS (fun _ => Finset ℕ → ℕ → S) := ⟨fun β => β⟩

/-- Definitions (new) 7 of `C47_the_ring_K_and_covariant_systems.md`: the unit of `R_𝒮`. -/
def one : RS := fun Δ q => if Δ = ∅ ∧ q = 0 then 1 else 0

/-- Definitions (new) 7 of `C47_the_ring_K_and_covariant_systems.md`: the product of `R_𝒮`. -/
def mul (β γ : RS) : RS := fun Δ q =>
  ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
    (Nat.choose q a : S) * β Δ₁ a * γ (Δ \ Δ₁) (q - a)

instance : One RS := ⟨one⟩
instance : Mul RS := ⟨mul⟩

lemma one_apply (Δ : Finset ℕ) (q : ℕ) :
    (1 : RS) Δ q = if Δ = ∅ ∧ q = 0 then 1 else 0 := rfl

lemma mul_apply (β γ : RS) (Δ : Finset ℕ) (q : ℕ) :
    (β * γ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
      (Nat.choose q a : S) * β Δ₁ a * γ (Δ \ Δ₁) (q - a) := rfl

lemma add_apply (β γ : RS) (Δ : Finset ℕ) (q : ℕ) : (β + γ) Δ q = β Δ q + γ Δ q := rfl
lemma zero_apply (Δ : Finset ℕ) (q : ℕ) : (0 : RS) Δ q = 0 := rfl
lemma neg_apply (β : RS) (Δ : Finset ℕ) (q : ℕ) : (-β) Δ q = -β Δ q := rfl
lemma sub_apply (β γ : RS) (Δ : Finset ℕ) (q : ℕ) : (β - γ) Δ q = β Δ q - γ Δ q := rfl

@[ext] lemma ext {β γ : RS} (h : ∀ Δ q, β Δ q = γ Δ q) : β = γ := funext fun Δ => funext (h Δ)

end RS

/-- Definitions (new) 8 of `C47_the_ring_K_and_covariant_systems.md`: the offset
`o_D = Σ_{t ∈ D} 2^t`. -/
def oS (D : Finset ℕ) : ℕ := ∑ t ∈ D, 2 ^ t

/-- Definitions (new) 9 of `C47_the_ring_K_and_covariant_systems.md`: the subsets of `P`. -/
def Dn (P : Finset ℕ) := {D : Finset ℕ // D ⊆ P}

instance (P : Finset ℕ) : Fintype (Dn P) :=
  inferInstanceAs (Fintype {D : Finset ℕ // D ⊆ P})

instance (P : Finset ℕ) : DecidableEq (Dn P) :=
  inferInstanceAs (DecidableEq {D : Finset ℕ // D ⊆ P})

/-- Definitions (new) 9 of `C47_the_ring_K_and_covariant_systems.md`: the covariant system,
`(covSys P h c Γ D D').coef m f = if D' ⊆ D then Γ (D \ D') m (2^h f + o_D + c) else 0`. -/
def covSys (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    Matrix (Dn P) (Dn P) (Bf ℤ_[2]) := fun D D' =>
  ⟨fun m f => if D'.1 ⊆ D.1 then
    Γ (D.1 \ D'.1) m ((2 : ℤ_[2]) ^ h * f + oS D.1 + c) else 0⟩

/-- Definitions (new) 10 of `C47_the_ring_K_and_covariant_systems.md`: `Θ_h` on systems. -/
def thetaSys (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : RS := fun Δ m => theta (Γ Δ m)

/-- Definitions (new) 11 of `C47_the_ring_K_and_covariant_systems.md`: the product of systems,
`Σ_{Δ₁ ⊆ Δ} Σ_{a ≤ m} C(m, a) Γ Δ₁ a y · Γ' (Δ \ Δ₁) (m − a) (y − a 2^h − o_{Δ₁})`. -/
def prodFun (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] := fun Δ m y =>
  ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (m + 1),
    (Nat.choose m a : ℤ_[2]) * Γ Δ₁ a y *
      Γ' (Δ \ Δ₁) (m - a) (y - a * 2 ^ h - oS Δ₁)

end RingK
