module

public import RequestProject.GlueDance.All

/-!
# `C50b_the_dance_modulo_two.md`: Definitions (new)

Namespace `DanceMod2`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
(`FormalOps`); `Agree`, `MAgree`, `vsplit`, `CleanStep`, `DanceRel` are C40b's (`FormalDance`);
`slots`, `splitIso` are C13's (`Dance`); `MCong` is C49b's (`ContZero`); `KRep`, `Kr`, `oS`, `Dn`,
`covSys`, `prodFun` are C47's (`RingK`); `InK`, `PayA`, `CoefB`, `Good`, `GB`, `GC`, `GP`, `GD`,
`vsplitG`, `splitDn`, `rinv`, `schurG` are C48's (`Cleanliness`); `glueC`, `PairRel` are C50's
(`GlueDance`).

The new definitions are written exactly as in the file:

* `RA R = Finset ℕ → ℕ → R`, a type synonym: addition, zero, negation are pointwise (those of the
  function type), while `1` and `*` are the new ones (`RA.one`, `RA.mul`); the commutative ring
  structure is (R1), in `PartR.lean`;
* `red4 = PadicInt.toZModPow 2 : ℤ_[2] →+* ZMod (2 ^ 2)`;
* `kap Γ Δ m = red4 (Γ Δ m 0)`;
* `Cong2 Γ Γ'' := ∀ Δ m y, ∃ z, Γ Δ m y - Γ'' Δ m y = 2 * z`.
-/

@[expose] public section

noncomputable section

namespace DanceMod2

open Finset

/-- Definitions (new) of `C50b_the_dance_modulo_two.md`: the carrier of the ring `RA R`
(C47's `RS` with the coefficient ring `R` in place of `𝒮`). -/
def RA (R : Type*) := Finset ℕ → ℕ → R

namespace RA

variable {R : Type*} [CommRing R]

instance : AddCommGroup (RA R) := inferInstanceAs (AddCommGroup (Finset ℕ → ℕ → R))

instance : CoeFun (RA R) (fun _ => Finset ℕ → ℕ → R) := ⟨fun β => β⟩

/-- Definitions (new) of `C50b_the_dance_modulo_two.md`: the unit of `RA R`,
`fun Δ q => if Δ = ∅ ∧ q = 0 then 1 else 0`. -/
def one : RA R := fun Δ q => if Δ = ∅ ∧ q = 0 then 1 else 0

/-- Definitions (new) of `C50b_the_dance_modulo_two.md`: the product of `RA R`,
`(β γ) Δ q = Σ_{Δ₁ ⊆ Δ} Σ_{a ≤ q} C(q, a) β Δ₁ a γ (Δ \ Δ₁) (q − a)`. -/
def mul (β γ : RA R) : RA R := fun Δ q =>
  ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
    (Nat.choose q a : R) * β Δ₁ a * γ (Δ \ Δ₁) (q - a)

instance : One (RA R) := ⟨one⟩
instance : Mul (RA R) := ⟨mul⟩

lemma add_apply (β γ : RA R) (Δ : Finset ℕ) (q : ℕ) : (β + γ) Δ q = β Δ q + γ Δ q := rfl
lemma zero_apply (Δ : Finset ℕ) (q : ℕ) : (0 : RA R) Δ q = 0 := rfl
lemma neg_apply (β : RA R) (Δ : Finset ℕ) (q : ℕ) : (-β) Δ q = -β Δ q := rfl
lemma sub_apply (β γ : RA R) (Δ : Finset ℕ) (q : ℕ) : (β - γ) Δ q = β Δ q - γ Δ q := rfl

omit [CommRing R] in
@[ext] lemma ext {β γ : RA R} (h : ∀ Δ q, β Δ q = γ Δ q) : β = γ :=
  funext fun Δ => funext (h Δ)

end RA

/-- Definitions (new) of `C50b_the_dance_modulo_two.md`: the reduction modulo `4`,
`red4 = PadicInt.toZModPow 2`. -/
abbrev red4 : ℤ_[2] →+* ZMod (2 ^ 2) := PadicInt.toZModPow 2

/-- Definitions (new) of `C50b_the_dance_modulo_two.md`: the constant terms modulo `4` of a
system, `kap Γ Δ m = red4 (Γ Δ m 0)`. -/
def kap (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : RA (ZMod (2 ^ 2)) := fun Δ m => red4 (Γ Δ m 0)

/-- Definitions (new) of `C50b_the_dance_modulo_two.md`: congruence modulo `2` of two systems,
`∀ Δ m y, ∃ z, Γ Δ m y - Γ'' Δ m y = 2 * z`. -/
def Cong2 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Prop :=
  ∀ Δ m y, ∃ z, Γ Δ m y - Γ'' Δ m y = 2 * z

end DanceMod2
