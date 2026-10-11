module

public import Mathlib

/-!
# `C40_the_formal_operators.md`: Definitions (new) — the formal operators `Bf A` and (B1)

Encoding (namespace `FormalOps`): `Bf A` is a new structure with one field
`coef : ℕ → ℤ → A`; `x.coef m f` is the coefficient of `F^{(m)}` at the target floor `f`.
Extensionality is `Bf.ext` / `Bf.ext_iff` (`x = y ↔ ∀ m f, x.coef m f = y.coef m f`).
`0`, `+`, `−`, `n •` (`n : ℕ` or `ℤ`) and `a •` (`a : A`) act coefficientwise; `1` has
`coef 0 f = 1` and `coef m f = 0` for `m ≥ 1`; the product is
`(x * y).coef m f = Σ_{a ∈ range (m + 1)} (Nat.choose m a : A) * x.coef a f * y.coef (m − a) (f − a)`.
The natural-number cast `n` (resp. integer cast) is the operator with `coef 0 f = n` and
`coef m f = 0` for `m ≥ 1`. With these, `Bf A` is a ring (`instRing`, (B1)) and an `A`-algebra
(`instAlgebra`, (B1)).
-/

@[expose] public section

noncomputable section

namespace FormalOps

open Finset

/-- Definitions (new) of `C40_the_formal_operators.md`: the formal operators `𝔅` over `A`, a new
type whose elements carry coefficients `coef m f` (the coefficient of `F^{(m)}` at the target
floor `f`). -/
structure Bf (A : Type*) [CommRing A] where
  /-- the coefficient of `F^{(m)}` at the target floor `f` -/
  coef : ℕ → ℤ → A

namespace Bf

variable {A : Type*} [CommRing A]

/-- Definitions (new): extensionality, `x = y` as soon as `x.coef m f = y.coef m f` for all
`m f`. -/
@[ext] theorem ext {x y : Bf A} (h : ∀ m f, x.coef m f = y.coef m f) : x = y := by
  cases x; cases y; congr; funext m f; exact h m f

lemma coef_injective : Function.Injective (coef : Bf A → ℕ → ℤ → A) := fun x y h =>
  ext fun m f => by rw [h]

instance : Zero (Bf A) := ⟨⟨fun _ _ => 0⟩⟩
instance : Add (Bf A) := ⟨fun x y => ⟨fun m f => x.coef m f + y.coef m f⟩⟩
instance : Neg (Bf A) := ⟨fun x => ⟨fun m f => -x.coef m f⟩⟩
instance : Sub (Bf A) := ⟨fun x y => ⟨fun m f => x.coef m f - y.coef m f⟩⟩
instance : SMul ℕ (Bf A) := ⟨fun n x => ⟨fun m f => n • x.coef m f⟩⟩
instance : SMul ℤ (Bf A) := ⟨fun n x => ⟨fun m f => n • x.coef m f⟩⟩
instance : SMul A (Bf A) := ⟨fun a x => ⟨fun m f => a * x.coef m f⟩⟩
instance : One (Bf A) := ⟨⟨fun m _ => if m = 0 then 1 else 0⟩⟩
instance : NatCast (Bf A) := ⟨fun n => ⟨fun m _ => if m = 0 then (n : A) else 0⟩⟩
instance : IntCast (Bf A) := ⟨fun n => ⟨fun m _ => if m = 0 then (n : A) else 0⟩⟩
/-- Definitions (new): the product
`(x * y).coef m f = Σ_{a ∈ range (m + 1)} C(m, a) * x.coef a f * y.coef (m − a) (f − a)`. -/
instance : Mul (Bf A) :=
  ⟨fun x y => ⟨fun m f => ∑ a ∈ range (m + 1),
    (Nat.choose m a : A) * x.coef a f * y.coef (m - a) (f - a)⟩⟩

@[simp] lemma coef_zero (m : ℕ) (f : ℤ) : (0 : Bf A).coef m f = 0 := rfl
/-- (B1) simp lemma: `(x + y).coef m f = x.coef m f + y.coef m f`. -/
@[simp] lemma coef_add (x y : Bf A) (m : ℕ) (f : ℤ) :
    (x + y).coef m f = x.coef m f + y.coef m f := rfl
@[simp] lemma coef_neg (x : Bf A) (m : ℕ) (f : ℤ) : (-x).coef m f = -x.coef m f := rfl
@[simp] lemma coef_sub (x y : Bf A) (m : ℕ) (f : ℤ) :
    (x - y).coef m f = x.coef m f - y.coef m f := rfl
@[simp] lemma coef_nsmul (n : ℕ) (x : Bf A) (m : ℕ) (f : ℤ) :
    (n • x).coef m f = n • x.coef m f := rfl
@[simp] lemma coef_zsmul (n : ℤ) (x : Bf A) (m : ℕ) (f : ℤ) :
    (n • x).coef m f = n • x.coef m f := rfl
@[simp] lemma coef_smul (a : A) (x : Bf A) (m : ℕ) (f : ℤ) :
    (a • x).coef m f = a * x.coef m f := rfl
/-- (B1) simp lemma: `coef 0 f = 1` and `coef m f = 0` for `m ≥ 1` for the unit. -/
@[simp] lemma coef_one (m : ℕ) (f : ℤ) : (1 : Bf A).coef m f = if m = 0 then 1 else 0 := rfl
@[simp] lemma coef_natCast (n m : ℕ) (f : ℤ) :
    (n : Bf A).coef m f = if m = 0 then (n : A) else 0 := rfl
@[simp] lemma coef_intCast (n : ℤ) (m : ℕ) (f : ℤ) :
    (n : Bf A).coef m f = if m = 0 then (n : A) else 0 := rfl
/-- (B1) simp lemma: the product of formal operators. -/
@[simp] lemma coef_mul (x y : Bf A) (m : ℕ) (f : ℤ) :
    (x * y).coef m f = ∑ a ∈ range (m + 1),
      (Nat.choose m a : A) * x.coef a f * y.coef (m - a) (f - a) := rfl

instance : AddCommGroup (Bf A) :=
  coef_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

lemma mul_assoc' (x y z : Bf A) : x * y * z = x * (y * z) := by
  ext m f
  simp only [coef_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := range (m + 1)) (s' := fun b => Ico b (m + 1))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at hb
    rw [Finset.sum_Ico_eq_sum_range, show m + 1 - b = m - b + 1 by omega]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.mem_range] at hc
    have hch : (m.choose (b + c) : A) * ((b + c).choose b : A) =
        (m.choose b : A) * ((m - b).choose c : A) := by
      have := Nat.choose_mul (n := m) (k := b + c) (s := b) (by omega)
      rw [show b + c - b = c by omega] at this
      rw [← Nat.cast_mul, ← Nat.cast_mul, this]
    rw [show b + c - b = c by omega, show m - (b + c) = m - b - c by omega,
      show f - ((b + c : ℕ) : ℤ) = f - b - c by push_cast; ring]
    linear_combination (x.coef b f * y.coef c (f - b) * z.coef (m - b - c) (f - b - c)) * hch
  · intro a b
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- **(B1)** of `C40_the_formal_operators.md`: `Bf A` is a ring, with the coefficientwise `0`,
`+`, `−`, the unit `1` and the product of the file. -/
instance instRing : Ring (Bf A) :=
  { (inferInstance : AddCommGroup (Bf A)) with
    mul := (· * ·)
    one := 1
    natCast := fun n => (n : Bf A)
    intCast := fun n => (n : Bf A)
    mul_assoc := mul_assoc'
    one_mul := fun x => by
      ext m f
      rw [coef_mul, Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    mul_one := fun x => by
      ext m f
      rw [coef_mul, Finset.sum_eq_single m]
      · simp
      · intro b hb hbm
        rw [Finset.mem_range] at hb
        simp [show m - b ≠ 0 by omega]
      · simp
    zero_mul := fun x => by ext m f; simp
    mul_zero := fun x => by ext m f; simp
    left_distrib := fun x y z => by
      ext m f; simp [mul_add, Finset.sum_add_distrib]
    right_distrib := fun x y z => by
      ext m f; simp [mul_add, add_mul, Finset.sum_add_distrib]
    natCast_zero := by ext m f; simp
    natCast_succ := fun n => by
      ext m f; simp only [coef_natCast, coef_add, coef_one]; split_ifs <;> push_cast <;> ring
    intCast_ofNat := fun n => by ext m f; simp
    intCast_negSucc := fun n => by
      ext m f; simp only [coef_intCast, coef_neg, coef_natCast]
      split_ifs <;> simp [Int.negSucc_eq] }

instance : Module A (Bf A) :=
  coef_injective.module A
    { toFun := coef, map_zero' := rfl, map_add' := fun _ _ => rfl } (fun _ _ => rfl)

/-- **(B1)** compatibility with scalars: `(a • x) * y = a • (x * y)`. -/
theorem smul_mul (a : A) (x y : Bf A) : (a • x) * y = a • (x * y) := by
  ext m f; simp [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

/-- **(B1)** compatibility with scalars: `x * (a • y) = a • (x * y)`. -/
theorem mul_smul (a : A) (x y : Bf A) : x * (a • y) = a • (x * y) := by
  ext m f; simp [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

/-- **(B1)** of `C40_the_formal_operators.md`: `Bf A` is an `A`-algebra (scalars act
coefficientwise). -/
instance instAlgebra : Algebra A (Bf A) := Algebra.ofModule smul_mul mul_smul

/-- Definitions (new): the formal `F^{(m)}`, `coef m' f = if m' = m then 1 else 0`. -/
def fd (m : ℕ) : Bf A := ⟨fun m' _ => if m' = m then 1 else 0⟩

/-- Definitions (new): the floor function `p(D)`, `coef 0 f = p f`, `coef m f = 0` for `m ≥ 1`. -/
def dg (p : ℤ → A) : Bf A := ⟨fun m f => if m = 0 then p f else 0⟩

/-- (B1) simp lemma for `Bf.fd`. -/
@[simp] lemma coef_fd (m m' : ℕ) (f : ℤ) : (fd m : Bf A).coef m' f = if m' = m then 1 else 0 := rfl

/-- (B1) simp lemma for `Bf.dg`. -/
@[simp] lemma coef_dg (p : ℤ → A) (m : ℕ) (f : ℤ) :
    (dg p).coef m f = if m = 0 then p f else 0 := rfl

end Bf

end FormalOps
