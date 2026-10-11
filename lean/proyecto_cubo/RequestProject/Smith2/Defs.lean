module

public import RequestProject.FormalDance.All

/-!
# `C46_smith_form_and_cokernel_over_Z2.md`: Definitions (new) — `Bf.map`, `XiOpZ`, `trunc`

Namespace `Smith2`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
`FormalOps.Bf` (`x.coef m f` = coefficient of `F^{(m)}` at the target floor `f`).

* `Bf.map φ x` (here `Smith2.Bf.map`) is the operator with `(Bf.map φ x).coef m f = φ (x.coef m f)`;
  on a matrix `G` over `Bf A` it acts entrywise as `G.map (Bf.map φ)` (Mathlib's `Matrix.map`).
* `XiOpZ α c η ζ : Bf ℤ_[2]` has `coef 0 f = 2 ^ α * ((f : ℤ_[2]) + c)`, `coef 1 f = η` and
  `coef j f = ζ j f` for `j ≥ 2`, exactly as in the file.
* `trunc N X i j = ((X i j).appr N : ℤ)` (Mathlib's `PadicInt.appr`, a natural number cast to `ℤ`).
-/

@[expose] public section

noncomputable section

namespace Smith2

open FormalOps

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- Definitions (new) 1 of `C46_smith_form_and_cokernel_over_Z2.md`: the formal operator mapped
along `φ`, `(Bf.map φ x).coef m f = φ (x.coef m f)`. -/
def Bf.map (φ : A →+* A') (x : Bf A) : Bf A' := ⟨fun m f => φ (x.coef m f)⟩

/-- Definitions (new) 1 of `C46_smith_form_and_cokernel_over_Z2.md` (simp lemma):
`(Bf.map φ x).coef m f = φ (x.coef m f)`. -/
@[simp] lemma Bf.coef_map (φ : A →+* A') (x : Bf A) (m : ℕ) (f : ℤ) :
    (Bf.map φ x).coef m f = φ (x.coef m f) := rfl

/-- Definitions (new) 2 of `C46_smith_form_and_cokernel_over_Z2.md`: the operator `Ξ` with
integral data, `coef 0 f = 2 ^ α * ((f : ℤ_[2]) + c)`, `coef 1 f = η`, `coef j f = ζ j f` for
`j ≥ 2`. -/
def XiOpZ (α c : ℕ) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) : Bf ℤ_[2] :=
  ⟨fun m f => if m = 0 then 2 ^ α * ((f : ℤ_[2]) + c) else if m = 1 then η else ζ m f⟩

/-- Definitions (new) 3 of `C46_smith_form_and_cokernel_over_Z2.md`: the truncation of a matrix
over `ℤ_[2]`, `trunc N X i j = ((X i j).appr N : ℤ)`. -/
def trunc {n : Type*} (N : ℕ) (X : Matrix n n ℤ_[2]) : Matrix n n ℤ :=
  fun i j => ((X i j).appr N : ℤ)

end Smith2
