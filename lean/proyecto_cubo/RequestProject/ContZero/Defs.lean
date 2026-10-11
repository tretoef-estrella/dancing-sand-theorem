module

public import RequestProject.FormalDance.All

/-!
# `C49b_congruence_and_the_data_at_zero.md`: Definitions (new) — `Cong`, `MCong`

Namespace `ContZero`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
`FormalOps.Bf` (`x.coef m f` = coefficient of `F^{(m)}` at the target floor `f`), and `Agree`,
`MAgree` are C40b's (`FormalDance`). The two new definitions are written exactly as in the file.
Matrices are Mathlib's `Matrix n n (Bf ℤ_[2])`, with the entrywise action of `ℤ_[2]`.
-/

@[expose] public section

noncomputable section

namespace ContZero

open FormalOps FormalDance

/-- Definitions (new) of `C49b_congruence_and_the_data_at_zero.md`: congruence modulo `2 ^ M` in
`Bf ℤ_[2]`, `Cong M x y := ∃ z, Agree (x - y) ((2 : ℤ_[2]) ^ M • z)`. -/
def Cong (M : ℕ) (x y : Bf ℤ_[2]) : Prop :=
  ∃ z : Bf ℤ_[2], Agree (x - y) ((2 : ℤ_[2]) ^ M • z)

/-- Definitions (new) of `C49b_congruence_and_the_data_at_zero.md`: entrywise congruence modulo
`2 ^ M` of matrices over `Bf ℤ_[2]`,
`MCong M G H := ∃ Z, MAgree (G - H) ((2 : ℤ_[2]) ^ M • Z)`. -/
def MCong {n : Type*} (M : ℕ) (G H : Matrix n n (Bf ℤ_[2])) : Prop :=
  ∃ Z : Matrix n n (Bf ℤ_[2]), MAgree (G - H) ((2 : ℤ_[2]) ^ M • Z)

end ContZero
