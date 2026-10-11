module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# `C44_stability_and_rigidity.md`: the definitions `hadOne` and `Wt` (Part S)

Namespace `Stability`.

* `hadOne B E` is the matrix `B ∘ (1 + E)` of the file, with entries `B i j * (1 + E i j)`.
* `Wt S ν s` is the weighted set of Part S: matrices supported on the relation `S` whose entry
  `(i, j)` has `2`-adic norm at most `2^{−(ν i j + s)}`.

The field is `ℚ_[2]` with its norm (`‖2‖ = 1/2`), so `‖x‖ ≤ 2^{−s}` means `v_2(x) ≥ s`; the
bound `2^{−s}` is written `(2 : ℝ) ^ (-(s : ℤ))`.
-/

@[expose] public section

noncomputable section

namespace Stability

/-- `C44_stability_and_rigidity.md` (introduction): `B ∘ (1 + E)`, the matrix with entries
`B i j * (1 + E i j)`. -/
def hadOne {n : Type*} (B E : Matrix n n ℚ_[2]) : Matrix n n ℚ_[2] :=
  Matrix.of fun i j => B i j * (1 + E i j)

/-- `C44_stability_and_rigidity.md`, Part S, **Definition**: the weighted set
`Wt S ν s = {X | ∀ i j, (¬ S i j → X i j = 0) ∧ ‖X i j‖ ≤ 2^{−(ν i j + s)}}`. -/
def Wt {n : Type*} (S : n → n → Prop) (ν : n → n → ℕ) (s : ℕ) : Set (Matrix n n ℚ_[2]) :=
  {X | ∀ i j, (¬ S i j → X i j = 0) ∧ ‖X i j‖ ≤ (2 : ℝ) ^ (-((ν i j + s : ℕ) : ℤ))}

end Stability
