module

public import RequestProject.Fold.All
public import RequestProject.Families.Theorem
public import RequestProject.Mirror.Group

/-!
# `C38b_the_folded_cube_and_proposition_103.md`: Definitions (new)

Encodings (namespace `FoldGroup`), reusing C38's `Fold.Xbar` and C29's `Filt.T`:

* `XbarFam lam i := Fold.Xbar (Filt.T ℤ_[2] lam) (lam + 2 * i) (lam + 2 * i + 1)` (the paper's
  `X̄(λ, i)`), written exactly as in the file: the centre `lam + 2 * i` is the integer
  `(lam : ℤ) + 2 * (i : ℤ)` (the centre argument of `Fold.Xbar` is an integer) and the bound
  `lam + 2 * i + 1` is a natural number.
* `twoM M : AddSubgroup M` is `2·M`, the range of the additive endomorphism `x ↦ 2 • x`
  (Mathlib's `nsmulAddMonoidHom 2`, `2 : ℕ`); membership is `mem_twoM`.
-/

@[expose] public section

noncomputable section

namespace FoldGroup

open CubeLaplacian Fold

/-- Definitions (new) of `C38b_the_folded_cube_and_proposition_103.md`: the paper's `X̄(λ, i)`,
`XbarFam λ i := Fold.Xbar (Filt.T ℤ_[2] λ) (λ + 2 * i) (λ + 2 * i + 1)` (a `ℤ_[2]`-module). -/
abbrev XbarFam (lam i : ℕ) :=
  Fold.Xbar (Filt.T ℤ_[2] lam) (lam + 2 * i) (lam + 2 * i + 1)

/-- Definitions (new) of `C38b_the_folded_cube_and_proposition_103.md`: for an additive
commutative group `M`, the subgroup `2·M = {2 • x : x ∈ M}`, the range of `x ↦ 2 • x`. -/
def twoM (M : Type*) [AddCommGroup M] : AddSubgroup M := (nsmulAddMonoidHom (α := M) 2).range

/-- Membership in `twoM M` (Definitions of `C38b_the_folded_cube_and_proposition_103.md`). -/
lemma mem_twoM {M : Type*} [AddCommGroup M] {y : M} : y ∈ twoM M ↔ ∃ x : M, (2 : ℕ) • x = y := by
  simp [twoM]

end FoldGroup
