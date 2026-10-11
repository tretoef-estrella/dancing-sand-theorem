module

public import RequestProject.CubeLaplacian.Basic
public import RequestProject.DPLattice.Basic

/-!
# `C38_the_fold_in_the_group_ring.md`: Definitions (new)

Encodings (namespace `Fold`), reusing C17's `G n = Fin n → ZMod 2`, `e n i`, `lap A n` and C18's
`DPLattice`, `H`:

* `aElt n : G n` is the constant function `1` (the antipode `a = x_1 ⋯ x_n`).
* `transl A n` is the translation by `aElt n` on functions, `(transl A n f) g = f (g + aElt n)`.
* `foldSub A n := range (lap A n) ⊔ range (transl A n − 1)`.
* `Gbar n` is the quotient group `G n ⧸ AddSubgroup.zmultiples (aElt n)` (Mathlib's quotient of
  an additive commutative group), and `mk n : G n →+ Gbar n` is the quotient map
  (`QuotientAddGroup.mk'`).
* `lapBar A n` is the Laplacian of the folded cube, `(lapBar A n u) x = n·u x − Σ_i u (x + mk (e n i))`
  (edges counted with multiplicity).
* `cokerBar n := (Gbar n → ℤ) ⧸ range (lapBar ℤ n)` and `KBar n` is its torsion submodule
  (Mathlib's `Submodule.torsion ℤ`), exactly as `coker` and `K` in C17.
* `push A n f x := Σ_{g ∈ G n, mk g = x} f g` (a sum over `Finset.univ.filter`).
* For a DP-lattice `M` over `A`, `c : ℤ`, `B : ℕ` (a vector of `M` is `M.ι → A`):
  `signOp M c` multiplies the coordinate `i` by `(−1)^{((c − wt i)/2).natAbs}` (integer division
  `Int.ediv`), `expF M B := Σ_{r < B} F^{(r)}`, `aOp M c B := signOp M c ∘ₗ expF M B`,
  `tauOp M c := F^{(1)} + (c : A) • 1 − H M`, and
  `Xbar M c B := (M.ι → A) ⧸ (range (tauOp M c) ⊔ range (aOp M c B − 1))`.
-/

@[expose] public section

noncomputable section

namespace Fold

open CubeLaplacian DPLattice Finset

/-- Definitions (C38): the antipode `a = x_1 ⋯ x_n`, i.e. the element `aElt n = (1, …, 1)` of
`G n`. -/
def aElt (n : ℕ) : G n := fun _ => 1

/-- Definitions (C38): the translation by the antipode, `(transl A n f) g = f (g + aElt n)`. -/
def transl (A : Type*) [CommRing A] (n : ℕ) : (G n → A) →ₗ[A] (G n → A) where
  toFun f g := f (g + aElt n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma transl_apply (A : Type*) [CommRing A] (n : ℕ) (f : G n → A) (g : G n) :
    transl A n f g = f (g + aElt n) := rfl

/-- Definitions (C38): `foldSub A n := range (lap A n) ⊔ range (transl A n − 1)`. -/
def foldSub (A : Type*) [CommRing A] (n : ℕ) : Submodule A (G n → A) :=
  LinearMap.range (lap A n) ⊔ LinearMap.range (transl A n - 1)

/-- Definitions (C38): the vertex set of the folded cube, `Gbar n := G n ⧸ ⟨aElt n⟩`. -/
abbrev Gbar (n : ℕ) := G n ⧸ AddSubgroup.zmultiples (aElt n)

/-- Definitions (C38): the quotient map `mk : G n → Gbar n` (an additive homomorphism). -/
def mk (n : ℕ) : G n →+ Gbar n := QuotientAddGroup.mk' _

/-- Definitions (C38): the Laplacian of the folded cube,
`(lapBar A n u) x = n·u x − Σ_i u (x + mk (e n i))` (edges counted with multiplicity). -/
def lapBar (A : Type*) [CommRing A] (n : ℕ) : (Gbar n → A) →ₗ[A] (Gbar n → A) where
  toFun u x := (n : A) * u x - ∑ i, u (x + mk n (e n i))
  map_add' u u' := by
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

lemma lapBar_apply (A : Type*) [CommRing A] (n : ℕ) (u : Gbar n → A) (x : Gbar n) :
    lapBar A n u x = (n : A) * u x - ∑ i, u (x + mk n (e n i)) := rfl

/-- Definitions (C38): `cokerBar n := (Gbar n → ℤ) ⧸ range (lapBar ℤ n)`. -/
abbrev cokerBar (n : ℕ) := (Gbar n → ℤ) ⧸ LinearMap.range (lapBar ℤ n)

/-- Definitions (C38): the critical group `K̄(n)` of the folded cube, the torsion of
`cokerBar n` (as `K` in C17). -/
abbrev KBar (n : ℕ) := Submodule.torsion ℤ (cokerBar n)

open Classical in
/-- Definitions (C38): `(push A n f) x = Σ_{g : mk g = x} f g`. -/
def push (A : Type*) [CommRing A] (n : ℕ) : (G n → A) →ₗ[A] (Gbar n → A) where
  toFun f x := ∑ g ∈ univ.filter (fun g => mk n g = x), f g
  map_add' f f' := by
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]

variable {A : Type*} [CommRing A]

/-- Definitions (C38): `(signOp M c f) i = (−1)^{((c − wt i)/2).natAbs} * f i`. -/
def signOp (M : DPLattice A) (c : ℤ) : Module.End A (M.ι → A) where
  toFun f i := (-1) ^ ((c - M.wt i) / 2).natAbs * f i
  map_add' f f' := by funext i; simp [mul_add]
  map_smul' a f := by funext i; simp; ring

lemma signOp_apply (M : DPLattice A) (c : ℤ) (f : M.ι → A) (i : M.ι) :
    signOp M c f i = (-1) ^ ((c - M.wt i) / 2).natAbs * f i := rfl

/-- Definitions (C38): `expF M B := Σ_{r ∈ range B} F^{(r)}`. -/
def expF (M : DPLattice A) (B : ℕ) : Module.End A (M.ι → A) := ∑ r ∈ range B, M.Fd r

/-- Definitions (C38): `aOp M c B := signOp M c ∘ₗ expF M B`. -/
def aOp (M : DPLattice A) (c : ℤ) (B : ℕ) : Module.End A (M.ι → A) :=
  signOp M c ∘ₗ expF M B

/-- Definitions (C38): `tauOp M c := F^{(1)} + (c : A) • 1 − H M`. -/
def tauOp (M : DPLattice A) (c : ℤ) : Module.End A (M.ι → A) :=
  M.Fd 1 + (c : A) • 1 - H M

/-- Definitions (C38):
`Xbar M c B := (M.ι → A) ⧸ (range (tauOp M c) ⊔ range (aOp M c B − 1))`. -/
abbrev Xbar (M : DPLattice A) (c : ℤ) (B : ℕ) :=
  (M.ι → A) ⧸ (LinearMap.range (tauOp M c) ⊔ LinearMap.range (aOp M c B - 1))

end Fold
