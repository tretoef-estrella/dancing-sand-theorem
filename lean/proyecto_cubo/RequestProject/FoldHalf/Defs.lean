module

public import RequestProject.FoldGroup.All
public import RequestProject.Lemma35.Basic

/-!
# `C39_the_fold_on_the_half_lattice.md`: Definitions (new)

Encodings (namespace `FoldHalf`), reusing C18's `DPLattice`, `H`, C20's `Doubling.dfi`
(`dfi s = ⅟(2s − 1)!!`, `dfi 0 = 1`):

* A vector of the DP-lattice `N` is a function `N.ι → A`; an operator on `N` is an element of
  the ring `Module.End A (N.ι → A)` (product `*` = composition `∘ₗ`, `1` = identity).
* `Ch N BN := Σ_{s ∈ range BN} dfi s • N.Fd s` and `Sh N BN := Σ_{s ∈ range BN} dfi (s + 1) • N.Fd s`
  (finite sums over `Finset.range BN`, i.e. `s < BN`).
* `parOp N d` (`d : ℤ`) multiplies the coordinate `i` by `(−1)^{(d − N.wt i).natAbs}`.
* `ShInv N BN := Ring.inverse (Sh N BN)`, the inverse in the ring `Module.End A (N.ι → A)`
  (Mathlib's `Ring.inverse`, which is `0` on non-units).
* `Psi N d BN := ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + (Ch N BN − parOp N d) * ShInv N BN`.
* `Zop N d BN := −1 − parOp N d * ShInv N BN`.
* `glueOp X Y Z` for operators `X, Y, Z` on any `A`-module `L` (in the file `L = N.ι → A`) is the
  operator on `L × L` given by `(m, m') ↦ (X m, Z m + Y m')` (Mathlib's `LinearMap.prod` of
  `X ∘ fst` and `Z ∘ fst + Y ∘ snd`); it is defined for any module, which is more general.
-/

@[expose] public section

noncomputable section

namespace FoldHalf

open DPLattice Doubling Finset

variable {A : Type*} [CommRing A]

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`:
`Ch N BN := Σ_{s < BN} dfi s • N.Fd s` (the paper's `Ch = Σ F^{(s)}/(2s − 1)!!`). -/
def Ch (N : DPLattice A) (BN : ℕ) : Module.End A (N.ι → A) :=
  ∑ s ∈ range BN, dfi (A := A) s • N.Fd s

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`:
`Sh N BN := Σ_{s < BN} dfi (s + 1) • N.Fd s` (the paper's `Sh = Σ F^{(s)}/(2s + 1)!!`). -/
def Sh (N : DPLattice A) (BN : ℕ) : Module.End A (N.ι → A) :=
  ∑ s ∈ range BN, dfi (A := A) (s + 1) • N.Fd s

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`: `parOp N d` multiplies the
coordinate `i` by `(−1)^{(d − N.wt i).natAbs}`. -/
def parOp (N : DPLattice A) (d : ℤ) : Module.End A (N.ι → A) where
  toFun f i := (-1) ^ (d - N.wt i).natAbs * f i
  map_add' f f' := by funext i; simp [mul_add]
  map_smul' a f := by funext i; simp; ring

lemma parOp_apply (N : DPLattice A) (d : ℤ) (f : N.ι → A) (i : N.ι) :
    parOp N d f i = (-1) ^ (d - N.wt i).natAbs * f i := rfl

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`:
`ShInv N BN := Ring.inverse (Sh N BN)` in the ring `Module.End A (N.ι → A)`. -/
def ShInv (N : DPLattice A) (BN : ℕ) : Module.End A (N.ι → A) := Ring.inverse (Sh N BN)

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`:
`Psi N d BN := ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + (Ch N BN − parOp N d) * ShInv N BN`
(the paper's `Ψ_j`). -/
def Psi (N : DPLattice A) (d : ℤ) (BN : ℕ) : Module.End A (N.ι → A) :=
  ((2 * d : ℤ) : A) • 1 - (2 : A) • H N + (Ch N BN - parOp N d) * ShInv N BN

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`:
`Zop N d BN := −1 − parOp N d * ShInv N BN` (the paper's `(Ψ_i − Ψ_{i+1})/2`). -/
def Zop (N : DPLattice A) (d : ℤ) (BN : ℕ) : Module.End A (N.ι → A) :=
  -1 - parOp N d * ShInv N BN

/-- Definitions (new) of `C39_the_fold_on_the_half_lattice.md`: for operators `X, Y, Z` on a
module `L`, the operator `(m, m') ↦ (X m, Z m + Y m')` on `L × L` (the paper's `glue(X, Y)` with
lower-left block `Z`). Stated for any module `L` (the file uses `L = N.ι → A`). -/
def glueOp {L : Type*} [AddCommGroup L] [Module A L] (X Y Z : Module.End A L) :
    Module.End A (L × L) :=
  LinearMap.prod (X ∘ₗ LinearMap.fst A L L) (Z ∘ₗ LinearMap.fst A L L + Y ∘ₗ LinearMap.snd A L L)

@[simp] lemma glueOp_apply {L : Type*} [AddCommGroup L] [Module A L] (X Y Z : Module.End A L)
    (p : L × L) : glueOp X Y Z p = (X p.1, Z p.1 + Y p.2) := rfl

end FoldHalf
