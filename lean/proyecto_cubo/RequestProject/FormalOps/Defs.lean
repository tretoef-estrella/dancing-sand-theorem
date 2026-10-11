module

public import RequestProject.FormalOps.Bf
public import RequestProject.Doubling.Basic

/-!
# `C40_the_formal_operators.md`: Definitions (new) — `flD`, `act`, the twist map, the `V`-split

Encodings (namespace `FormalOps`), reusing C18's `DPLattice` and C20's `Doubling.dfi`:

* A vector of a DP-lattice `N` is a function `N.ι → A`; an operator is an element of the ring
  `Module.End A (N.ι → A)` (`*` = composition, `1` = identity).
* `flD N W p` (`p : ℤ → A`) is the diagonal operator `(flD N W p v) i = p ((W − N.wt i) / 2) * v i`
  (`/` is integer division `Int.ediv`), exactly as in the file.
* `act N W B x := Σ_{m ∈ range B} flD N W (x.coef m) * N.Fd m`, exactly as in the file.
* `tw00`, `tw11`, `tw10`, `tw01` (the twist map), `vplus`, `vprime` (the `V`-split) are elements
  of `Bf A` whose coefficients are written exactly as in the file (`tw01` by cases on the first
  index: `0` and `q + 1`). The natural numbers `2q`, `2q + 1`, `2q + 2` in the indices are
  natural numbers, and `2f`, `2f + 1`, `g + 1` are integers.
-/

@[expose] public section

noncomputable section

namespace FormalOps

open DPLattice Doubling Finset

variable {A : Type*} [CommRing A]

/-- Definitions (new) of `C40_the_formal_operators.md`: the diagonal operator
`(flD N W p v) i = p ((W − N.wt i) / 2) * v i` (`p` evaluated at the floor of `i`). -/
def flD (N : DPLattice A) (W : ℤ) (p : ℤ → A) : Module.End A (N.ι → A) where
  toFun v i := p ((W - N.wt i) / 2) * v i
  map_add' v w := by funext i; simp [mul_add]
  map_smul' c v := by funext i; simp; ring

@[simp] lemma flD_apply (N : DPLattice A) (W : ℤ) (p : ℤ → A) (v : N.ι → A) (i : N.ι) :
    flD N W p v i = p ((W - N.wt i) / 2) * v i := rfl

/-- Definitions (new) of `C40_the_formal_operators.md`: the action of `x : Bf A` on `N`,
`act N W B x := Σ_{m ∈ range B} flD N W (x.coef m) * N.Fd m`. -/
def act (N : DPLattice A) (W : ℤ) (B : ℕ) (x : Bf A) : Module.End A (N.ι → A) :=
  ∑ m ∈ range B, flD N W (x.coef m) * N.Fd m

/-- Definitions (new), the twist map: `(tw00 x).coef q f = dfi q * x.coef (2q) (2f)`. -/
def tw00 (x : Bf A) : Bf A := ⟨fun q f => dfi q * x.coef (2 * q) (2 * f)⟩

/-- Definitions (new), the twist map: `(tw11 x).coef q f = dfi q * x.coef (2q) (2f + 1)`. -/
def tw11 (x : Bf A) : Bf A := ⟨fun q f => dfi q * x.coef (2 * q) (2 * f + 1)⟩

/-- Definitions (new), the twist map:
`(tw10 x).coef q f = dfi (q + 1) * x.coef (2q + 1) (2f + 1)`. -/
def tw10 (x : Bf A) : Bf A := ⟨fun q f => dfi (q + 1) * x.coef (2 * q + 1) (2 * f + 1)⟩

/-- Definitions (new), the twist map: `(tw01 x).coef 0 f = 0` and
`(tw01 x).coef (q + 1) f = ((2q + 2 : ℕ) : A) * dfi (q + 1) * x.coef (2q + 1) (2f)`. -/
def tw01 (x : Bf A) : Bf A :=
  ⟨fun m f => match m with
    | 0 => 0
    | q + 1 => ((2 * q + 2 : ℕ) : A) * dfi (q + 1) * x.coef (2 * q + 1) (2 * f)⟩

/-- Definitions (new), the `V`-split: `(vplus x).coef m g = x.coef m (g + 1)`. -/
def vplus (x : Bf A) : Bf A := ⟨fun m g => x.coef m (g + 1)⟩

/-- Definitions (new), the `V`-split: `(vprime x).coef m g = x.coef (m + 1) (g + 1)`. -/
def vprime (x : Bf A) : Bf A := ⟨fun m g => x.coef (m + 1) (g + 1)⟩

@[simp] lemma coef_tw00 (x : Bf A) (q : ℕ) (f : ℤ) :
    (tw00 x).coef q f = dfi q * x.coef (2 * q) (2 * f) := rfl
@[simp] lemma coef_tw11 (x : Bf A) (q : ℕ) (f : ℤ) :
    (tw11 x).coef q f = dfi q * x.coef (2 * q) (2 * f + 1) := rfl
@[simp] lemma coef_tw10 (x : Bf A) (q : ℕ) (f : ℤ) :
    (tw10 x).coef q f = dfi (q + 1) * x.coef (2 * q + 1) (2 * f + 1) := rfl
@[simp] lemma coef_tw01_zero (x : Bf A) (f : ℤ) : (tw01 x).coef 0 f = 0 := rfl
@[simp] lemma coef_tw01_succ (x : Bf A) (q : ℕ) (f : ℤ) :
    (tw01 x).coef (q + 1) f = ((2 * q + 2 : ℕ) : A) * dfi (q + 1) * x.coef (2 * q + 1) (2 * f) :=
  rfl
@[simp] lemma coef_vplus (x : Bf A) (m : ℕ) (g : ℤ) : (vplus x).coef m g = x.coef m (g + 1) := rfl
@[simp] lemma coef_vprime (x : Bf A) (m : ℕ) (g : ℤ) :
    (vprime x).coef m g = x.coef (m + 1) (g + 1) := rfl

end FormalOps
