module

public import RequestProject.FoldHalf.All

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: Definitions (new)

Encodings (namespace `FoldCube`), reusing C18's `DPLattice`, `H`, C20's `Doubling.phi`, C39's
`FoldHalf.beta`, `FoldHalf.betaInv`:

* A vector of the DP-lattice `M` is a function `M.ι → A`; an operator on `M` is an element of the
  ring `Module.End A (M.ι → A)` (product `*` = composition, `1` = identity, `2 = 2 • 1`).
* `Jop M c := (c : A) • 1 − H M` (`c : ℤ`), `Gp N d := N.Fd 1 − (2 : A) • (Jop N d * (Jop N d + 1))`,
  `SigmaOp N e := N.Fd 1 + ((2 * e : ℤ) : A) • 1 − (2 : A) • H N`, written exactly as in the file.
* `halfJJ M c` is the diagonal operator `(halfJJ M c f) i = ((((c − wt i) * (c − wt i + 2)) / 2 : ℤ) : A) * f i`
  (`/` is integer division `Int.ediv`).
* `thetaOp M c := M.Fd 2 + M.Fd 1 * (Jop M c + 2) + halfJJ M c`.
* `thX N BN d B`, `thY N BN d B`: the blocks of `θ` in the basis `β` of C39 (E4), written exactly
  as in the file with `LinearMap.fst`, `LinearMap.snd`, `LinearMap.inl` (`M = Doubling.phi N`;
  since `Doubling.phi` needs `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, so do these two).
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice Doubling

variable {A : Type*} [CommRing A]

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`:
`Jop M c := (c : A) • 1 − H M` (so `Fold.tauOp M c = M.Fd 1 + Jop M c`). -/
def Jop (M : DPLattice A) (c : ℤ) : Module.End A (M.ι → A) := (c : A) • 1 - H M

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`:
`Gp N d := N.Fd 1 − (2 : A) • (Jop N d * (Jop N d + 1))` (the paper's `G'`). -/
def Gp (N : DPLattice A) (d : ℤ) : Module.End A (N.ι → A) :=
  N.Fd 1 - (2 : A) • (Jop N d * (Jop N d + 1))

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`:
`SigmaOp N e := N.Fd 1 + ((2 * e : ℤ) : A) • 1 − (2 : A) • H N` (the paper's `Σ`). -/
def SigmaOp (N : DPLattice A) (e : ℤ) : Module.End A (N.ι → A) :=
  N.Fd 1 + ((2 * e : ℤ) : A) • 1 - (2 : A) • H N

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`: `halfJJ M c` multiplies the
coordinate `i` by `((((c − M.wt i) * (c − M.wt i + 2)) / 2 : ℤ) : A)` (integer division). -/
def halfJJ (M : DPLattice A) (c : ℤ) : Module.End A (M.ι → A) where
  toFun f i := ((((c - M.wt i) * (c - M.wt i + 2)) / 2 : ℤ) : A) * f i
  map_add' f g := by funext i; simp [mul_add]
  map_smul' a f := by funext i; simp; ring

lemma halfJJ_apply (M : DPLattice A) (c : ℤ) (f : M.ι → A) (i : M.ι) :
    halfJJ M c f i = ((((c - M.wt i) * (c - M.wt i + 2)) / 2 : ℤ) : A) * f i := rfl

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`:
`thetaOp M c := M.Fd 2 + M.Fd 1 * (Jop M c + 2) + halfJJ M c` (the paper's `θ = τ(τ + 2)/2`). -/
def thetaOp (M : DPLattice A) (c : ℤ) : Module.End A (M.ι → A) :=
  M.Fd 2 + M.Fd 1 * (Jop M c + 2) + halfJJ M c

section phi

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`: the diagonal block of `θ` in
the basis `β`, `thX N BN d B := LinearMap.fst ∘ₗ FoldHalf.betaInv N BN d ∘ₗ
thetaOp (Doubling.phi N) (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl`. -/
def thX (N : DPLattice A) (BN : ℕ) (d : ℤ) (B : ℕ) : Module.End A (N.ι → A) :=
  LinearMap.fst A (N.ι → A) (N.ι → A) ∘ₗ FoldHalf.betaInv N BN d ∘ₗ
    thetaOp (phi N) (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl A (N.ι → A) (N.ι → A)

/-- Definitions (new) of `C39b_the_cube_side_on_the_half_lattice.md`: the off-diagonal block of `θ`
in the basis `β`, `thY N BN d B := LinearMap.snd ∘ₗ FoldHalf.betaInv N BN d ∘ₗ
thetaOp (Doubling.phi N) (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl`. -/
def thY (N : DPLattice A) (BN : ℕ) (d : ℤ) (B : ℕ) : Module.End A (N.ι → A) :=
  LinearMap.snd A (N.ι → A) (N.ι → A) ∘ₗ FoldHalf.betaInv N BN d ∘ₗ
    thetaOp (phi N) (2 * d + 1) ∘ₗ FoldHalf.beta N d B ∘ₗ LinearMap.inl A (N.ι → A) (N.ι → A)

end phi

end FoldCube
