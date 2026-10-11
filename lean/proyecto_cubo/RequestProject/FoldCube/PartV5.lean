module

public import RequestProject.FoldCube.PartV3

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: Part V — (V5) and (V6)

* (V5) `V5equiv`, `V5`: Lemma 10.5(b), general form. The chain is: `2d + 2 = (2d + 1) + 1`, (V1)
  with `c = 2d + 1`, (V2) (so the cokernel is that of `(2 : A) • θ`), (O2) for `L = M.ι → A`
  (no `2`-torsion over `[IsDomain A] [CharZero A]`, `O2_pi`), and (V4) with `β = betaEquiv`
  (C39 (E4)) and the identity (V3)(a).
* (V6) `V6`: Lemma 10.5(b) over `ℤ_[2]`, from
  `Families.sigL ℤ_[2] (2l+2) 1 i = Fold.tauOp (Filt.T ℤ_[2] (2l+2)) (2(l + i) + 2)` (`sigL_even`),
  C29 `Filt.T_even`, C39 (A3) for (nil), (V5) and C32 `sigEquivZ` (the explicit form of `B2Z`).
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice Doubling Fold FoldHalf

variable {A : Type*} [CommRing A]

section V5

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (BN : ℕ)
  (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)

/-- (V5) the cokernel of `tauOp (tensorV (phi N)) (2d + 2)` is that of `(2 : A) • θ`
(from (V1) and (V2)). -/
def V5step1 :
    (((tensorV (phi N)).ι → A) ⧸ LinearMap.range (tauOp (tensorV (phi N)) (2 * d + 2))) ≃ₗ[A]
      ((phi N).ι → A) ⧸ LinearMap.range ((2 : A) • thetaOp (phi N) (2 * d + 1)) :=
  (Submodule.quotEquivOfEq _ _ (by rw [show (2 * d + 2 : ℤ) = 2 * d + 1 + 1 by ring])).trans
    ((V1equiv (phi N) (2 * d + 1)).trans
      (Submodule.quotEquivOfEq _ _ (by rw [(V2_phi N d).2])))

include hnil hB

/-- **(V5)** of `C39b_the_cube_side_on_the_half_lattice.md` (Lemma 10.5(b), general form): an explicit
additive equivalence `FoldGroup.twoM (((DPLattice.tensorV (Doubling.phi N)).ι → A) ⧸
range (Fold.tauOp (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2))) ≃+
((N.ι → A) × (N.ι → A)) ⧸ range (FoldHalf.glueOp (X − Y) (X + Y) Y)`,
`X = thX N BN d B`, `Y = thY N BN d B`. -/
def V5equiv :
    FoldGroup.twoM (((tensorV (phi N)).ι → A) ⧸
        LinearMap.range (tauOp (tensorV (phi N)) (2 * d + 2))) ≃+
      ((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (glueOp (thX N BN d B - thY N BN d B)
        (thX N BN d B + thY N BN d B) (thY N BN d B)) :=
  (FoldGroup.twoMCongr (V5step1 N d).toAddEquiv).trans
    ((O2equiv (O2_pi _) (thetaOp (phi N) (2 * d + 1))).trans
      (V4equiv (betaEquiv N BN hnil d B hB) (thetaOp (phi N) (2 * d + 1)) (thX N BN d B)
        (thY N BN d B) (V3a N BN hnil d B hB)).toAddEquiv)

/-- **(V5)** of `C39b_the_cube_side_on_the_half_lattice.md` (Lemma 10.5(b), general form): over
`[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, for `N`, `BN` with (nil), `d : ℤ`,
`B ≥ 2 * BN`: `FoldGroup.twoM (((DPLattice.tensorV (Doubling.phi N)).ι → A) ⧸
range (Fold.tauOp (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2))) ≃+
((N.ι → A) × (N.ι → A)) ⧸ range (FoldHalf.glueOp (thX N BN d B − thY N BN d B)
(thX N BN d B + thY N BN d B) (thY N BN d B))`. -/
theorem V5 :
    Nonempty (FoldGroup.twoM (((DPLattice.tensorV (phi N)).ι → A) ⧸
        LinearMap.range (Fold.tauOp (DPLattice.tensorV (phi N)) (2 * d + 2))) ≃+
      ((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (FoldHalf.glueOp (thX N BN d B - thY N BN d B)
        (thX N BN d B + thY N BN d B) (thY N BN d B))) :=
  ⟨V5equiv N BN hnil d B hB⟩

/-- (V5) transported along an equality `M = tensorV (phi N)` (used for (V6)). -/
theorem V5_of_eq (M : DPLattice A) (hM : M = tensorV (phi N)) :
    Nonempty (FoldGroup.twoM ((M.ι → A) ⧸ LinearMap.range (tauOp M (2 * d + 2))) ≃+
      ((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (glueOp (thX N BN d B - thY N BN d B)
        (thX N BN d B + thY N BN d B) (thY N BN d B))) := by
  subst hM
  exact V5 N BN hnil d B hB

end V5

lemma sigL_even (l i : ℕ) :
    Families.sigL ℤ_[2] (2 * l + 2) 1 i =
      tauOp (Filt.T ℤ_[2] (2 * l + 2)) (2 * ((l : ℤ) + i) + 2) := by
  have h : (((2 * ((l : ℤ) + i) + 2 : ℤ)) : ℤ_[2]) = ((2 * l + 2 : ℕ) : ℤ_[2]) + 2 * (i : ℤ_[2]) := by
    push_cast; ring
  rw [Families.sigL, tauOp, h, add_sub_assoc]
  simp only [Nat.sub_self, pow_zero, one_smul]
  rfl

/-- **(V6)** of `C39b_the_cube_side_on_the_half_lattice.md` (Lemma 10.5(b) over `ℤ_[2]`): for every
`l, i : ℕ`, with `N := Filt.T ℤ_[2] l`, `d := l + i`, `BN := l + 1`, `B := 2 * l + 2`,
`FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i) ≃+ ((N.ι → ℤ_[2]) × (N.ι → ℤ_[2])) ⧸
range (FoldHalf.glueOp (thX N BN d B − thY N BN d B) (thX N BN d B + thY N BN d B)
(thY N BN d B))`. -/
theorem V6 (l i : ℕ) :
    Nonempty (FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 2)) 1 i) ≃+
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
        LinearMap.range (FoldHalf.glueOp
          (thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) -
            thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2))
          (thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) +
            thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2))
          (thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2)))) := by
  have h := V5_of_eq (Filt.T ℤ_[2] l) (l + 1) (FoldHalf.A3 ℤ_[2] l).2 ((l : ℤ) + i) (2 * l + 2)
    (by omega) _ (Filt.T_even ℤ_[2] l)
  rw [← sigL_even] at h
  obtain ⟨e⟩ := h
  exact ⟨(FoldGroup.twoMCongr (Families.sigEquivZ (2 * l + 2) 1 i).symm.toAddEquiv).trans e⟩

end FoldCube
