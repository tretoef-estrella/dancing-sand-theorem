module

public import RequestProject.FoldCube.PartV

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: Part V — (V3), (V5), (V6)

* (V3) `V3a`, `V3b`, `V3c`, collected in `V3`: with `M = Doubling.phi N`, `c = 2d + 1`,
  `X = thX N BN d B`, `Y = thY N BN d B`, `P = FoldHalf.PE N BN d`, `Q = FoldHalf.QE N BN d`.
  The proof of (a) uses `θ · aOp = aOp · θ`, obtained from (V2) and C39 (E3) after cancelling `2`
  (the vector space `M.ι → A` has no `2`-torsion over `[IsDomain A] [CharZero A]`).
* (V5) `V5`: from (V1), (V2), (O2), (V4) and (V3)(a).
* (V6) `V6`: from (V5), C39 (A3), C29 `T_even` and C32 `sigEquivZ`.
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice Doubling Fold FoldHalf

variable {A : Type*} [CommRing A]

section V3

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (BN : ℕ)
  (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)

lemma beta_inl (x : N.ι → A) : beta N d B (x, 0) = b0 N x := by
  simp [beta_apply']

lemma beta_split (x y : N.ι → A) :
    beta N d B (x, y) = beta N d B (x, 0) + aOp (phi N) (2 * d + 1) B (beta N d B (y, 0)) := by
  rw [beta_inl, beta_inl, beta_apply']

include hnil hB

lemma theta_comm_aOp :
    thetaOp (phi N) (2 * d + 1) * aOp (phi N) (2 * d + 1) B =
      aOp (phi N) (2 * d + 1) B * thetaOp (phi N) (2 * d + 1) := by
  have hc : Commute (aOp (phi N) (2 * d + 1) B) (tauOp (phi N) (2 * d + 1)) :=
    (E3 N BN hnil d B hB).2
  have hc2 : Commute (aOp (phi N) (2 * d + 1) B)
      (tauOp (phi N) (2 * d + 1) * (tauOp (phi N) (2 * d + 1) + 2)) :=
    hc.mul_right (hc.add_right (Commute.ofNat_right _ 2))
  apply smul_two_cancel
  rw [← smul_mul_assoc, ← mul_smul_comm, (V2_phi N d).2]
  exact hc2.eq.symm

lemma beta_betaInv (v : (phi N).ι → A) : beta N d B (betaInv N BN d v) = v :=
  (betaEquiv N BN hnil d B hB).apply_symm_apply v

lemma theta_beta_left (x : N.ι → A) :
    thetaOp (phi N) (2 * d + 1) (beta N d B (x, 0)) =
      beta N d B (thX N BN d B x, thY N BN d B x) := by
  simp only [thX, thY, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Prod.mk.eta]
  rw [beta_betaInv N BN hnil d B hB]

/-- **(V3)(a)** of `C39b_the_cube_side_on_the_half_lattice.md`: under (nil) and `B ≥ 2 * BN`,
`thetaOp M c (FoldHalf.beta N d B (x, y)) = FoldHalf.beta N d B (X x + Y y, Y x + X y)`. -/
theorem V3a (x y : N.ι → A) :
    thetaOp (phi N) (2 * d + 1) (beta N d B (x, y)) =
      beta N d B (thX N BN d B x + thY N BN d B y, thY N BN d B x + thX N BN d B y) := by
  have hθa := LinearMap.congr_fun (theta_comm_aOp N BN hnil d B hB) (beta N d B (y, 0))
  simp only [Module.End.mul_apply] at hθa
  rw [beta_split N d B x y, map_add, hθa, theta_beta_left N BN hnil d B hB,
    theta_beta_left N BN hnil d B hB, (E5 N BN hnil d B hB).2.1, ← map_add]
  rfl

lemma V3b_key (x : N.ι → A) :
    beta N d B ((2 : A) • thX N BN d B x, (2 : A) • thY N BN d B x) =
      beta N d B (PE N BN d (PE N BN d x) + QE N BN d (QE N BN d x) + (2 : A) • PE N BN d x,
        QE N BN d (PE N BN d x) + PE N BN d (QE N BN d x) + (2 : A) • QE N BN d x) := by
  have h1 := (E5 N BN hnil d B hB).1
  have h2 := LinearMap.congr_fun (V2_phi N d).2 (beta N d B (x, 0))
  rw [← Prod.smul_mk, map_smul, ← theta_beta_left N BN hnil d B hB, ← LinearMap.smul_apply, h2,
    Module.End.mul_apply, LinearMap.add_apply, two_apply]
  have h0 := h1 x 0
  simp only [map_zero, add_zero] at h0
  rw [h0, ← map_smul, ← map_add, h1, Prod.smul_mk]
  congr 1
  refine Prod.ext ?_ ?_ <;>
    simp only [Prod.fst_add, Prod.snd_add, map_add, map_smul, smul_zero, add_zero] <;> abel

/-- **(V3)(b)** of `C39b_the_cube_side_on_the_half_lattice.md`:
`(2 : A) • X = P * P + Q * Q + (2 : A) • P` and `(2 : A) • Y = P * Q + Q * P + (2 : A) • Q`. -/
theorem V3b :
    (2 : A) • thX N BN d B = PE N BN d * PE N BN d + QE N BN d * QE N BN d + (2 : A) • PE N BN d ∧
    (2 : A) • thY N BN d B = PE N BN d * QE N BN d + QE N BN d * PE N BN d + (2 : A) • QE N BN d := by
  have hinj := (betaEquiv N BN hnil d B hB).injective
  constructor
  · apply LinearMap.ext; intro x
    have := congrArg Prod.fst (hinj (V3b_key N BN hnil d B hB x))
    simpa using this
  · apply LinearMap.ext; intro x
    have := congrArg Prod.snd (hinj (V3b_key N BN hnil d B hB x))
    simp only at this
    rw [LinearMap.smul_apply, this]
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply]
    abel

/-- **(V3)(c)** of `C39b_the_cube_side_on_the_half_lattice.md`:
`P − Q = FoldHalf.Psi N (d + 1) BN − 2`,
`(2 : A) • (X + Y) = FoldHalf.Psi N d BN * (FoldHalf.Psi N d BN + 2)` and
`(2 : A) • (X − Y) = (FoldHalf.Psi N (d + 1) BN − 2) * FoldHalf.Psi N (d + 1) BN`. -/
theorem V3c :
    PE N BN d - QE N BN d = Psi N (d + 1) BN - 2 ∧
    (2 : A) • (thX N BN d B + thY N BN d B) = Psi N d BN * (Psi N d BN + 2) ∧
    (2 : A) • (thX N BN d B - thY N BN d B) = (Psi N (d + 1) BN - 2) * Psi N (d + 1) BN := by
  obtain ⟨hX, hY⟩ := V3b N BN hnil d B hB
  have h2 : (2 : A) • (1 : Module.End A (N.ι → A)) = 2 := by
    rw [two_smul, one_add_one_eq_two]
  have hPQ : PE N BN d - QE N BN d = Psi N (d + 1) BN - 2 := by
    rw [psi_succ_eq, h2]; abel
  have hsum := (E5 N BN hnil d B hB).2.2
  refine ⟨hPQ, ?_, ?_⟩
  · rw [smul_add, hX, hY, ← hsum, two_smul A (PE N BN d), two_smul A (QE N BN d)]
    noncomm_ring
  · have : Psi N (d + 1) BN = PE N BN d - QE N BN d + 2 := by rw [hPQ]; abel
    rw [smul_sub, hX, hY, this, add_sub_cancel_right, two_smul A (PE N BN d),
      two_smul A (QE N BN d), mul_add, mul_two, sub_mul, mul_sub, mul_sub]
    abel

/-- **(V3)** of `C39b_the_cube_side_on_the_half_lattice.md` (`θ` in the basis `β`): for `N`, `BN`
with (nil) `∀ s ≥ BN, N.Fd s = 0`, `d : ℤ`, `B ≥ 2 * BN`, `M = Doubling.phi N`, `c = 2 * d + 1`,
`X := thX N BN d B`, `Y := thY N BN d B`, `P := FoldHalf.PE N BN d`, `Q := FoldHalf.QE N BN d`:
(a), (b) and (c) of the file. -/
theorem V3 :
    (∀ x y, thetaOp (phi N) (2 * d + 1) (beta N d B (x, y)) =
      beta N d B (thX N BN d B x + thY N BN d B y, thY N BN d B x + thX N BN d B y)) ∧
    ((2 : A) • thX N BN d B = PE N BN d * PE N BN d + QE N BN d * QE N BN d + (2 : A) • PE N BN d ∧
      (2 : A) • thY N BN d B =
        PE N BN d * QE N BN d + QE N BN d * PE N BN d + (2 : A) • QE N BN d) ∧
    (PE N BN d - QE N BN d = Psi N (d + 1) BN - 2 ∧
      (2 : A) • (thX N BN d B + thY N BN d B) = Psi N d BN * (Psi N d BN + 2) ∧
      (2 : A) • (thX N BN d B - thY N BN d B) = (Psi N (d + 1) BN - 2) * Psi N (d + 1) BN) :=
  ⟨V3a N BN hnil d B hB, V3b N BN hnil d B hB, V3c N BN hnil d B hB⟩

end V3

end FoldCube
