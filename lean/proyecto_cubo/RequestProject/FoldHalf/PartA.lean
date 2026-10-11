module

public import RequestProject.FoldHalf.PartE
public import RequestProject.FoldHalf.Quot

/-!
# `C39_the_fold_on_the_half_lattice.md`: Part A — Lemma 10.4(a) and Lemma 10.5(a)

* (A1) `A1equiv`, `A1`: `Fold.Xbar (Doubling.phi N) (2 * d + 1) B ≃ₗ[A]
  (N.ι → A) ⧸ range (Psi N d BN)` for `B ≥ 2 * BN`. The map sends the class of `β (x, y)` to the
  class of `x + y` (`β` of (E4)).
* (A2) `A2equiv`, `A2`: `Fold.Xbar (tensorV (Doubling.phi N)) (2 * d + 2) B ≃ₗ[A]
  ((N.ι → A) × (N.ι → A)) ⧸ range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN))` for
  `B ≥ 2 * BN + 1`, following the sketch of the file: modulo `aOp − 1`, `V ⊗ M ≅ M` through
  `ψ (b₀ u₀ + b₁ u₁) = u₀ + (1 − a) u₁`, `tauOp` becomes `f = 1 + tauOp_M − aOp_M`, and in the
  basis `β` followed by the slot change `(u, v) ↦ (v − u, u)` `f` becomes the glued operator.
* (A3) `A3`: weights of `Filt.T A l` in `[−l, l]`, `(Filt.T A l).Fd s = 0` for `s ≥ l + 1`.
* (A4) `A4_odd`, `A4_even` (and `A4`): the families `FoldGroup.XbarFam` over `ℤ_[2]`.

`Doubling.phi` (hence (A1), (A2)) needs `[IsDomain A] [CharZero A] [OddUnits A]` (C20).
"`≃ₗ[A]`" statements are given as explicit definitions and as `Nonempty` theorems.
-/

@[expose] public section

noncomputable section

namespace FoldHalf

open DPLattice Doubling Finset Fold

variable {A : Type*} [CommRing A]

/-! ### The slots of `V ⊗ M` (any ring) -/

section slots

variable (M : DPLattice A)

/-- `bvec 0` with codomain written `(tensorV M).ι → A`. -/
def t0 : (M.ι → A) →ₗ[A] ((tensorV M).ι → A) := bvec 0
/-- `bvec 1` with codomain written `(tensorV M).ι → A`. -/
def t1 : (M.ι → A) →ₗ[A] ((tensorV M).ι → A) := bvec 1
/-- `slice 0` with domain written `(tensorV M).ι → A`. -/
def u0 : ((tensorV M).ι → A) →ₗ[A] (M.ι → A) := slice 0
/-- `slice 1` with domain written `(tensorV M).ι → A`. -/
def u1 : ((tensorV M).ι → A) →ₗ[A] (M.ι → A) := slice 1

@[simp] lemma u0_t0 (x : M.ι → A) : u0 M (t0 M x) = x := slice_bvec_self 0 x
@[simp] lemma u1_t1 (x : M.ι → A) : u1 M (t1 M x) = x := slice_bvec_self 1 x
@[simp] lemma u0_t1 (x : M.ι → A) : u0 M (t1 M x) = 0 := slice0_bvec1 x
@[simp] lemma u1_t0 (x : M.ι → A) : u1 M (t0 M x) = 0 := slice1_bvec0 x

lemma eq_t_u (f : (tensorV M).ι → A) : f = t0 M (u0 M f) + t1 M (u1 M f) := eq_bvec_slice f

lemma H_tensorV_bvec0 (m : M.ι → A) : H (tensorV M) (bvec 0 m) = bvec 0 (H M m + m) := by
  funext ⟨e, i⟩
  show ((wtV e + M.wt i : ℤ) : A) * _ = _
  fin_cases e
  · simp [Hop_apply]; ring
  · simp

lemma H_tensorV_bvec1 (m : M.ι → A) : H (tensorV M) (bvec 1 m) = bvec 1 (H M m - m) := by
  funext ⟨e, i⟩
  show ((wtV e + M.wt i : ℤ) : A) * _ = _
  fin_cases e
  · simp
  · simp [Hop_apply]; ring

lemma tauOp_t0 (c : ℤ) (m : M.ι → A) :
    tauOp (tensorV M) (c + 1) (t0 M m) = t0 M (tauOp M c m) + t1 M m := by
  have hF : (tensorV M).Fd 1 (bvec 0 m) = bvec 0 (M.Fd 1 m) + bvec 1 m := by
    rw [tensorV_Fd_b0 M 1 le_rfl, Nat.sub_self, M.isDP.P0_F]; rfl
  show tauOp (tensorV M) (c + 1) (bvec 0 m) = bvec 0 (tauOp M c m) + bvec 1 m
  rw [tauOp, LinearMap.sub_apply, LinearMap.add_apply, hF, LinearMap.smul_apply,
    Module.End.one_apply, H_tensorV_bvec0]
  funext ⟨e, i⟩
  fin_cases e
  · simp [tauOp]; ring
  · simp

lemma tauOp_t1 (c : ℤ) (m : M.ι → A) :
    tauOp (tensorV M) (c + 1) (t1 M m) = t1 M (tauOp M c m + (2 : A) • m) := by
  have hF : (tensorV M).Fd 1 (bvec 1 m) = bvec 1 (M.Fd 1 m) := tensorV_Fd_b1 M 1 m
  show tauOp (tensorV M) (c + 1) (bvec 1 m) = bvec 1 (tauOp M c m + (2 : A) • m)
  rw [tauOp, LinearMap.sub_apply, LinearMap.add_apply, hF, LinearMap.smul_apply,
    Module.End.one_apply, H_tensorV_bvec1]
  funext ⟨e, i⟩
  fin_cases e
  · simp
  · simp [tauOp]; ring

lemma aOp_tensorV_slots (c : ℤ) (B : ℕ) (hE : expF M (B + 1) = expF M B)
    (x0 x1 : M.ι → A) :
    aOp (tensorV M) (c + 1) (B + 1) (bvec 0 x0 + bvec 1 x1) =
      bvec 0 (aOp M c B x0) + bvec 1 (-aOp M c B (x0 + x1)) := by
  rw [aOp, LinearMap.comp_apply, map_add, Fold.expF_tensorV_bvec0, Fold.expF_tensorV_bvec1, hE,
    map_add, map_add, Fold.signOp_tensorV_bvec0, Fold.signOp_tensorV_bvec1,
    Fold.signOp_tensorV_bvec1, aOp, LinearMap.comp_apply, map_add, map_neg, map_add]
  abel

lemma aOp_t (c : ℤ) (B : ℕ) (hE : expF M (B + 1) = expF M B) (x0 x1 : M.ι → A) :
    aOp (tensorV M) (c + 1) (B + 1) (t0 M x0 + t1 M x1) =
      t0 M (aOp M c B x0) + t1 M (-aOp M c B (x0 + x1)) :=
  aOp_tensorV_slots M c B hE x0 x1

end slots

/-- the slot change `(u, v) ↦ (v − u, u)` (Part A2), with inverse `(p, q) ↦ (q, p + q)`. -/
def pi3 (L : Type*) [AddCommGroup L] [Module A L] : (L × L) ≃ₗ[A] (L × L) :=
  LinearEquiv.ofLinear
    (LinearMap.prod (LinearMap.snd A L L - LinearMap.fst A L L) (LinearMap.fst A L L))
    (LinearMap.prod (LinearMap.snd A L L) (LinearMap.fst A L L + LinearMap.snd A L L))
    (by apply LinearMap.ext; rintro ⟨p, q⟩; simp)
    (by apply LinearMap.ext; rintro ⟨p, q⟩; simp)

@[simp] lemma pi3_apply (L : Type*) [AddCommGroup L] [Module A L] (u v : L) :
    pi3 (A := A) L (u, v) = (v - u, u) := rfl

/-- the sum map `(x, y) ↦ x + y` (Part A1). -/
def sumMap (L : Type*) [AddCommGroup L] [Module A L] : (L × L) →ₗ[A] L :=
  LinearMap.fst A L L + LinearMap.snd A L L

@[simp] lemma sumMap_apply (L : Type*) [AddCommGroup L] [Module A L] (x y : L) :
    sumMap (A := A) L (x, y) = x + y := rfl

section phi

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (BN : ℕ)

/-! ### (A1) -/

/-- the map `M.ι → A → N.ι → A`, `β (x, y) ↦ x + y` (Part A1). -/
def piA1 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    ((phi N).ι → A) →ₗ[A] (N.ι → A) :=
  sumMap (N.ι → A) ∘ₗ (betaEquiv N BN hnil d B hB).symm.toLinearMap

lemma piA1_beta (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
    (x y : N.ι → A) : piA1 N BN hnil d B hB (beta N d B (x, y)) = x + y := by
  rw [← betaEquiv_coe N BN hnil d B hB]
  simp [piA1]

lemma exists_beta (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
    (w : (phi N).ι → A) : ∃ x y, w = beta N d B (x, y) := by
  obtain ⟨⟨x, y⟩, rfl⟩ := (betaEquiv N BN hnil d B hB).surjective w
  exact ⟨x, y, rfl⟩

lemma piA1_surjective (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    Function.Surjective (piA1 N BN hnil d B hB) := fun x =>
  ⟨beta N d B (x, 0), by rw [piA1_beta, add_zero]⟩

lemma piA1_tau (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    piA1 N BN hnil d B hB ∘ₗ tauOp (phi N) (2 * d + 1) =
      Psi N d BN ∘ₗ piA1 N BN hnil d B hB := by
  apply LinearMap.ext; intro w
  obtain ⟨x, y, rfl⟩ := exists_beta N BN hnil d B hB w
  obtain ⟨h1, -, h3⟩ := E5 N BN hnil d B hB
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, piA1_beta, piA1_beta, ← h3]
  simp only [LinearMap.add_apply, map_add]
  abel

lemma piA1_aOp (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    LinearMap.range (aOp (phi N) (2 * d + 1) B - 1) ≤ LinearMap.ker (piA1 N BN hnil d B hB) := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨x, y, rfl⟩ := exists_beta N BN hnil d B hB w
  obtain ⟨-, h2, -⟩ := E5 N BN hnil d B hB
  rw [LinearMap.mem_ker, LinearMap.sub_apply, h2, Module.End.one_apply, map_sub, piA1_beta,
    piA1_beta, add_comm, sub_self]

lemma piA1_ker (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    LinearMap.ker (piA1 N BN hnil d B hB) ≤
      LinearMap.range (tauOp (phi N) (2 * d + 1)) ⊔
        LinearMap.range (aOp (phi N) (2 * d + 1) B - 1) := by
  intro w hw
  obtain ⟨x, y, rfl⟩ := exists_beta N BN hnil d B hB w
  rw [LinearMap.mem_ker, piA1_beta] at hw
  obtain ⟨-, h2, -⟩ := E5 N BN hnil d B hB
  refine Submodule.mem_sup_right ⟨beta N d B (-x, 0), ?_⟩
  rw [LinearMap.sub_apply, h2, Module.End.one_apply, ← map_sub, eq_neg_of_add_eq_zero_right hw]
  congr 1
  simp

/-- **(A1)** of `C39_the_fold_on_the_half_lattice.md` (Lemma 10.4(a), general form): under (nil),
for every `d : ℤ` and `B ≥ 2 * BN`, an explicit `A`-linear equivalence
`Fold.Xbar (Doubling.phi N) (2 * d + 1) B ≃ₗ[A] (N.ι → A) ⧸ LinearMap.range (Psi N d BN)`
(the class of `β (x, y)` goes to the class of `x + y`). -/
def A1equiv (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    Fold.Xbar (phi N) (2 * d + 1) B ≃ₗ[A] (N.ι → A) ⧸ LinearMap.range (Psi N d BN) :=
  quotEquivOfIntertwine (piA1 N BN hnil d B hB) (piA1_surjective N BN hnil d B hB) _ _ _
    (piA1_tau N BN hnil d B hB) (piA1_aOp N BN hnil d B hB) (piA1_ker N BN hnil d B hB)

/-- **(A1)** of `C39_the_fold_on_the_half_lattice.md` (Lemma 10.4(a), general form): for `N`,
`BN` with (nil), every `d : ℤ` and every `B ≥ 2 * BN`,
`Fold.Xbar (Doubling.phi N) (2 * d + 1) B ≃ₗ[A] (N.ι → A) ⧸ LinearMap.range (Psi N d BN)`. -/
theorem A1 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    Nonempty (Fold.Xbar (phi N) (2 * d + 1) B ≃ₗ[A] (N.ι → A) ⧸ LinearMap.range (Psi N d BN)) :=
  ⟨A1equiv N BN hnil d B hB⟩

/-! ### (A2) -/

/-- (A2) `ψ (b₀ u₀ + b₁ u₁) = u₀ + (1 − a) u₁`, `a = aOp (phi N) (2d + 1) B`. -/
def psiA2 (d : ℤ) (B : ℕ) : ((tensorV (phi N)).ι → A) →ₗ[A] ((phi N).ι → A) :=
  u0 (phi N) + (1 - aOp (phi N) (2 * d + 1) B) ∘ₗ u1 (phi N)

lemma psiA2_t (d : ℤ) (B : ℕ) (x0 x1 : (phi N).ι → A) :
    psiA2 N d B (t0 (phi N) x0 + t1 (phi N) x1) =
      x0 + (1 - aOp (phi N) (2 * d + 1) B) x1 := by
  simp [psiA2]

/-- (A2) `f = 1 + tauOp_M − aOp_M`. -/
def fA2 (d : ℤ) (B : ℕ) : Module.End A ((phi N).ι → A) :=
  1 + tauOp (phi N) (2 * d + 1) - aOp (phi N) (2 * d + 1) B

/-- (A2) the full map `V ⊗ M → N ⊕ N`: `ψ`, then `β⁻¹`, then `(u, v) ↦ (v − u, u)`. -/
def piA2 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    ((tensorV (phi N)).ι → A) →ₗ[A] (N.ι → A) × (N.ι → A) :=
  ((betaEquiv N BN hnil d B hB).symm.trans (pi3 (N.ι → A))).toLinearMap ∘ₗ psiA2 N d B

omit [IsDomain A] [CharZero A] [OddUnits A] in
lemma psi_succ_eq (d : ℤ) :
    Psi N (d + 1) BN = PE N BN d - QE N BN d + (2 : A) • 1 := by
  simp only [Psi, PE, QE, parOp_succ, sub_neg_eq_add, add_mul]
  push_cast
  module

omit [IsDomain A] [CharZero A] [OddUnits A] in
lemma zop_eq (d : ℤ) : Zop N d BN = QE N BN d - 1 := by
  simp only [Zop, QE]; abel

section A2

variable (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
include hnil hB

lemma aOp_T_slots (x0 x1 : (phi N).ι → A) :
    aOp (tensorV (phi N)) (2 * d + 1 + 1) (B + 1) (t0 (phi N) x0 + t1 (phi N) x1) =
      t0 (phi N) (aOp (phi N) (2 * d + 1) B x0) +
        t1 (phi N) (-aOp (phi N) (2 * d + 1) B (x0 + x1)) :=
  aOp_t _ _ _ (by rw [expF_phi_eq N BN hnil _ (by omega), expF_phi_eq N BN hnil B hB]) x0 x1

lemma psiA2_tau :
    psiA2 N d B ∘ₗ tauOp (tensorV (phi N)) (2 * d + 1 + 1) = fA2 N d B ∘ₗ psiA2 N d B := by
  obtain ⟨hsq, hcomm⟩ := E3 N BN hnil d B hB
  have ha : ∀ v, aOp (phi N) (2 * d + 1) B (aOp (phi N) (2 * d + 1) B v) = v :=
    fun v => by simpa using LinearMap.congr_fun hsq v
  have hc : ∀ v, tauOp (phi N) (2 * d + 1) (aOp (phi N) (2 * d + 1) B v) =
      aOp (phi N) (2 * d + 1) B (tauOp (phi N) (2 * d + 1) v) :=
    fun v => (LinearMap.congr_fun hcomm v).symm
  apply LinearMap.ext; intro w
  rw [eq_t_u (phi N) w]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, map_add, tauOp_t0, tauOp_t1, add_assoc,
    ← map_add, psiA2_t, psiA2_t, fA2]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, map_add, map_sub,
    map_smul, ha, hc]
  module

lemma psiA2_aOp :
    LinearMap.range (aOp (tensorV (phi N)) (2 * d + 1 + 1) (B + 1) - 1) ≤
      LinearMap.ker (piA2 N BN hnil d B hB) := by
  obtain ⟨hsq, -⟩ := E3 N BN hnil d B hB
  have hsq' : ∀ v, aOp (phi N) (2 * d + 1) B (aOp (phi N) (2 * d + 1) B v) = v :=
    fun v => by simpa using LinearMap.congr_fun hsq v
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker, piA2, LinearMap.comp_apply]
  have h0 : psiA2 N d B ((aOp (tensorV (phi N)) (2 * d + 1 + 1) (B + 1) - 1) w) = 0 := by
    rw [eq_t_u (phi N) w, LinearMap.sub_apply, aOp_T_slots N BN hnil d B hB, Module.End.one_apply,
      show ∀ p q r s : ((tensorV (phi N)).ι → A), p + q - (r + s) = (p - r) + (q - s) from
        fun p q r s => by abel, ← map_sub, ← map_sub, psiA2_t]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_neg, map_add, hsq']
    abel
  rw [h0, map_zero]

lemma piA2_ker :
    LinearMap.ker (piA2 N BN hnil d B hB) ≤
      LinearMap.range (tauOp (tensorV (phi N)) (2 * d + 1 + 1)) ⊔
        LinearMap.range (aOp (tensorV (phi N)) (2 * d + 1 + 1) (B + 1) - 1) := by
  intro w hw
  rw [LinearMap.mem_ker, piA2, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff] at hw
  refine Submodule.mem_sup_right ⟨t0 (phi N) (u1 (phi N) w) + t1 (phi N) (-u1 (phi N) w), ?_⟩
  rw [LinearMap.sub_apply, aOp_T_slots N BN hnil d B hB, Module.End.one_apply, add_neg_cancel,
    map_zero, neg_zero, map_zero, add_zero]
  rw [eq_t_u (phi N) w, psiA2_t, add_eq_zero_iff_eq_neg] at hw
  conv_rhs => rw [eq_t_u (phi N) w, hw]
  simp only [map_neg, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  abel

lemma piA2_surjective : Function.Surjective (piA2 N BN hnil d B hB) := by
  intro p
  obtain ⟨m, hm⟩ := ((betaEquiv N BN hnil d B hB).symm.trans (pi3 (N.ι → A))).surjective p
  refine ⟨t0 (phi N) m + t1 (phi N) 0, ?_⟩
  rw [piA2, LinearMap.comp_apply, psiA2_t, map_zero, add_zero, LinearEquiv.coe_coe, hm]

lemma piA2_tau :
    piA2 N BN hnil d B hB ∘ₗ tauOp (tensorV (phi N)) (2 * d + 1 + 1) =
      glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN) ∘ₗ piA2 N BN hnil d B hB := by
  obtain ⟨h1, h2, h3⟩ := E5 N BN hnil d B hB
  rw [piA2, LinearMap.comp_assoc, psiA2_tau N BN hnil d B hB, ← LinearMap.comp_assoc,
    ← LinearMap.comp_assoc (psiA2 N d B)]
  congr 1
  apply LinearMap.ext; intro m
  obtain ⟨x, y, rfl⟩ := exists_beta N BN hnil d B hB m
  have hf : fA2 N d B (beta N d B (x, y)) =
      beta N d B (x + PE N BN d x + QE N BN d y - y, y + QE N BN d x + PE N BN d y - x) := by
    rw [fA2, LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, h1, h2, ← map_add,
      ← map_sub]
    congr 1
    ext <;> simp <;> abel
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [hf, ← betaEquiv_coe N BN hnil d B hB, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, pi3_apply, pi3_apply, glueOp_apply, psi_succ_eq N BN d,
    zop_eq N BN d, ← h3]
  refine Prod.ext ?_ ?_
  · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub]
    module
  · simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    abel

end A2

/-- (A2) with the bound written `B + 1` and the centre `2 * d + 1 + 1`. -/
def A2equiv' (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    Fold.Xbar (tensorV (phi N)) (2 * d + 1 + 1) (B + 1) ≃ₗ[A]
      ((N.ι → A) × (N.ι → A)) ⧸
        LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN)) :=
  quotEquivOfIntertwine (piA2 N BN hnil d B hB) (piA2_surjective N BN hnil d B hB) _ _ _
    (piA2_tau N BN hnil d B hB) (psiA2_aOp N BN hnil d B hB) (piA2_ker N BN hnil d B hB)

/-- **(A2)** of `C39_the_fold_on_the_half_lattice.md` (Lemma 10.5(a), general form): under (nil),
for every `d : ℤ` and every `B ≥ 2 * BN + 1`, an explicit `A`-linear equivalence
`Fold.Xbar (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2) B ≃ₗ[A]
((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN))`. -/
def A2equiv (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN + 1 ≤ B) :
    Fold.Xbar (DPLattice.tensorV (phi N)) (2 * d + 2) B ≃ₗ[A]
      ((N.ι → A) × (N.ι → A)) ⧸
        LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN)) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [show (2 * d + 1 + 1 : ℤ) = 2 * d + 2 by ring, show B - 1 + 1 = B by omega])).trans
    (A2equiv' N BN hnil d (B - 1) (by omega))

/-- **(A2)** of `C39_the_fold_on_the_half_lattice.md` (Lemma 10.5(a), general form): for `N`,
`BN` with (nil), every `d : ℤ` and every `B ≥ 2 * BN + 1`,
`Fold.Xbar (DPLattice.tensorV (Doubling.phi N)) (2 * d + 2) B ≃ₗ[A]
((N.ι → A) × (N.ι → A)) ⧸ LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN))`. -/
theorem A2 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN + 1 ≤ B) :
    Nonempty (Fold.Xbar (DPLattice.tensorV (phi N)) (2 * d + 2) B ≃ₗ[A]
      ((N.ι → A) × (N.ι → A)) ⧸
        LinearMap.range (glueOp (Psi N (d + 1) BN) (Psi N d BN) (Zop N d BN))) :=
  ⟨A2equiv N BN hnil d B hB⟩

end phi

/-! ### (A3) -/

section A3

variable (A) [IsDomain A] [CharZero A] [OddUnits A]

lemma wtV_bound (e : Fin 2) : -1 ≤ wtV e ∧ wtV e ≤ 1 := by
  fin_cases e <;> simp [wtV]

lemma T_wt_bound (l : ℕ) : ∀ i : (Filt.T A l).ι, -(l : ℤ) ≤ (Filt.T A l).wt i ∧
    (Filt.T A l).wt i ≤ l := by
  induction l using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [Filt.T_zero]
      intro i; exact ⟨le_refl _, le_refl _⟩
    · obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
      · rw [Filt.T_odd]
        rintro ⟨e, i⟩
        have h1 := ih l (by omega) i
        have h2 := wtV_bound e
        show -((2 * l + 1 : ℕ) : ℤ) ≤ 2 * (Filt.T A l).wt i + wtV e ∧
          2 * (Filt.T A l).wt i + wtV e ≤ ((2 * l + 1 : ℕ) : ℤ)
        push_cast; constructor <;> omega
      · rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring, Filt.T_even]
        rintro ⟨e, e', i⟩
        have h1 := ih l (by omega) i
        have h2 := wtV_bound e
        have h3 := wtV_bound e'
        show -((2 * l + 2 : ℕ) : ℤ) ≤ wtV e + (2 * (Filt.T A l).wt i + wtV e') ∧
          wtV e + (2 * (Filt.T A l).wt i + wtV e') ≤ ((2 * l + 2 : ℕ) : ℤ)
        push_cast; constructor <;> omega

/-- **(A3)** of `C39_the_fold_on_the_half_lattice.md` (nilpotence on the dance lattices): over
`A` with `[IsDomain A] [CharZero A] [Doubling.OddUnits A]`, every weight of `Filt.T A l` lies in
`[−l, l]`, and `∀ s ≥ l + 1, (Filt.T A l).Fd s = 0` (via C24 `Lemma35.Fd_eq_zero_of_bound`). -/
theorem A3 (l : ℕ) :
    (∀ i : (Filt.T A l).ι, -(l : ℤ) ≤ (Filt.T A l).wt i ∧ (Filt.T A l).wt i ≤ l) ∧
    ∀ s ≥ l + 1, (Filt.T A l).Fd s = 0 :=
  ⟨T_wt_bound A l, fun s hs =>
    Lemma35.Fd_eq_zero_of_bound (Filt.T A l) l (T_wt_bound A l) s (by omega)⟩

end A3

/-! ### (A4) -/

/-- **(A4)** of `C39_the_fold_on_the_half_lattice.md`, odd families: with
`N := Filt.T ℤ_[2] l`, `BN := l + 1`, for every `j`,
`FoldGroup.XbarFam (2 * l + 1) j ≃ₗ[ℤ_[2]] (N.ι → ℤ_[2]) ⧸ range (Psi N (l + j) (l + 1))`. -/
theorem A4_odd (l j : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃ₗ[ℤ_[2]]
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range (Psi (Filt.T ℤ_[2] l) (l + j) (l + 1))) := by
  unfold FoldGroup.XbarFam
  rw [Filt.T_odd, show (((2 * l + 1 : ℕ) : ℤ) + 2 * (j : ℤ)) = 2 * ((l : ℤ) + j) + 1 by
    push_cast; ring]
  exact A1 _ _ (A3 ℤ_[2] l).2 _ _ (by omega)

/-- **(A4)** of `C39_the_fold_on_the_half_lattice.md`, even families: with
`N := Filt.T ℤ_[2] l`, `BN := l + 1`, for every `i`,
`FoldGroup.XbarFam (2 * l + 2) i ≃ₗ[ℤ_[2]] ((N.ι → ℤ_[2]) × (N.ι → ℤ_[2])) ⧸
range (glueOp (Psi N (l + i + 1) (l + 1)) (Psi N (l + i) (l + 1)) (Zop N (l + i) (l + 1)))`. -/
theorem A4_even (l i : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
        LinearMap.range (glueOp (Psi (Filt.T ℤ_[2] l) (l + i + 1) (l + 1))
          (Psi (Filt.T ℤ_[2] l) (l + i) (l + 1)) (Zop (Filt.T ℤ_[2] l) (l + i) (l + 1)))) := by
  unfold FoldGroup.XbarFam
  rw [Filt.T_even, show (((2 * l + 2 : ℕ) : ℤ) + 2 * (i : ℤ)) = 2 * ((l : ℤ) + i) + 2 by
    push_cast; ring]
  exact A2 _ _ (A3 ℤ_[2] l).2 _ _ (by omega)

/-- **(A4)** of `C39_the_fold_on_the_half_lattice.md` (the families over `ℤ_[2]`), both cases
together (`N := Filt.T ℤ_[2] l`, `BN := l + 1`). -/
theorem A4 (l : ℕ) :
    (∀ j : ℕ, Nonempty (FoldGroup.XbarFam (2 * l + 1) j ≃ₗ[ℤ_[2]]
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸ LinearMap.range (Psi (Filt.T ℤ_[2] l) (l + j) (l + 1)))) ∧
    (∀ i : ℕ, Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
        LinearMap.range (glueOp (Psi (Filt.T ℤ_[2] l) (l + i + 1) (l + 1))
          (Psi (Filt.T ℤ_[2] l) (l + i) (l + 1)) (Zop (Filt.T ℤ_[2] l) (l + i) (l + 1))))) :=
  ⟨A4_odd l, A4_even l⟩

end FoldHalf
