module

public import RequestProject.FoldHalf.PartS

/-!
# `C39_the_fold_on_the_half_lattice.md`: Part E — the antipode on `Φ(N)`

Here `M = Doubling.phi N` (basis `Fin 2 × N.ι`; the vector with `n` in slot `e` is C18's
`bvec e n`), `c = 2d + 1`, and `B ≥ 2 * BN`. `Doubling.phi` is only defined over a ring with
`[IsDomain A] [CharZero A] [OddUnits A]` (C20), so Part E assumes these instances.

Internally, `b0 N = bvec 0`, `b1 N = bvec 1`, `s0 N = slice 0`, `s1 N = slice 1` are the same
maps with the vector space of `M` written `(phi N).ι → A` (definitionally `Fin 2 × N.ι → A`).

* (E0) `E0`; (E1) `E1`; (E2) `E2`; (E3) `E3`;
* (E4) `beta N d B (x, y) = bvec 0 x + aOp M c B (bvec 0 y)` (`beta`, a linear map; in
  `beta_apply` the `id` only fixes the ambient type `(phi N).ι → A` of the sum) is a linear
  equivalence: `betaEquiv` (with `betaEquiv_apply`) and `E4`;
* (E5) `E5`, with `PE N BN d := ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + Ch N BN * ShInv N BN` and
  `QE N BN d := −(parOp N d * ShInv N BN)` (the file's `P` and `Q`).
-/

@[expose] public section

noncomputable section

namespace FoldHalf

open DPLattice Doubling Finset Fold

variable {A : Type*} [CommRing A]

/-! ### Operator identities from (S1), (S2) -/

section ops

variable {N : DPLattice A} {BN : ℕ}

/-- the operator identities of (S1), (S2) used in Parts E and A -/
structure OpFacts (N : DPLattice A) (BN : ℕ) (d : ℤ) : Prop where
  PP : parOp N d * parOp N d = 1
  ShSi : Sh N BN * ShInv N BN = 1
  SiSh : ShInv N BN * Sh N BN = 1
  PCh : parOp N d * Ch N BN = Ch N BN * parOp N d
  PSh : parOp N d * Sh N BN = Sh N BN * parOp N d
  PSi : parOp N d * ShInv N BN = ShInv N BN * parOp N d
  ChSi : Ch N BN * ShInv N BN = ShInv N BN * Ch N BN

lemma opFacts [OddUnits A] (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) : OpFacts N BN d :=
  ⟨parOp_mul_self N d, (S1 N BN hnil).2.1, (S1 N BN hnil).2.2, parOp_commute_Ch N BN d,
    parOp_commute_Sh N BN d, parOp_commute_ShInv N BN d, Ch_commute_ShInv N BN⟩

lemma OpFacts.PChPSi {d : ℤ} (h : OpFacts N BN d) :
    parOp N d * Ch N BN * (parOp N d * ShInv N BN) = Ch N BN * ShInv N BN := by
  rw [h.PCh, mul_assoc, ← mul_assoc (parOp N d), h.PP, one_mul]

lemma OpFacts.PShPSi {d : ℤ} (h : OpFacts N BN d) :
    parOp N d * Sh N BN * (parOp N d * ShInv N BN) = 1 := by
  rw [h.PSh, mul_assoc, ← mul_assoc (parOp N d), h.PP, one_mul, h.ShSi]

lemma OpFacts.PChSiP {d : ℤ} (h : OpFacts N BN d) :
    parOp N d * Ch N BN * (ShInv N BN * parOp N d) = Ch N BN * ShInv N BN := by
  rw [← h.PSi]; exact h.PChPSi

lemma OpFacts.PShSiP {d : ℤ} (h : OpFacts N BN d) :
    parOp N d * Sh N BN * (ShInv N BN * parOp N d) = 1 := by
  rw [← h.PSi]; exact h.PShPSi

lemma OpFacts.ChSiPSh {d : ℤ} (h : OpFacts N BN d) :
    Ch N BN * ShInv N BN * (parOp N d * Sh N BN) = parOp N d * Ch N BN := by
  rw [h.PSh, ← mul_assoc, mul_assoc (Ch N BN), h.SiSh, mul_one, h.PCh]

lemma OpFacts.SiPPSh {d : ℤ} (h : OpFacts N BN d) :
    ShInv N BN * parOp N d * (parOp N d * Sh N BN) = 1 := by
  rw [mul_assoc, ← mul_assoc (parOp N d), h.PP, one_mul, h.SiSh]

end ops

lemma Ch_succ (N : DPLattice A) (k : ℕ) : Ch N (k + 1) = Ch N k + dfi (A := A) k • N.Fd k := by
  simp [Ch, sum_range_succ]

lemma Sh_succ (N : DPLattice A) (k : ℕ) :
    Sh N (k + 1) = Sh N k + dfi (A := A) (k + 1) • N.Fd k := by
  simp [Sh, sum_range_succ]

section phi

variable [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (BN : ℕ)

/-! ### The slots of `Φ(N)` -/

/-- `bvec 0` with codomain written `(phi N).ι → A`. -/
def b0 : (N.ι → A) →ₗ[A] ((phi N).ι → A) := bvec 0
/-- `bvec 1` with codomain written `(phi N).ι → A`. -/
def b1 : (N.ι → A) →ₗ[A] ((phi N).ι → A) := bvec 1
/-- `slice 0` with domain written `(phi N).ι → A`. -/
def s0 : ((phi N).ι → A) →ₗ[A] (N.ι → A) := slice 0
/-- `slice 1` with domain written `(phi N).ι → A`. -/
def s1 : ((phi N).ι → A) →ₗ[A] (N.ι → A) := slice 1

@[simp] lemma s0_b0 (x : N.ι → A) : s0 N (b0 N x) = x := slice_bvec_self 0 x
@[simp] lemma s1_b1 (x : N.ι → A) : s1 N (b1 N x) = x := slice_bvec_self 1 x
@[simp] lemma s0_b1 (x : N.ι → A) : s0 N (b1 N x) = 0 := slice0_bvec1 x
@[simp] lemma s1_b0 (x : N.ι → A) : s1 N (b0 N x) = 0 := slice1_bvec0 x

lemma eq_b_s (f : (phi N).ι → A) : f = b0 N (s0 N f) + b1 N (s1 N f) := eq_bvec_slice f

lemma b_ext {f g : (phi N).ι → A} (h0 : s0 N f = s0 N g) (h1 : s1 N f = s1 N g) : f = g :=
  ext_slice h0 h1

lemma phiFd_even_b0 (s : ℕ) (n : N.ι → A) :
    (phi N).Fd (2 * s) (b0 N n) = dfi (A := A) s • b0 N (N.Fd s n) := (B3 N s n).1 0

lemma phiFd_even_b1 (s : ℕ) (n : N.ι → A) :
    (phi N).Fd (2 * s) (b1 N n) = dfi (A := A) s • b1 N (N.Fd s n) := (B3 N s n).1 1

lemma phiFd_odd_b0' (s : ℕ) (n : N.ι → A) :
    (phi N).Fd (2 * s + 1) (b0 N n) = dfi (A := A) (s + 1) • b1 N (N.Fd s n) := (B3 N s n).2.1

lemma phiFd_odd_b1' (s : ℕ) (n : N.ι → A) :
    (phi N).Fd (2 * s + 1) (b1 N n) =
      (((2 * s + 2 : ℕ) : A) * dfi (s + 1)) • b0 N (N.Fd (s + 1) n) := (B3 N s n).2.2

lemma phiF1_b0 (n : N.ι → A) : (phi N).Fd 1 (b0 N n) = b1 N n := (B1 N).1 n

lemma signOp_b0 (d : ℤ) (x : N.ι → A) :
    signOp (phi N) (2 * d + 1) (b0 N x) = b0 N (parOp N d x) := by
  funext ⟨e, i⟩
  rw [signOp_apply]
  show (-1 : A) ^ ((2 * d + 1 - (2 * N.wt i + wtV e)) / 2).natAbs * bvec 0 x (e, i) =
    bvec 0 (parOp N d x) (e, i)
  fin_cases e
  · simp only [Fin.zero_eta, wtV_zero, bvec_apply, if_true, parOp_apply]
    rw [show 2 * d + 1 - (2 * N.wt i + 1) = 2 * (d - N.wt i) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  · simp

lemma signOp_b1 (d : ℤ) (x : N.ι → A) :
    signOp (phi N) (2 * d + 1) (b1 N x) = -b1 N (parOp N d x) := by
  funext ⟨e, i⟩
  rw [signOp_apply]
  show (-1 : A) ^ ((2 * d + 1 - (2 * N.wt i + wtV e)) / 2).natAbs * bvec 1 x (e, i) =
    -bvec 1 (parOp N d x) (e, i)
  fin_cases e
  · simp
  · simp only [Fin.mk_one, wtV_one, bvec_apply, if_true, parOp_apply]
    rw [show 2 * d + 1 - (2 * N.wt i + -1) = 2 * ((d - N.wt i) + 1) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num), Fold.neg_one_pow_natAbs_add_one]
    ring

lemma H_b0 (x : N.ι → A) : H (phi N) (b0 N x) = b0 N ((2 : A) • H N x + x) := by
  funext ⟨e, i⟩
  show ((2 * N.wt i + wtV e : ℤ) : A) * bvec 0 x (e, i) = bvec 0 ((2 : A) • H N x + x) (e, i)
  fin_cases e
  · simp [Hop_apply]; ring
  · simp

/-! ### (E0)–(E3) -/

lemma phi_Fd_b0_zero (hnil : ∀ s ≥ BN, N.Fd s = 0) (r : ℕ) (hr : 2 * BN ≤ r)
    (n : N.ι → A) : (phi N).Fd r (b0 N n) = 0 := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [phiFd_even_b0, hnil s (by omega), LinearMap.zero_apply, map_zero, smul_zero]
  · rw [phiFd_odd_b0', hnil s (by omega), LinearMap.zero_apply, map_zero, smul_zero]

lemma phi_Fd_b1_zero (hnil : ∀ s ≥ BN, N.Fd s = 0) (r : ℕ) (hr : 2 * BN ≤ r)
    (n : N.ι → A) : (phi N).Fd r (b1 N n) = 0 := by
  obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' r
  · rw [phiFd_even_b1, hnil s (by omega), LinearMap.zero_apply, map_zero, smul_zero]
  · rw [phiFd_odd_b1', hnil (s + 1) (by omega), LinearMap.zero_apply, map_zero, smul_zero]

/-- **(E0)** of `C39_the_fold_on_the_half_lattice.md`: under (nil),
`∀ r ≥ 2 * BN, (Doubling.phi N).Fd r = 0`. -/
theorem E0 (hnil : ∀ s ≥ BN, N.Fd s = 0) : ∀ r ≥ 2 * BN, (phi N).Fd r = 0 := by
  intro r hr
  apply LinearMap.ext; intro f
  rw [eq_b_s N f, map_add, phi_Fd_b0_zero N BN hnil r hr, phi_Fd_b1_zero N BN hnil r hr,
    add_zero, LinearMap.zero_apply]

lemma expF_phi_eq (hnil : ∀ s ≥ BN, N.Fd s = 0) (B : ℕ) (hB : 2 * BN ≤ B) :
    expF (phi N) B = expF (phi N) (2 * BN) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  rw [expF, expF, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range k) (fun r _ => E0 N BN hnil _ (by omega)), add_zero]

lemma expF_phi_two_mul_b0 (k : ℕ) (n : N.ι → A) :
    expF (phi N) (2 * k) (b0 N n) = b0 N (Ch N k n) + b1 N (Sh N k n) := by
  induction k with
  | zero => simp [expF, Ch, Sh]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, expF, sum_range_succ, sum_range_succ, ← expF,
      LinearMap.add_apply, LinearMap.add_apply, ih, phiFd_even_b0, phiFd_odd_b0', Ch_succ,
      Sh_succ]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]
    abel

lemma E1' (hnil : ∀ s ≥ BN, N.Fd s = 0) (B : ℕ) (hB : 2 * BN ≤ B) (n : N.ι → A) :
    Fold.expF (phi N) B (b0 N n) = b0 N (Ch N BN n) + b1 N (Sh N BN n) := by
  rw [expF_phi_eq N BN hnil B hB, expF_phi_two_mul_b0]

/-- **(E1)** of `C39_the_fold_on_the_half_lattice.md`: for `B ≥ 2 * BN`,
`Fold.expF M B (bvec 0 n) = bvec 0 (Ch N BN n) + bvec 1 (Sh N BN n)` (`M = Doubling.phi N`). -/
theorem E1 (hnil : ∀ s ≥ BN, N.Fd s = 0) (B : ℕ) (hB : 2 * BN ≤ B) (n : N.ι → A) :
    Fold.expF (phi N) B (bvec 0 n) = bvec 0 (Ch N BN n) + bvec 1 (Sh N BN n) :=
  E1' N BN hnil B hB n

lemma E2' (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) (n : N.ι → A) :
    Fold.aOp (phi N) (2 * d + 1) B (b0 N n) =
      b0 N (parOp N d (Ch N BN n)) - b1 N (parOp N d (Sh N BN n)) := by
  rw [aOp, LinearMap.comp_apply, E1' N BN hnil B hB, map_add, signOp_b0, signOp_b1,
    sub_eq_add_neg]

/-- **(E2)** of `C39_the_fold_on_the_half_lattice.md`: for `B ≥ 2 * BN`,
`Fold.aOp M (2d + 1) B (bvec 0 n) = bvec 0 (parOp N d (Ch N BN n)) − bvec 1 (parOp N d (Sh N BN n))`. -/
theorem E2 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) (n : N.ι → A) :
    Fold.aOp (phi N) (2 * d + 1) B (bvec 0 n) =
      bvec 0 (parOp N d (Ch N BN n)) - bvec 1 (parOp N d (Sh N BN n)) :=
  E2' N BN hnil d B hB n

/-- **(E3)** of `C39_the_fold_on_the_half_lattice.md`: for `B ≥ 2 * BN`,
`Fold.aOp M c B * Fold.aOp M c B = 1` and `Fold.aOp M c B * Fold.tauOp M c = Fold.tauOp M c *
Fold.aOp M c B` (`M = Doubling.phi N`, `c = 2d + 1`). -/
theorem E3 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    Fold.aOp (phi N) (2 * d + 1) B * Fold.aOp (phi N) (2 * d + 1) B = 1 ∧
    Fold.aOp (phi N) (2 * d + 1) B * Fold.tauOp (phi N) (2 * d + 1) =
      Fold.tauOp (phi N) (2 * d + 1) * Fold.aOp (phi N) (2 * d + 1) B := by
  have hB' : ∀ r ≥ B, (phi N).Fd r = 0 := fun r hr => E0 N BN hnil r (by omega)
  exact ⟨aOp_mul_self _ _ _ hB', aOp_comm_tauOp _ _ _ hB'⟩

/-! ### (E4) -/

/-- **(E4)** of `C39_the_fold_on_the_half_lattice.md`: the linear map
`β (x, y) := bvec 0 x + Fold.aOp M (2d + 1) B (bvec 0 y)` (`M = Doubling.phi N`). -/
def beta (d : ℤ) (B : ℕ) : (N.ι → A) × (N.ι → A) →ₗ[A] ((phi N).ι → A) :=
  b0 N ∘ₗ LinearMap.fst A _ _ + (aOp (phi N) (2 * d + 1) B ∘ₗ b0 N) ∘ₗ LinearMap.snd A _ _

lemma beta_apply' (d : ℤ) (B : ℕ) (x y : N.ι → A) :
    beta N d B (x, y) = b0 N x + aOp (phi N) (2 * d + 1) B (b0 N y) := rfl

/-- (E4) `β (x, y) = bvec 0 x + Fold.aOp M (2d + 1) B (bvec 0 y)` (the `id` only fixes the
ambient type `(phi N).ι → A` of the sum). -/
lemma beta_apply (d : ℤ) (B : ℕ) (x y : N.ι → A) :
    beta N d B (x, y) = (id (bvec 0 x) : (phi N).ι → A) + aOp (phi N) (2 * d + 1) B (bvec 0 y) :=
  rfl

/-- The inverse of `β` (Part E4): `f ↦ (f₀ + Ch·ShInv f₁, −ShInv·parOp f₁)` on the slots. -/
def betaInv (d : ℤ) : ((phi N).ι → A) →ₗ[A] (N.ι → A) × (N.ι → A) :=
  LinearMap.prod (s0 N + (Ch N BN * ShInv N BN) ∘ₗ s1 N) (-(ShInv N BN * parOp N d) ∘ₗ s1 N)

lemma betaInv_b (d : ℤ) (u v : N.ι → A) :
    betaInv N BN d (b0 N u + b1 N v) =
      (u + Ch N BN (ShInv N BN v), -ShInv N BN (parOp N d v)) := by
  simp [betaInv]

lemma slices_beta (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
    (x y : N.ι → A) :
    beta N d B (x, y) = b0 N (x + parOp N d (Ch N BN y)) + b1 N (-parOp N d (Sh N BN y)) := by
  rw [beta_apply', E2' N BN hnil d B hB, map_add, map_neg]
  abel

/-- **(E4)** of `C39_the_fold_on_the_half_lattice.md`: `β` as an `A`-linear equivalence
`(N.ι → A) × (N.ι → A) ≃ₗ[A] (M.ι → A)` (`M = Doubling.phi N`, `B ≥ 2 * BN`). -/
def betaEquiv (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    ((N.ι → A) × (N.ι → A)) ≃ₗ[A] ((phi N).ι → A) :=
  LinearEquiv.ofLinear (beta N d B) (betaInv N BN d)
    (by
      have h := opFacts hnil d
      apply LinearMap.ext; intro f
      rw [eq_b_s N f]
      have e1 := LinearMap.congr_fun h.PChSiP (s1 N f)
      have e2 := LinearMap.congr_fun h.PShSiP (s1 N f)
      simp only [Module.End.mul_apply, Module.End.one_apply] at e1 e2
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [betaInv_b, slices_beta N BN hnil d B hB]
      simp only [map_neg, e1, e2, neg_neg, add_neg_cancel_right])
    (by
      have h := opFacts hnil d
      apply LinearMap.ext; rintro ⟨x, y⟩
      have e1 := LinearMap.congr_fun h.ChSiPSh y
      have e2 := LinearMap.congr_fun h.SiPPSh y
      simp only [Module.End.mul_apply, Module.End.one_apply] at e1 e2
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [slices_beta N BN hnil d B hB, betaInv_b]
      simp only [map_neg, e1, e2, neg_neg, add_neg_cancel_right])

lemma betaEquiv_coe (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    ⇑(betaEquiv N BN hnil d B hB) = beta N d B := rfl

lemma betaEquiv_apply (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
    (x y : N.ι → A) :
    betaEquiv N BN hnil d B hB (x, y) =
      (id (bvec 0 x) : (phi N).ι → A) + Fold.aOp (phi N) (2 * d + 1) B (bvec 0 y) :=
  rfl

/-- **(E4)** of `C39_the_fold_on_the_half_lattice.md` (freeness): for `B ≥ 2 * BN`, the map
`β (x, y) = bvec 0 x + Fold.aOp M (2d + 1) B (bvec 0 y)` is an `A`-linear equivalence
`(N.ι → A) × (N.ι → A) ≃ₗ[A] (M.ι → A)`, `M = Doubling.phi N` (the `id` only fixes the ambient
type `(phi N).ι → A` of the sum). -/
theorem E4 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    ∃ β : ((N.ι → A) × (N.ι → A)) ≃ₗ[A] ((phi N).ι → A),
      ∀ x y, β (x, y) = (id (bvec 0 x) : (phi N).ι → A) +
        Fold.aOp (phi N) (2 * d + 1) B (bvec 0 y) :=
  ⟨betaEquiv N BN hnil d B hB, betaEquiv_apply N BN hnil d B hB⟩

/-! ### (E5) -/

/-- (E5) the operator `P := ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + Ch N BN * ShInv N BN`. -/
def PE (d : ℤ) : Module.End A (N.ι → A) :=
  ((2 * d : ℤ) : A) • 1 - (2 : A) • H N + Ch N BN * ShInv N BN

/-- (E5) the operator `Q := −(parOp N d * ShInv N BN)`. -/
def QE (d : ℤ) : Module.End A (N.ι → A) := -(parOp N d * ShInv N BN)

lemma tauOp_phi_b0 (d : ℤ) (x : N.ι → A) :
    tauOp (phi N) (2 * d + 1) (b0 N x) =
      b0 N ((((2 * d : ℤ) : A) • 1 - (2 : A) • H N) x) + b1 N x := by
  rw [tauOp, LinearMap.sub_apply, LinearMap.add_apply, phiF1_b0, LinearMap.smul_apply,
    Module.End.one_apply, H_b0]
  apply b_ext N
  · simp only [map_sub, map_add, map_smul, s0_b0, s0_b1, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    push_cast
    module
  · simp

lemma tauOp_beta_left (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B)
    (x : N.ι → A) :
    tauOp (phi N) (2 * d + 1) (b0 N x) = beta N d B (PE N BN d x, QE N BN d x) := by
  have h := opFacts hnil d
  rw [slices_beta N BN hnil d B hB, tauOp_phi_b0]
  have e1 := LinearMap.congr_fun h.PChPSi x
  have e2 := LinearMap.congr_fun h.PShPSi x
  simp only [Module.End.mul_apply, Module.End.one_apply] at e1 e2
  simp only [PE, QE, LinearMap.neg_apply, Module.End.mul_apply, map_neg, e1, e2, neg_neg,
    LinearMap.add_apply]
  congr 2
  abel

/-- **(E5)** of `C39_the_fold_on_the_half_lattice.md` (the circulant matrix): with
`P = PE N BN d = ((2 * d : ℤ) : A) • 1 − (2 : A) • H N + Ch N BN * ShInv N BN` and
`Q = QE N BN d = −(parOp N d * ShInv N BN)`, for `B ≥ 2 * BN`:
`Fold.tauOp M c (β (x, y)) = β (P x + Q y, Q x + P y)`, `Fold.aOp M c B (β (x, y)) = β (y, x)`,
and `P + Q = Psi N d BN` (`M = Doubling.phi N`, `c = 2d + 1`, `β = beta N d B`). -/
theorem E5 (hnil : ∀ s ≥ BN, N.Fd s = 0) (d : ℤ) (B : ℕ) (hB : 2 * BN ≤ B) :
    (∀ x y, Fold.tauOp (phi N) (2 * d + 1) (beta N d B (x, y)) =
      beta N d B (PE N BN d x + QE N BN d y, QE N BN d x + PE N BN d y)) ∧
    (∀ x y, Fold.aOp (phi N) (2 * d + 1) B (beta N d B (x, y)) = beta N d B (y, x)) ∧
    PE N BN d + QE N BN d = Psi N d BN := by
  obtain ⟨hsq, hcomm⟩ := E3 N BN hnil d B hB
  have hsq' : ∀ v, aOp (phi N) (2 * d + 1) B (aOp (phi N) (2 * d + 1) B v) = v :=
    fun v => by simpa using LinearMap.congr_fun hsq v
  have hcomm' : ∀ v, tauOp (phi N) (2 * d + 1) (aOp (phi N) (2 * d + 1) B v) =
      aOp (phi N) (2 * d + 1) B (tauOp (phi N) (2 * d + 1) v) :=
    fun v => (LinearMap.congr_fun hcomm v).symm
  have hswap : ∀ x y, aOp (phi N) (2 * d + 1) B (beta N d B (x, y)) = beta N d B (y, x) := by
    intro x y
    rw [beta_apply', beta_apply', map_add, hsq', add_comm]
  refine ⟨fun x y => ?_, hswap, ?_⟩
  · rw [beta_apply', map_add, hcomm', tauOp_beta_left N BN hnil d B hB,
      tauOp_beta_left N BN hnil d B hB, hswap, ← map_add]
    rfl
  · simp only [PE, QE, Psi, sub_mul]
    abel

end phi

end FoldHalf
