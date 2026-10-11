module

public import RequestProject.FoldHalf.Defs

/-!
# `C39_the_fold_on_the_half_lattice.md`: general facts on operators of a DP-lattice

Auxiliary lemmas (used in Parts S and E): the divided powers commute, `H` against `F^{(r)}`,
`signOp` and `parOp` on weight vectors and against `F^{(r)}`, and — for any DP-lattice `M` with
`F^{(r)} = 0` for `r ≥ B` — `aOp M c B * aOp M c B = 1` and `aOp M c B` commutes with
`tauOp M c` (`aOp_mul_self`, `aOp_comm_tauOp`).
-/

@[expose] public section

noncomputable section

namespace FoldHalf

open DPLattice Doubling Finset Fold

variable {A : Type*} [CommRing A]

lemma neg_one_pow_natAbs_add_nat (y : ℤ) (k : ℕ) :
    (-1 : A) ^ (y + k).natAbs = (-1) ^ y.natAbs * (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Fold.neg_one_pow_natAbs_add_one, ih, pow_succ]; ring

lemma neg_one_pow_natAbs_add_two_mul (y : ℤ) (k : ℕ) :
    (-1 : A) ^ (y + 2 * k).natAbs = (-1) ^ y.natAbs := by
  have := neg_one_pow_natAbs_add_nat (A := A) y (2 * k)
  push_cast at this
  rw [this, pow_mul]; simp

lemma vec_eq_sum_single {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → A) :
    v = ∑ i, v i • (Pi.single i (1 : A) : ι → A) := by
  funext k; simp [Finset.sum_apply, Pi.single_apply]

section lattice

variable (M : DPLattice A)

/-! ### Products of divided powers -/

lemma Fd_mul (a b : ℕ) : M.Fd a * M.Fd b = (((a + b).choose a : ℕ) : A) • M.Fd (a + b) := by
  have h := M.isDP.P1_F a b
  rw [Module.End.mul_eq_comp, h]
  congr 2
  rw [← Nat.cast_add, Ring.choose_natCast]
  simp

lemma Fd_comm (a b : ℕ) : M.Fd a * M.Fd b = M.Fd b * M.Fd a := by
  rw [Fd_mul, Fd_mul, add_comm b a, Nat.choose_symm_add]

lemma Fd_commute (a b : ℕ) : Commute (M.Fd a) (M.Fd b) := Fd_comm M a b

lemma Fd_one_mul (r : ℕ) : M.Fd 1 * M.Fd r = ((r + 1 : ℕ) : A) • M.Fd (r + 1) := by
  rw [Fd_mul, add_comm 1 r, Nat.choose_one_right]

/-! ### `H` against `F^{(r)}` -/

lemma H_single (i : M.ι) :
    H M (Pi.single i 1) = ((M.wt i : ℤ) : A) • (Pi.single i 1 : M.ι → A) :=
  Hop_of_inWt (inWt_single M.wt i)

lemma H_mul_Fd (r : ℕ) : H M * M.Fd r = M.Fd r * H M - ((2 * r : ℕ) : A) • M.Fd r := by
  refine ext_single fun i => ?_
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [Hop_of_inWt (M.isDP.inWt_Fd r (inWt_single M.wt i)), H_single, map_smul, ← sub_smul]
  congr 1; push_cast; ring

/-! ### `signOp` -/

lemma signOp_of_inWt (c w : ℤ) {v : M.ι → A} (hv : InWt M.wt w v) :
    signOp M c v = ((-1 : A) ^ ((c - w) / 2).natAbs) • v := by
  funext j
  rw [signOp_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : M.wt j = w
  · rw [h]
  · rw [hv j h, mul_zero, mul_zero]

lemma signOp_mul_self (c : ℤ) : signOp M c * signOp M c = 1 := by
  apply LinearMap.ext; intro f; funext i
  simp only [Module.End.mul_apply, signOp_apply, Module.End.one_apply, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul]
  simp

lemma signOp_mul_Fd_mul_signOp (c : ℤ) (r : ℕ) :
    signOp M c * M.Fd r * signOp M c = ((-1 : A) ^ r) • M.Fd r := by
  refine ext_single fun i => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply]
  rw [signOp_of_inWt M c _ (inWt_single M.wt i), map_smul, map_smul,
    signOp_of_inWt M c _ (M.isDP.inWt_Fd r (inWt_single M.wt i)), smul_smul]
  congr 1
  rw [show c - (M.wt i - 2 * r) = (c - M.wt i) + r * 2 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num), neg_one_pow_natAbs_add_nat]
  rw [show ∀ x y : A, x * (x * y) = (x * x) * y from fun x y => by ring, ← pow_add, ← two_mul,
    pow_mul]
  simp

lemma signOp_comm_H (c : ℤ) : signOp M c * H M = H M * signOp M c := by
  apply LinearMap.ext; intro f; funext i
  simp only [Module.End.mul_apply, signOp_apply, Hop_apply]
  ring

lemma signOp_mul_Fd (c : ℤ) (r : ℕ) :
    signOp M c * M.Fd r = ((-1 : A) ^ r) • (M.Fd r * signOp M c) := by
  calc signOp M c * M.Fd r = signOp M c * M.Fd r * (signOp M c * signOp M c) := by
        rw [signOp_mul_self, mul_one]
    _ = (signOp M c * M.Fd r * signOp M c) * signOp M c := by noncomm_ring
    _ = _ := by rw [signOp_mul_Fd_mul_signOp, smul_mul_assoc]

/-! ### `expF`, `aOp` and `tauOp` -/

/-- The alternating sum `Σ_{r < B} (−1)^r F^{(r)}` is inverse to `expF M B` when `F^{(r)} = 0`
for `r ≥ B`. -/
lemma alt_mul_expF (B : ℕ) (hB : ∀ r ≥ B, M.Fd r = 0) :
    (∑ r ∈ range B, ((-1 : A) ^ r) • M.Fd r) * expF M B = 1 := by
  rw [expF, Finset.sum_mul_sum]
  have h1 : ∀ a ∈ range B, ∑ b ∈ range B, ((-1 : A) ^ a) • M.Fd a * M.Fd b =
      ∑ b ∈ range (B - a), ((-1 : A) ^ a * ((a + b).choose a : ℕ)) • M.Fd (a + b) := by
    intro a _
    rw [← Finset.sum_subset (s₁ := range (B - a)) (s₂ := range B)]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [smul_mul_assoc, Fd_mul, smul_smul]
    · intro b; simp only [mem_range]; omega
    · intro b _ hb
      simp only [mem_range, not_lt] at hb
      rw [smul_mul_assoc, Fd_mul, hB (a + b) (by omega), smul_zero, smul_zero]
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_range_diag_flip B
    (fun a b => ((-1 : A) ^ a * ((a + b).choose a : ℕ)) • M.Fd (a + b))]
  have h2 : ∀ m ∈ range B, ∑ k ∈ range (m + 1),
      ((-1 : A) ^ k * ((k + (m - k)).choose k : ℕ)) • M.Fd (k + (m - k)) =
      (if m = 0 then (1 : A) else 0) • M.Fd m := by
    intro m _
    rw [← Finset.sum_congr rfl (fun k hk => by
      rw [show k + (m - k) = m by simp at hk; omega]), ← Finset.sum_smul]
    congr 1
    have := Int.alternating_sum_range_choose (n := m)
    have h := congrArg (Int.cast : ℤ → A) this
    push_cast at h
    rw [h]
  rw [Finset.sum_congr rfl h2]
  rcases Nat.eq_zero_or_pos B with rfl | hBpos
  · have : (1 : Module.End A (M.ι → A)) = 0 := by rw [← M.isDP.P0_F]; exact hB 0 le_rfl
    simp [this]
  · rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [hb]) (fun h => absurd (by simpa using hBpos) h)]
    simp [M.isDP.P0_F]

lemma signOp_expF_signOp (c : ℤ) (B : ℕ) :
    signOp M c * expF M B * signOp M c = ∑ r ∈ range B, ((-1 : A) ^ r) • M.Fd r := by
  rw [expF, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => signOp_mul_Fd_mul_signOp M c r

lemma aOp_eq_mul (c : ℤ) (B : ℕ) : aOp M c B = signOp M c * expF M B := rfl

/-- On any DP-lattice with `F^{(r)} = 0` for `r ≥ B`, `aOp M c B * aOp M c B = 1`. -/
lemma aOp_mul_self (c : ℤ) (B : ℕ) (hB : ∀ r ≥ B, M.Fd r = 0) :
    aOp M c B * aOp M c B = 1 := by
  rw [aOp_eq_mul, show signOp M c * expF M B * (signOp M c * expF M B) =
    (signOp M c * expF M B * signOp M c) * expF M B by noncomm_ring, signOp_expF_signOp,
    alt_mul_expF M B hB]

lemma expF_comm_Fd (B r : ℕ) : expF M B * M.Fd r = M.Fd r * expF M B := by
  rw [expF, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => Fd_comm M s r

/-- `E F + F E = E H − H E` for `E = expF M B`, `F = F^{(1)}`, when `F^{(r)} = 0` for `r ≥ B`. -/
lemma expF_F_add (B : ℕ) (hB : ∀ r ≥ B, M.Fd r = 0) :
    expF M B * M.Fd 1 + M.Fd 1 * expF M B = expF M B * H M - H M * expF M B := by
  have hL : expF M B * M.Fd 1 + M.Fd 1 * expF M B =
      ∑ r ∈ range B, ((2 * (r + 1) : ℕ) : A) • M.Fd (r + 1) := by
    rw [← expF_comm_Fd, ← two_smul A, expF, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fd_comm, Fd_one_mul, smul_smul]; push_cast; ring_nf
  have hR : expF M B * H M - H M * expF M B = ∑ r ∈ range B, ((2 * r : ℕ) : A) • M.Fd r := by
    rw [expF, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [H_mul_Fd]; abel
  rw [hL, hR]
  have h1 := Finset.sum_range_succ' (fun r => ((2 * r : ℕ) : A) • M.Fd r) B
  have h2 := Finset.sum_range_succ (fun r => ((2 * r : ℕ) : A) • M.Fd r) B
  rw [hB B le_rfl, smul_zero, add_zero] at h2
  simp only [Nat.mul_zero, Nat.cast_zero, zero_smul, add_zero] at h1
  rw [← h1, h2]

/-- On any DP-lattice with `F^{(r)} = 0` for `r ≥ B`, `aOp M c B` commutes with `tauOp M c`. -/
lemma aOp_comm_tauOp (c : ℤ) (B : ℕ) (hB : ∀ r ≥ B, M.Fd r = 0) :
    aOp M c B * tauOp M c = tauOp M c * aOp M c B := by
  have hSF : M.Fd 1 * signOp M c = -(signOp M c * M.Fd 1) := by
    apply LinearMap.ext; intro f
    have h := LinearMap.congr_fun (signOp_mul_Fd M c 1) f
    simp only [Module.End.mul_apply, LinearMap.smul_apply, pow_one, neg_smul, one_smul] at h
    simp only [Module.End.mul_apply, LinearMap.neg_apply, h, neg_neg]
  have hSH := signOp_comm_H M c
  have key := expF_F_add M B hB
  set S := signOp M c
  set E := expF M B
  set F := M.Fd 1
  rw [aOp_eq_mul, tauOp]
  have h1 : (F + (c : A) • 1 - H M) * S = S * ((c : A) • 1 - H M - F) := by
    rw [sub_mul, add_mul, hSF, ← hSH, smul_mul_assoc, one_mul, mul_sub, mul_sub, mul_smul_comm,
      mul_one]
    abel
  have h2 : E * (F + (c : A) • 1 - H M) = ((c : A) • 1 - H M - F) * E := by
    rw [mul_sub, mul_add, sub_mul, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
      show E * F = E * H M - H M * E - F * E by rw [← key]; abel]
    abel
  rw [mul_assoc, h2, ← mul_assoc, ← h1, mul_assoc]

end lattice

/-! ### `parOp` -/

section par

variable (N : DPLattice A)

lemma parOp_of_inWt (d w : ℤ) {v : N.ι → A} (hv : InWt N.wt w v) :
    parOp N d v = ((-1 : A) ^ (d - w).natAbs) • v := by
  funext j
  rw [parOp_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : N.wt j = w
  · rw [h]
  · rw [hv j h, mul_zero, mul_zero]

lemma parOp_mul_self (d : ℤ) : parOp N d * parOp N d = 1 := by
  apply LinearMap.ext; intro f; funext i
  simp only [Module.End.mul_apply, parOp_apply, Module.End.one_apply, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul]
  simp

lemma parOp_comm_Fd (d : ℤ) (s : ℕ) : parOp N d * N.Fd s = N.Fd s * parOp N d := by
  refine ext_single fun i => ?_
  simp only [Module.End.mul_apply]
  rw [parOp_of_inWt N d _ (inWt_single N.wt i), map_smul,
    parOp_of_inWt N d _ (N.isDP.inWt_Fd s (inWt_single N.wt i)),
    show d - (N.wt i - 2 * s) = (d - N.wt i) + 2 * s by ring, neg_one_pow_natAbs_add_two_mul]

lemma parOp_succ (d : ℤ) : parOp N (d + 1) = -parOp N d := by
  apply LinearMap.ext; intro f; funext i
  simp only [parOp_apply, LinearMap.neg_apply, Pi.neg_apply]
  rw [show d + 1 - N.wt i = (d - N.wt i) + 1 by ring, Fold.neg_one_pow_natAbs_add_one]
  ring

end par

end FoldHalf
