module

public import RequestProject.Fold.Defs
public import RequestProject.DPLattice.Dictionary

/-!
# `C38_the_fold_in_the_group_ring.md`: Part L — Lemma 10.1 (the antipode on `V^{⊗n}`)

* (L0) `F^{(r)} = 0` on `tensorPow A n` for `r > n` (`L0`), from (W) and the weight bound
  `−n ≤ wt ≤ n` (from C18 `wt_pt`, `pt_bijective`).
* (L1) Lemma 10.1: `psi ∘ transl = aOp (tensorPow A n) n (n + 1) ∘ psi` (`L1`), by induction on
  `n` along the recursion of C18's `psi` (`gSplit`, `shear`, `sliceEquiv`) and of `tensorFd`.
* (L2) `expF (tensorPow A n) B = expF (tensorPow A n) (n + 1)` for `B ≥ n + 1` (`L2`).

Here `c = n` is the integer `(n : ℤ)`.
-/

@[expose] public section

noncomputable section

namespace Fold

open CubeLaplacian DPLattice Finset

variable {A : Type*} [CommRing A]

/-! ### (L0) and (L2) -/

/-- (L0, auxiliary) the weights of `V^{⊗n}` lie in `[−n, n]`. -/
lemma wt_tensorPow_bound (n : ℕ) (i : (tensorPow A n).ι) :
    -(n : ℤ) ≤ (tensorPow A n).wt i ∧ (tensorPow A n).wt i ≤ n := by
  obtain ⟨S, rfl⟩ := (pt_bijective (A := A) n).2 i
  rw [wt_pt]
  have h := Finset.card_le_univ S
  rw [Fintype.card_fin] at h
  constructor <;> omega

/-- **(L0)** of `C38_the_fold_in_the_group_ring.md`: for every `n` and `r > n`,
`(tensorPow A n).Fd r = 0`. -/
theorem L0 (n r : ℕ) (hr : n < r) : (tensorPow A n).Fd r = 0 := by
  refine ext_single fun i => funext fun j => ?_
  rw [LinearMap.zero_apply, Pi.zero_apply]
  apply (tensorPow A n).isDP.W_F i r j
  have := wt_tensorPow_bound (A := A) n i
  have := wt_tensorPow_bound (A := A) n j
  omega

/-- **(L2)** of `C38_the_fold_in_the_group_ring.md`: for `B ≥ n + 1`,
`expF (tensorPow A n) B = expF (tensorPow A n) (n + 1)`. -/
theorem L2 (n B : ℕ) (hB : n + 1 ≤ B) :
    expF (tensorPow A n) B = expF (tensorPow A n) (n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  rw [expF, expF, Finset.sum_range_add,
    Finset.sum_eq_zero (s := range k) (fun r _ => L0 n _ (by omega)), add_zero]

/-! ### `expF` and `signOp` on `V ⊗ M` -/

lemma expF_tensorV_bvec0 (M : DPLattice A) (B : ℕ) (m : M.ι → A) :
    expF (tensorV M) (B + 1) (bvec 0 m) = bvec 0 (expF M (B + 1) m) + bvec 1 (expF M B m) := by
  have h : ∀ r, (tensorV M).Fd r (bvec 0 m) = bvec 0 (M.Fd r m) + bvec 1 (pred M.Fd r m) :=
    fun r => tensorFd_bvec0 _ _ _
  simp only [expF, LinearMap.coe_sum, Finset.sum_apply, h, Finset.sum_add_distrib]
  rw [map_sum, map_sum]
  congr 1
  rw [Finset.sum_range_succ']
  simp

lemma expF_tensorV_bvec1 (M : DPLattice A) (B : ℕ) (m : M.ι → A) :
    expF (tensorV M) B (bvec 1 m) = bvec 1 (expF M B m) := by
  have h : ∀ r, (tensorV M).Fd r (bvec 1 m) = bvec 1 (M.Fd r m) := fun r => tensorFd_bvec1 _ _ _
  simp only [expF, LinearMap.coe_sum, Finset.sum_apply, h]
  rw [map_sum]

lemma neg_one_pow_natAbs_add_one (y : ℤ) :
    (-1 : A) ^ (y + 1).natAbs = -(-1) ^ y.natAbs := by
  rcases Int.even_or_odd y with h | h
  · rw [(Int.natAbs_even.2 h).neg_one_pow, (Int.natAbs_odd.2 h.add_one).neg_one_pow]
  · rw [(Int.natAbs_odd.2 h).neg_one_pow, (Int.natAbs_even.2 h.add_one).neg_one_pow, neg_neg]

lemma signOp_tensorV_bvec0 (M : DPLattice A) (c : ℤ) (m : M.ι → A) :
    signOp (tensorV M) (c + 1) (bvec 0 m) = bvec 0 (signOp M c m) := by
  funext ⟨e, i⟩
  rw [signOp_apply, bvec_apply, bvec_apply]
  split_ifs with he
  · subst he
    rw [signOp_apply]
    show (-1 : A) ^ ((c + 1 - (wtV 0 + M.wt i)) / 2).natAbs * m i = _
    rw [wtV_zero, show c + 1 - (1 + M.wt i) = c - M.wt i by ring]
  · rw [mul_zero]

lemma signOp_tensorV_bvec1 (M : DPLattice A) (c : ℤ) (m : M.ι → A) :
    signOp (tensorV M) (c + 1) (bvec 1 m) = -bvec 1 (signOp M c m) := by
  funext ⟨e, i⟩
  rw [signOp_apply, Pi.neg_apply, bvec_apply, bvec_apply]
  split_ifs with he
  · subst he
    rw [signOp_apply]
    show (-1 : A) ^ ((c + 1 - (wtV 1 + M.wt i)) / 2).natAbs * m i = _
    rw [wtV_one, show c + 1 - (-1 + M.wt i) = (c - M.wt i) + 1 * 2 by ring,
      Int.add_mul_ediv_right _ _ (by norm_num), neg_one_pow_natAbs_add_one]
    ring
  · rw [mul_zero, neg_zero]

/-- (L1, the inductive step) `aOp` of `V^{⊗(n+1)}` on the slots:
`(x_0, x_1) ↦ (a x_0, −a (x_0 + x_1))` where `a = aOp (tensorPow A n) n (n + 1)`. -/
lemma aOp_succ_slots (n : ℕ) (x0 x1 : (tensorPow A n).ι → A) :
    aOp (tensorPow A (n + 1)) ((n + 1 : ℕ) : ℤ) (n + 1 + 1) (bvec 0 x0 + bvec 1 x1) =
      bvec 0 (aOp (tensorPow A n) n (n + 1) x0) +
        bvec 1 (-aOp (tensorPow A n) n (n + 1) (x0 + x1)) := by
  show aOp (tensorV (tensorPow A n)) _ _ _ = _
  have hE : expF (tensorPow A n) (n + 1 + 1) = expF (tensorPow A n) (n + 1) := L2 n _ (by omega)
  rw [aOp, LinearMap.comp_apply, map_add, expF_tensorV_bvec0, expF_tensorV_bvec1, hE,
    Nat.cast_succ, map_add, map_add, signOp_tensorV_bvec0, signOp_tensorV_bvec1,
    signOp_tensorV_bvec1, aOp, LinearMap.comp_apply, LinearMap.comp_apply, map_add, map_add,
    map_neg, map_add]
  abel

/-! ### Translation on `G (n+1)` -/

lemma cons_add_aElt (n : ℕ) (a : ZMod 2) (g : G n) :
    (Fin.cons a g : G (n + 1)) + aElt (n + 1) = Fin.cons (a + 1) (g + aElt n) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [aElt]
  · simp [aElt]

lemma slice0_gSplit_transl (n : ℕ) (f : G (n + 1) → A) :
    slice 0 (gSplit A n (transl A (n + 1) f)) = transl A n (slice 1 (gSplit A n f)) := by
  funext g
  show f (Fin.cons _ g + aElt (n + 1)) = f (Fin.cons _ (g + aElt n))
  rw [cons_add_aElt]
  rfl

lemma slice1_gSplit_transl (n : ℕ) (f : G (n + 1) → A) :
    slice 1 (gSplit A n (transl A (n + 1) f)) = transl A n (slice 0 (gSplit A n f)) := by
  funext g
  show f (Fin.cons _ g + aElt (n + 1)) = f (Fin.cons _ (g + aElt n))
  rw [cons_add_aElt]
  rfl

/-! ### (L1) -/

/-- **(L1)** of `C38_the_fold_in_the_group_ring.md` (Lemma 10.1): for every commutative ring `A`
and every `n`,
`(psi A n).toLinearMap ∘ₗ transl A n = aOp (tensorPow A n) n (n + 1) ∘ₗ (psi A n).toLinearMap`. -/
theorem L1 (n : ℕ) :
    (psi A n).toLinearMap ∘ₗ transl A n =
      aOp (tensorPow A n) n (n + 1) ∘ₗ (psi A n).toLinearMap := by
  induction n with
  | zero =>
    refine LinearMap.ext fun f => ?_
    have ht : transl A 0 f = f :=
      funext fun g => by rw [transl_apply]; congr 1; exact Subsingleton.elim _ _
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ht]
    funext u
    rw [aOp, LinearMap.comp_apply, signOp_apply]
    simp [expF, tensorPow, one, oneFd]
  | succ n ih =>
    have ih' : ∀ x, psi A n (transl A n x) = aOp (tensorPow A n) n (n + 1) (psi A n x) :=
      fun x => LinearMap.congr_fun ih x
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [eq_bvec_slice (psi A (n + 1) f), aOp_succ_slots, slice0_psi_succ, slice1_psi_succ]
    apply ext_slice
    · rw [map_add, slice_bvec_self, slice0_bvec1, add_zero, slice0_psi_succ, slice0_gSplit_transl,
        slice1_gSplit_transl, ← map_add, add_comm, ih']
    · rw [map_add, slice1_bvec0, slice_bvec_self, zero_add, slice1_psi_succ, slice1_gSplit_transl,
        ← map_add, map_neg, ih', add_neg_cancel_right]

end Fold
