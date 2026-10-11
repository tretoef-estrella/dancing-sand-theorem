module

public import RequestProject.FormalDance.PartL1

/-!
# `C40b_the_formal_dance_of_payment_systems.md`: Part L, (L2) — the split move of a payment system

The entries of `vsplit (paySys p κ)` are again of the form `mk c e` (`vsplit_paySys_eq`); the
values of the split data are read through C12's `Split.pSp_A`, `Split.pSp_C`, `Split.κSp_AA`,
`Split.κSp_CC`, `Split.κSp_CA`, `Split.κSp_AC` (`entSp_AA`, `entSp_CC`, `entSp_CA`, `entSp_AC`).
The equality `Dd − B C = 2 • PS` holds exactly (`L2_schur_eq`), which is more than the agreement
stated in the file.
-/

@[expose] public section

noncomputable section

namespace FormalDance

open FormalOps Finset Split

variable {A : Type*} [CommRing A] {n : Type*} [LinearOrder n]

lemma fin_two_cases (v : Fin 2) : v = 0 ∨ v = 1 := by
  rcases v with ⟨_ | _ | v, hv⟩
  · left; rfl
  · right; rfl
  · omega

/-! ### The split data through `ent` -/

section Sp
variable [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A)

lemma entSp_AA (s s' : n) (f : ℤ) :
    ent (pSp p) (κSp p κ) (toLex (s, 0)) (toLex (s', 0)) f =
      ent (Payment.pT p) (Payment.κT p κ) s s' f := by
  unfold ent
  simp only [toLex_inj, Prod.mk.injEq, and_true, Prod.Lex.toLex_lt_toLex, lt_self_iff_false,
    and_false, or_false]
  split_ifs with h1 h2
  · subst h1; simp only [ext0, pSp_A]
  · simp only [ext0, κSp_AA, if_pos h2]
  · rfl

lemma entSp_CC (s s' : n) (f : ℤ) :
    ent (pSp p) (κSp p κ) (toLex (s, 1)) (toLex (s', 1)) f =
      ent (Payment.pT (shiftP p)) (Payment.κT (shiftP p) (shiftK κ)) s s' f := by
  unfold ent
  simp only [toLex_inj, Prod.mk.injEq, and_true, Prod.Lex.toLex_lt_toLex, lt_self_iff_false,
    and_false, or_false]
  split_ifs with h1 h2
  · subst h1; simp only [ext0, pSp_C]
  · simp only [ext0, κSp_CC, if_pos h2]
  · rfl

lemma entSp_CA (s s' : n) (f : ℤ) :
    ent (pSp p) (κSp p κ) (toLex (s, 1)) (toLex (s', 0)) f = -ent p κ s s' (2 * f + 1) := by
  rcases lt_or_ge f 0 with hf | hf
  · rw [ent_neg p κ s s' (show 2 * f + 1 < 0 by omega)]
    unfold ent
    split_ifs <;> simp [ext0_neg _ hf]
  · lift f to ℕ using hf
    have h1 : (2 * (f : ℤ) + 1) = ((2 * f + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, ent_natCast, ent_natCast]
    unfold entN
    simp only [toLex_inj, Prod.mk.injEq, Prod.Lex.toLex_lt_toLex, Fin.isValue, κSp_CA]
    rcases lt_trichotomy s' s with h | rfl | h
    · simp [h, h.ne']
    · simp
    · simp [h.ne, h.not_gt]

lemma entSp_AC (s s' : n) (f : ℤ) :
    ent (pSp p) (κSp p κ) (toLex (s, 0)) (toLex (s', 1)) f = 0 := by
  unfold ent
  simp only [toLex_inj, Prod.mk.injEq, Fin.zero_eq_one_iff, Nat.succ_ne_self, and_false,
    if_false]
  split_ifs
  · simp [ext0, κSp_AC]
  · rfl

/-- The identity behind (L2) on the `C`-slots, at every floor `f`. -/
lemma ent_sum_shift (s s' : n) (f : ℤ) :
    ∑ t, ent p κ s t (2 * f + 1) * ent p κ t s' (2 * f + 1 + 1) =
      -(2 * ent (Payment.pT (shiftP p)) (Payment.κT (shiftP p) (shiftK κ)) s s' f) := by
  rcases lt_or_ge f 0 with hf | hf
  · rw [ent_neg _ _ _ _ hf, Finset.sum_eq_zero]
    · ring
    · intro t _; rw [ent_neg p κ s t (show 2 * f + 1 < 0 by omega), zero_mul]
  · lift f to ℕ using hf
    have h1 : (2 * (f : ℤ) + 1 + 1) = ((2 * f + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
    have h2 : (2 * (f : ℤ) + 1) = ((2 * f + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [h1]
    simp only [h2, ent_natCast]
    exact core_sum (shiftP p) (shiftK κ) s s' f

end Sp

/-! ### The entries of `vsplit (paySys p κ)` -/

/-- The coefficient of `F^{(0)}` of the entry `(q, q')` of `vsplit (paySys p κ)`. -/
def entV (p : n → ℕ → A) (κ : n → n → ℕ → A) (q q' : n × Fin 2) : ℤ → A :=
  if q.2 = 0 ∧ q'.2 = 0 then ent p κ q.1 q'.1
  else if q.2 = 1 ∧ q'.2 = 0 then (fun _ => if q.1 = q'.1 then 1 else 0)
  else if q.2 = 1 ∧ q'.2 = 1 then (fun g => ent p κ q.1 q'.1 (g + 1)) else 0

lemma vsplit_paySys_eq (p : n → ℕ → A) (κ : n → n → ℕ → A) (q q' : n × Fin 2) :
    vsplit (paySys p κ) q q' = mk (if q = q' then 1 else 0) (entV p κ q q') := by
  obtain ⟨s, v⟩ := q
  obtain ⟨s', v'⟩ := q'
  rcases fin_two_cases v with rfl | rfl <;> rcases fin_two_cases v' with rfl | rfl <;>
    simp [vsplit, entV, paySys_eq_mk, vprime_mk, vplus_mk, dg_eq_mk, zero_eq_mk]

/-- The identity behind (L2) at every floor `f`. -/
lemma entV_sum [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) (q q' : n × Fin 2) (f : ℤ) :
    ∑ t, entV p κ q t (2 * f) * entV p κ t q' (2 * f + 1) =
      -(2 * ent (pSp p) (κSp p κ) (toLex q) (toLex q') f) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  obtain ⟨s, v⟩ := q
  obtain ⟨s', v'⟩ := q'
  rcases fin_two_cases v with rfl | rfl <;> rcases fin_two_cases v' with rfl | rfl <;>
    simp only [entV, Fin.isValue, one_ne_zero, zero_ne_one, and_true, and_false, if_true, if_false, Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add]
  · rw [ent_sum, entSp_AA]
  · rw [entSp_AC, Finset.sum_const_zero]; ring
  · simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', entSp_CA]
    simp only [Finset.mem_univ, if_true]
    ring
  · rw [ent_sum_shift, entSp_CC]

/-! ### (L2) -/

lemma twB_vsplit (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twB (vsplit (paySys p κ)) =
      Matrix.of (fun q q' => Bf.dg (fun f => entV p κ q q' (2 * f))) := by
  funext q q'; simp only [twB, vsplit_paySys_eq, tw00_mk, Matrix.of_apply]

lemma twC_vsplit (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twC (vsplit (paySys p κ)) =
      Matrix.of (fun q q' => Bf.dg (fun f => entV p κ q q' (2 * f + 1))) := by
  funext q q'; simp only [twC, vsplit_paySys_eq, tw11_mk, Matrix.of_apply]

/-- (L2) of `C40b_the_formal_dance_of_payment_systems.md`, first equality: the pivot block of the
V-split of a payment system is exactly `1` (no finiteness of `n` is needed). -/
theorem L2_twP (p : n → ℕ → A) (κ : n → n → ℕ → A) : twP (vsplit (paySys p κ)) = 1 := by
  funext q q'
  simp only [twP, vsplit_paySys_eq, tw10_mk, Matrix.one_apply]
  split_ifs
  · exact one_eq_dg.symm
  · ext m f; simp

/-- (L2) of `C40b_the_formal_dance_of_payment_systems.md`, second equality, in the stronger exact
form: `Dd − B C = 2 • PS` holds exactly (the file only claims agreement). -/
theorem L2_schur_eq [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twD (vsplit (paySys p κ)) - twB (vsplit (paySys p κ)) * twC (vsplit (paySys p κ)) =
      (2 : A) • ((fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')) :
        Matrix (n × Fin 2) (n × Fin 2) (Bf A)) := by
  rw [twB_vsplit, twC_vsplit, dgMat_mul]
  funext q q'
  simp only [Matrix.sub_apply, Pi.smul_apply, Matrix.of_apply, twD, vsplit_paySys_eq,
    tw01_mk, dg_eq_mk, mk_sub, smul_mk, paySys_eq_mk, toLex_inj]
  congr 1
  · ring
  · funext f
    simp only [Pi.sub_apply, Pi.zero_apply, zero_sub]
    rw [entV_sum]; ring

/-- **(L2)** of `C40b_the_formal_dance_of_payment_systems.md` (Lemma 10.6(a), second sentence):
with `PS q q' := paySys (pSp p) (κSp p κ) (toLex q) (toLex q')` (the payment system of the split
data on `Lex (n × Fin 2)`, read through `toLex`), `twP (vsplit (paySys p κ)) = 1`,
`MAgree (Dd − B C) ((2 : A) • PS)`, and consequently `CleanStep (vsplit (paySys p κ)) PS`
(with `Q = 1`). The agreement is in fact an exact equality (`L2_schur_eq`). -/
theorem L2 [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twP (vsplit (paySys p κ)) = 1 ∧
    MAgree (twD (vsplit (paySys p κ)) - twB (vsplit (paySys p κ)) * twC (vsplit (paySys p κ)))
      ((2 : A) • ((fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')) :
        Matrix (n × Fin 2) (n × Fin 2) (Bf A))) ∧
    CleanStep (vsplit (paySys p κ))
      (fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')) := by
  refine ⟨L2_twP p κ, MAgree.of_eq (L2_schur_eq p κ), 1, ?_, ?_, ?_⟩
  · rw [L2_twP, mul_one]; exact MAgree.refl _
  · rw [L2_twP, mul_one]; exact MAgree.refl _
  · rw [mul_one]; exact MAgree.of_eq (L2_schur_eq p κ)

end FormalDance
