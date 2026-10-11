module

public import RequestProject.FormalDance.PartC

/-!
# `C40b_the_formal_dance_of_payment_systems.md`: Part L, (L1) — the twist move of a payment system

Every entry of a payment system is of the form `mk c e = c • Bf.fd 1 + Bf.dg e`; the twist map
and the V-split act on such operators by explicit formulas (`tw10_mk`, `tw01_mk`, `tw00_mk`,
`tw11_mk`, `vplus_mk`, `vprime_mk`). The products of the blocks are matrices of `Bf.dg`'s
(`dgMat_mul`), and the identity behind (L1) is a sum over lower-triangular data (`core_sum`).
-/

@[expose] public section

noncomputable section

namespace FormalDance

open FormalOps Finset Doubling

variable {A : Type*} [CommRing A]

/-! ### Operators of the form `c • F + e(D)` -/

/-- The operator `c • F^{(1)} + e(D)`. -/
def mk (c : A) (e : ℤ → A) : Bf A := c • Bf.fd 1 + Bf.dg e

@[simp] lemma coef_mk (c : A) (e : ℤ → A) (m : ℕ) (f : ℤ) :
    (mk c e).coef m f = c * (if m = 1 then 1 else 0) + (if m = 0 then e f else 0) := by
  simp [mk]

lemma one_eq_dg : (1 : Bf A) = Bf.dg (fun _ => 1) := by
  ext m f; simp

lemma dg_eq_mk (e : ℤ → A) : Bf.dg e = mk 0 e := by ext m f; simp

lemma zero_eq_mk : (0 : Bf A) = mk 0 0 := by ext m f; simp

lemma tw10_mk (c : A) (e : ℤ → A) : tw10 (mk c e) = Bf.dg (fun _ => c) := by
  ext q f
  rcases q with _ | q <;> simp [dfi_one]

lemma tw01_mk (c : A) (e : ℤ → A) : tw01 (mk c e) = mk (2 * c) 0 := by
  ext q f
  rcases q with _ | q
  · simp
  · rcases q with _ | q
    · simp [dfi_one]
    · simp

lemma tw00_mk (c : A) (e : ℤ → A) : tw00 (mk c e) = Bf.dg (fun f => e (2 * f)) := by
  ext q f
  rcases q with _ | q
  · simp
  · simp

lemma tw11_mk (c : A) (e : ℤ → A) : tw11 (mk c e) = Bf.dg (fun f => e (2 * f + 1)) := by
  ext q f
  rcases q with _ | q
  · simp
  · simp

lemma vplus_mk (c : A) (e : ℤ → A) : vplus (mk c e) = mk c (fun g => e (g + 1)) := by
  ext m g; simp

lemma vprime_mk (c : A) (e : ℤ → A) : vprime (mk c e) = Bf.dg (fun _ => c) := by
  ext m g; rcases m with _ | m <;> simp

lemma mk_sub (c c' : A) (e e' : ℤ → A) : mk c e - mk c' e' = mk (c - c') (e - e') := by
  ext m f; simp; split_ifs <;> ring

lemma smul_mk (a c : A) (e : ℤ → A) : a • mk c e = mk (a * c) (fun f => a * e f) := by
  ext m f; simp; split_ifs <;> ring

lemma dg_mul_dg (a b : ℤ → A) : Bf.dg a * Bf.dg b = Bf.dg (fun f => a f * b f) := by
  ext m f
  rw [Bf.coef_mul]
  rcases m with _ | m
  · simp
  · rw [Finset.sum_eq_zero]
    · simp
    · intro i hi
      rw [Finset.mem_range] at hi
      by_cases h : i = 0
      · subst h; simp
      · simp [h]

lemma coef_sum {ι : Type*} (s : Finset ι) (x : ι → Bf A) (m : ℕ) (f : ℤ) :
    (∑ i ∈ s, x i).coef m f = ∑ i ∈ s, (x i).coef m f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Bf.coef_add, ih]

lemma sum_dg {ι : Type*} (s : Finset ι) (e : ι → ℤ → A) :
    ∑ i ∈ s, Bf.dg (e i) = Bf.dg (fun f => ∑ i ∈ s, e i f) := by
  ext m f
  rw [coef_sum]
  by_cases hm : m = 0 <;> simp [hm]

/-- The product of two matrices of floor functions is the matrix of floor functions of the
pointwise products. -/
lemma dgMat_mul {n : Type*} [Fintype n] (b c : n → n → ℤ → A) :
    Matrix.of (fun s s' => Bf.dg (b s s')) * Matrix.of (fun s s' => Bf.dg (c s s')) =
      Matrix.of (fun s s' => Bf.dg (fun f => ∑ t, b s t f * c t s' f)) := by
  refine Matrix.ext fun s s' => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply, dg_mul_dg]
  exact sum_dg (A := A) _ _

/-! ### Extension by zero -/

lemma ext0_natCast (q : ℕ → A) (k : ℕ) : ext0 q (k : ℤ) = q k := by
  simp [ext0]

lemma ext0_neg (q : ℕ → A) {f : ℤ} (hf : f < 0) : ext0 q f = 0 := by
  simp [ext0, not_le.mpr hf]

/-! ### The entries of a payment system -/

section Pay

variable {n : Type*} [LinearOrder n]

/-- The coefficient of `F^{(0)}` of the entry `(s, s')` of `paySys p κ`. -/
def ent (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) : ℤ → A :=
  if s = s' then ext0 (fun f => 2 * p s f) else if s' < s then ext0 (fun f => 2 * κ s s' f)
  else 0

/-- The same at natural floors. -/
def entN (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) (k : ℕ) : A :=
  if s = s' then 2 * p s k else if s' < s then 2 * κ s s' k else 0

lemma ent_natCast (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) (k : ℕ) :
    ent p κ s s' (k : ℤ) = entN p κ s s' k := by
  unfold ent entN; split_ifs <;> simp [ext0_natCast]

lemma ent_neg (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) {f : ℤ} (hf : f < 0) :
    ent p κ s s' f = 0 := by
  unfold ent; split_ifs <;> simp [ext0_neg _ hf]

lemma paySys_eq_mk (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) :
    paySys p κ s s' = mk (if s = s' then 1 else 0) (ent p κ s s') := by
  unfold paySys ent
  split_ifs <;> ext m f <;> simp

/-- A sum of products of two lower-triangular arrays. -/
lemma lower_sum [Fintype n] (β γ : n → n → A) (δ ε : n → A) (s s' : n) :
    ∑ t, (if s = t then δ s else if t < s then β s t else 0) *
        (if t = s' then ε t else if s' < t then γ t s' else 0) =
      if s = s' then δ s * ε s
      else if s' < s then δ s * γ s s' + β s s' * ε s' +
        ∑ t ∈ univ.filter (fun t => s' < t ∧ t < s), β s t * γ t s'
      else 0 := by
  have z1 : ∀ t, s < t → (if s = t then δ s else if t < s then β s t else 0) = 0 := by
    intro t h; rw [if_neg h.ne, if_neg (not_lt.mpr h.le)]
  have z2 : ∀ t, t < s' → (if t = s' then ε t else if s' < t then γ t s' else 0) = 0 := by
    intro t h; rw [if_neg h.ne, if_neg (not_lt.mpr h.le)]
  rcases lt_trichotomy s s' with h | rfl | h
  · rw [if_neg h.ne, if_neg (not_lt.mpr h.le)]
    refine Finset.sum_eq_zero fun t _ => ?_
    rcases lt_or_ge s t with h' | h'
    · rw [z1 t h', zero_mul]
    · rw [z2 t (lt_of_le_of_lt h' h), mul_zero]
  · rw [if_pos rfl, Finset.sum_eq_single s]
    · simp
    · intro t _ ht
      rcases lt_or_gt_of_ne ht with h' | h'
      · rw [z2 t h', mul_zero]
      · rw [z1 t h', zero_mul]
    · simp
  · rw [if_neg h.ne', if_pos h]
    have hS : ∀ t ∈ (univ : Finset n),
        t ∉ insert s (insert s' (univ.filter (fun t => s' < t ∧ t < s))) →
        (if s = t then δ s else if t < s then β s t else 0) *
        (if t = s' then ε t else if s' < t then γ t s' else 0) = 0 := by
      intro t _ ht
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and,
        not_lt] at ht
      obtain ⟨h1, h2, h3⟩ := ht
      rcases lt_or_ge s t with h' | h'
      · rw [z1 t h', zero_mul]
      · rcases lt_or_ge t s' with h'' | h''
        · rw [z2 t h'', mul_zero]
        · exfalso
          have := h3 (lt_of_le_of_ne h'' (Ne.symm h2))
          exact h1 (le_antisymm h' this)
    rw [← Finset.sum_subset (Finset.subset_univ _) hS]
    rw [Finset.sum_insert, Finset.sum_insert]
    · rw [if_pos rfl, if_neg h.ne', if_neg (lt_irrefl _), if_neg h.ne', if_pos h, if_pos rfl,
        if_pos h]
      rw [Finset.sum_congr rfl (g := fun t => β s t * γ t s')]
      · ring
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [if_neg ht.2.ne', if_pos ht.2, if_neg ht.1.ne', if_pos ht.1]
    · simp
    · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
      exact ⟨h.ne', fun h' => lt_irrefl _ h'.2⟩

/-- The identity behind (L1) at a natural floor `k`. -/
lemma core_sum [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) (k : ℕ) :
    ∑ t, entN p κ s t (2 * k) * entN p κ t s' (2 * k + 1) =
      -(2 * entN (Payment.pT p) (Payment.κT p κ) s s' k) := by
  have := lower_sum (fun s t => 2 * κ s t (2 * k)) (fun t s' => 2 * κ t s' (2 * k + 1))
    (fun s => 2 * p s (2 * k)) (fun t => 2 * p t (2 * k + 1)) s s'
  simp only [entN]
  rw [this]
  have hsum : ∑ t ∈ univ.filter (fun t => s' < t ∧ t < s),
      2 * κ s t (2 * k) * (2 * κ t s' (2 * k + 1)) =
      4 * ∑ t ∈ univ.filter (fun t => s' < t ∧ t < s), κ t s' (2 * k + 1) * κ s t (2 * k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  split_ifs
  · simp only [Payment.pT]; ring
  · simp only [Payment.κT]; rw [hsum]; ring
  · ring

/-- The identity behind (L1) at every floor `f`. -/
lemma ent_sum [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) (f : ℤ) :
    ∑ t, ent p κ s t (2 * f) * ent p κ t s' (2 * f + 1) =
      -(2 * ent (Payment.pT p) (Payment.κT p κ) s s' f) := by
  rcases lt_or_ge f 0 with hf | hf
  · rw [ent_neg _ _ _ _ hf, Finset.sum_eq_zero]
    · ring
    · intro t _; rw [ent_neg _ _ _ _ (by omega), zero_mul]
  · lift f to ℕ using hf
    have h1 : (2 * (f : ℤ)) = ((2 * f : ℕ) : ℤ) := by push_cast; ring
    have h2 : (2 * (f : ℤ) + 1) = ((2 * f + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [h2]
    simp only [h1, ent_natCast]
    exact core_sum p κ s s' f

end Pay

section L1

variable {n : Type*} [LinearOrder n]

lemma twB_paySys (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twB (paySys p κ) = Matrix.of (fun s s' => Bf.dg (fun f => ent p κ s s' (2 * f))) := by
  funext s s'; simp only [twB, paySys_eq_mk, tw00_mk, Matrix.of_apply]

lemma twC_paySys (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twC (paySys p κ) = Matrix.of (fun s s' => Bf.dg (fun f => ent p κ s s' (2 * f + 1))) := by
  funext s s'; simp only [twC, paySys_eq_mk, tw11_mk, Matrix.of_apply]

/-- (L1) of `C40b_the_formal_dance_of_payment_systems.md`, first equality: the pivot block of a
payment system is exactly `1` (no finiteness of `n` is needed). -/
theorem L1_twP (p : n → ℕ → A) (κ : n → n → ℕ → A) : twP (paySys p κ) = 1 := by
  funext s s'
  simp only [twP, paySys_eq_mk, tw10_mk, Matrix.one_apply]
  split_ifs
  · exact one_eq_dg.symm
  · ext m f; simp

/-- (L1) of `C40b_the_formal_dance_of_payment_systems.md`, second equality (exact):
`Dd − B C = 2 • paySys (pT p) (κT p κ)`. -/
theorem L1_schur [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twD (paySys p κ) - twB (paySys p κ) * twC (paySys p κ) =
      (2 : A) • paySys (Payment.pT p) (Payment.κT p κ) := by
  rw [twB_paySys, twC_paySys, dgMat_mul]
  funext s s'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, twD, paySys_eq_mk, tw01_mk,
    dg_eq_mk, mk_sub, smul_mk]
  congr 1
  · ring
  · funext f
    simp only [Pi.sub_apply, Pi.zero_apply, zero_sub]
    rw [ent_sum]; ring

/-- **(L1)** of `C40b_the_formal_dance_of_payment_systems.md` (Lemma 10.6(a), first sentence):
`twP (paySys p κ) = 1`, `twD − twB * twC = (2 : A) • paySys (pT p) (κT p κ)` (exact equalities),
and consequently `CleanStep (paySys p κ) (paySys (pT p) (κT p κ))` (with `Q = 1`). -/
theorem L1 [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twP (paySys p κ) = 1 ∧
    twD (paySys p κ) - twB (paySys p κ) * twC (paySys p κ) =
      (2 : A) • paySys (Payment.pT p) (Payment.κT p κ) ∧
    CleanStep (paySys p κ) (paySys (Payment.pT p) (Payment.κT p κ)) := by
  refine ⟨L1_twP p κ, L1_schur p κ, 1, ?_, ?_, ?_⟩
  · rw [L1_twP, mul_one]; exact MAgree.refl _
  · rw [L1_twP, mul_one]; exact MAgree.refl _
  · rw [mul_one, L1_schur]; exact MAgree.refl _

end L1


end FormalDance
