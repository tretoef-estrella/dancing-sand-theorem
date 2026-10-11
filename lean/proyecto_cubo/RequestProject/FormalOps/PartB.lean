module

public import RequestProject.FormalOps.Defs

/-!
# `C40_the_formal_operators.md`: Part B — the algebra and its action

(B1) is in `Bf.lean` (`Bf.instRing`, `Bf.instAlgebra`, `Bf.smul_mul`, `Bf.mul_smul` and the simp
lemmas `Bf.coef_add`, `Bf.coef_mul`, `Bf.coef_one`, `Bf.coef_fd`, `Bf.coef_dg`). Here:

* (B2) `flD_one`, `flD_add`, `flD_mul` (and `B2`, `flDHom`: `flD N W` as a ring hom
  `(ℤ → A) →+* Module.End A (N.ι → A)`);
* (B3) `B3`;
* (B4) `act_bound`, `act_one`, `act_add`, `act_smul`, `act_mul`, `act_fd`, `act_dg`, collected
  in `B4`.

Hypotheses. With the floor written `(W − N.wt i) / 2` (integer division), the identities
`(W − (w − 2a)) / 2 = (W − w) / 2 + a` hold for every integer `w`, so (top W) is not needed in
Parts B: (B3) and (B4) are stated without it (more general). In (B4), (nil BN) is used only
for the independence of the bound, for multiplicativity and for `act (fd m) = N.Fd m`;
`act 1 = 1`, additivity, `act (a • x) = a • act x` and `act (dg p) = flD p` hold for every `B`
(resp. every `B ≥ 1`) without (nil).
-/

@[expose] public section

noncomputable section

namespace FormalOps

open DPLattice Finset

variable {A : Type*} [CommRing A] (N : DPLattice A) (W : ℤ)

/-! ### (B2) -/

/-- **(B2)** of `C40_the_formal_operators.md`: `flD N W 1 = 1`. -/
theorem flD_one : flD N W 1 = 1 := by
  apply LinearMap.ext; intro v; funext i; simp

/-- **(B2)** of `C40_the_formal_operators.md`: `flD N W (p + q) = flD N W p + flD N W q`. -/
theorem flD_add (p q : ℤ → A) : flD N W (p + q) = flD N W p + flD N W q := by
  apply LinearMap.ext; intro v; funext i; simp [add_mul]

/-- **(B2)** of `C40_the_formal_operators.md`: `flD N W (p * q) = flD N W p * flD N W q`. -/
theorem flD_mul (p q : ℤ → A) : flD N W (p * q) = flD N W p * flD N W q := by
  apply LinearMap.ext; intro v; funext i; simp [mul_assoc]

/-- **(B2)** of `C40_the_formal_operators.md`: `flD N W` as a ring map
`(ℤ → A) →+* Module.End A (N.ι → A)` (pointwise operations on `ℤ → A`). -/
def flDHom : (ℤ → A) →+* Module.End A (N.ι → A) where
  toFun := flD N W
  map_one' := flD_one N W
  map_mul' := flD_mul N W
  map_zero' := by apply LinearMap.ext; intro v; funext i; simp
  map_add' := flD_add N W

/-- **(B2)** of `C40_the_formal_operators.md`, collected:
`flD N W 1 = 1`, `flD N W (p + q) = flD N W p + flD N W q`,
`flD N W (p * q) = flD N W p * flD N W q`. -/
theorem B2 : flD N W 1 = 1 ∧ (∀ p q : ℤ → A, flD N W (p + q) = flD N W p + flD N W q) ∧
    (∀ p q : ℤ → A, flD N W (p * q) = flD N W p * flD N W q) :=
  ⟨flD_one N W, flD_add N W, flD_mul N W⟩

lemma flD_zero : flD N W (0 : ℤ → A) = 0 := (flDHom N W).map_zero

lemma flD_sum (s : Finset ℕ) (g : ℕ → ℤ → A) :
    flD N W (fun f => ∑ a ∈ s, g a f) = ∑ a ∈ s, flD N W (g a) := by
  apply LinearMap.ext; intro v; funext i
  simp [LinearMap.sum_apply, Finset.sum_apply, Finset.sum_mul]

lemma flD_const_mul (c : A) (p : ℤ → A) : flD N W (fun f => c * p f) = c • flD N W p := by
  apply LinearMap.ext; intro v; funext i; simp [mul_assoc]

lemma flD_single (p : ℤ → A) (i : N.ι) :
    flD N W p (Pi.single i 1) = p ((W - N.wt i) / 2) • (Pi.single i 1 : N.ι → A) := by
  funext j; by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-! ### (B3) -/

/-- **(B3)** of `C40_the_formal_operators.md` (floor shift): for every `a : ℕ` and `p : ℤ → A`,
`N.Fd a * flD N W p = flD N W (fun f => p (f − a)) * N.Fd a`.
(More general than the file: (top W) is not needed.) -/
theorem B3 (a : ℕ) (p : ℤ → A) :
    N.Fd a * flD N W p = flD N W (fun f => p (f - a)) * N.Fd a := by
  refine ext_single fun i => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, flD_single, map_smul]
  funext j
  simp only [flD_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : N.wt j = N.wt i - 2 * a
  · congr 2; rw [hj]; omega
  · rw [N.isDP.W_F i a j hj]; simp

/-! ### (B4) -/

variable {N W}

lemma act_apply (B : ℕ) (x : Bf A) (v : N.ι → A) :
    act N W B x v = ∑ m ∈ range B, flD N W (x.coef m) (N.Fd m v) := by
  simp [act, LinearMap.sum_apply]

lemma coef_add_fun (x y : Bf A) (m : ℕ) : (x + y).coef m = x.coef m + y.coef m := rfl

/-- **(B4)** (independence of the bound), auxiliary form: under (nil BN),
`act N W B x = act N W BN x` for `B ≥ BN`. -/
lemma act_bound_aux {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) (B : ℕ) (hB : BN ≤ B) (x : Bf A) :
    act N W B x = act N W BN x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
  rw [act, act, Finset.sum_range_add, add_eq_left]
  exact Finset.sum_eq_zero fun j _ => by rw [hnil (BN + j) (by omega), mul_zero]

/-- **(B4)** of `C40_the_formal_operators.md` (independence of the bound): under (nil BN), for
all `B, B' ≥ BN`, `act N W B x = act N W B' x`. (Without (top W): more general.) -/
theorem act_bound {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) {B B' : ℕ} (hB : BN ≤ B)
    (hB' : BN ≤ B') (x : Bf A) : act N W B x = act N W B' x := by
  rw [act_bound_aux hnil B hB, act_bound_aux hnil B' hB']

/-- **(B4)** of `C40_the_formal_operators.md`: `act N W B 1 = 1` if `B ≥ 1` (for every `B ≥ 1`,
without (top W) and (nil BN): more general). -/
theorem act_one {B : ℕ} (hB : 1 ≤ B) : act N W B (1 : Bf A) = 1 := by
  rw [act, Finset.sum_eq_single 0]
  · rw [show (1 : Bf A).coef 0 = 1 from funext fun f => by simp, flD_one, N.isDP.P0_F, one_mul]
  · intro m _ hm
    rw [show (1 : Bf A).coef m = 0 from funext fun f => by simp [hm], flD_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **(B4)** of `C40_the_formal_operators.md`: `act N W B (x + y) = act N W B x + act N W B y`
(for every `B`: more general). -/
theorem act_add (B : ℕ) (x y : Bf A) : act N W B (x + y) = act N W B x + act N W B y := by
  simp only [act, coef_add_fun, flD_add, add_mul, Finset.sum_add_distrib]

/-- **(B4)** of `C40_the_formal_operators.md`: `act N W B (a • x) = a • act N W B x`
(for every `B`: more general). -/
theorem act_smul (B : ℕ) (a : A) (x : Bf A) : act N W B (a • x) = a • act N W B x := by
  simp only [act, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show (a • x).coef m = fun f => a * x.coef m f from rfl, flD_const_mul, smul_mul_assoc]

/-- **(B4)** of `C40_the_formal_operators.md`: under (nil BN), `act N W B (Bf.fd m) = N.Fd m`
for every `m` and every `B ≥ BN`. -/
theorem act_fd {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) {B : ℕ} (hB : BN ≤ B) (m : ℕ) :
    act N W B (Bf.fd m : Bf A) = N.Fd m := by
  have hz : ∀ m', m' ≠ m → (Bf.fd m : Bf A).coef m' = 0 := fun m' h =>
    funext fun f => by simp [h]
  by_cases hm : m < B
  · rw [act, Finset.sum_eq_single m]
    · rw [show (Bf.fd m : Bf A).coef m = 1 from funext fun f => by simp, flD_one, one_mul]
    · intro m' _ h; rw [hz m' h, flD_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_range.2 hm) h
  · rw [hnil m (by omega), act]
    exact Finset.sum_eq_zero fun m' hm' => by
      rw [hz m' (by rw [Finset.mem_range] at hm'; omega), flD_zero, zero_mul]

/-- **(B4)** of `C40_the_formal_operators.md`: `act N W B (Bf.dg p) = flD N W p` if `B ≥ 1`
(for every `B ≥ 1`, without (top W) and (nil BN): more general). -/
theorem act_dg {B : ℕ} (hB : 1 ≤ B) (p : ℤ → A) : act N W B (Bf.dg p) = flD N W p := by
  rw [act, Finset.sum_eq_single 0]
  · rw [show (Bf.dg p).coef 0 = p from funext fun f => by simp, N.isDP.P0_F, mul_one]
  · intro m _ hm
    rw [show (Bf.dg p).coef m = 0 from funext fun f => by simp [hm], flD_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

variable (N W) in
lemma act_term (x y : Bf A) (a b : ℕ) :
    (flD N W (x.coef a) * N.Fd a) * (flD N W (y.coef b) * N.Fd b) =
      ((a + b).choose a : A) • (flD N W (fun f => x.coef a f * y.coef b (f - a)) * N.Fd (a + b)) := by
  calc (flD N W (x.coef a) * N.Fd a) * (flD N W (y.coef b) * N.Fd b)
      = flD N W (x.coef a) * (N.Fd a * flD N W (y.coef b)) * N.Fd b := by
        simp only [mul_assoc]
    _ = flD N W (x.coef a) * (flD N W (fun f => y.coef b (f - a)) * N.Fd a) * N.Fd b := by
        rw [B3]
    _ = (flD N W (x.coef a) * flD N W (fun f => y.coef b (f - a))) * (N.Fd a * N.Fd b) := by
        simp only [mul_assoc]
    _ = _ := by
        rw [← flD_mul, Module.End.mul_eq_comp (N.Fd a), N.isDP.P1_F, choose_natAdd, mul_smul_comm]
        push_cast
        rfl

/-- **(B4)** of `C40_the_formal_operators.md` (multiplicativity): under (nil BN), for `B ≥ BN`,
`act N W B (x * y) = act N W B x * act N W B y`. (Without (top W): more general.) -/
theorem act_mul {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) {B : ℕ} (hB : BN ≤ B) (x y : Bf A) :
    act N W B (x * y) = act N W B x * act N W B y := by
  set G : ℕ → ℕ → Module.End A (N.ι → A) := fun a b => ((a + b).choose a : A) •
    (flD N W (fun f => x.coef a f * y.coef b (f - a)) * N.Fd (a + b)) with hG
  have hG0 : ∀ a b, B ≤ a + b → G a b = 0 := fun a b h => by
    simp only [G, hnil (a + b) (by omega), mul_zero, smul_zero]
  have hL : act N W B x * act N W B y = ∑ a ∈ range B, ∑ b ∈ range (B - a), G a b := by
    unfold act
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le B a))]
    · exact Finset.sum_congr rfl fun b _ => act_term N W x y a b
    · intro b _ hb
      rw [Finset.mem_range, not_lt] at hb
      rw [act_term]; exact hG0 a b (by omega)
  have hR : act N W B (x * y) = ∑ a ∈ range B, ∑ b ∈ range (B - a), G a b := by
    unfold act
    have hm : ∀ m, flD N W ((x * y).coef m) * N.Fd m = ∑ a ∈ range (m + 1), G a (m - a) := by
      intro m
      rw [show (x * y).coef m = fun f => ∑ a ∈ range (m + 1),
          (m.choose a : A) * (x.coef a f * y.coef (m - a) (f - a)) from
          funext fun f => by simp [mul_assoc]]
      rw [flD_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mem_range] at ha
      simp only [G]
      rw [flD_const_mul, smul_mul_assoc, Nat.add_sub_cancel' (by omega : a ≤ m)]
    simp_rw [hm]
    rw [Finset.sum_comm' (t' := range B) (s' := fun a => Ico a B)]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_Ico_eq_sum_range]
      exact Finset.sum_congr rfl fun b _ => by rw [Nat.add_sub_cancel_left]
    · intro m a
      simp only [Finset.mem_range, Finset.mem_Ico]
      omega
  rw [hL, hR]

/-- **(B4)** of `C40_the_formal_operators.md` (the action), collected: under (nil BN), for all
`B, B' ≥ BN`: independence of the bound, `act 1 = 1` (if `B ≥ 1`), additivity, compatibility with
scalars, multiplicativity, `act (fd m) = N.Fd m` and `act (dg p) = flD N W p` (if `B ≥ 1`).
(Stated without (top W), which is not needed: more general.) -/
theorem B4 {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) {B B' : ℕ} (hB : BN ≤ B) (hB' : BN ≤ B') :
    (∀ x : Bf A, act N W B x = act N W B' x) ∧
    (1 ≤ B → act N W B (1 : Bf A) = 1) ∧
    (∀ x y : Bf A, act N W B (x + y) = act N W B x + act N W B y) ∧
    (∀ (a : A) (x : Bf A), act N W B (a • x) = a • act N W B x) ∧
    (∀ x y : Bf A, act N W B (x * y) = act N W B x * act N W B y) ∧
    (∀ m : ℕ, act N W B (Bf.fd m : Bf A) = N.Fd m) ∧
    (1 ≤ B → ∀ p : ℤ → A, act N W B (Bf.dg p) = flD N W p) :=
  ⟨act_bound hnil hB hB', act_one, act_add B, act_smul B, act_mul hnil hB, act_fd hnil hB,
    fun h p => act_dg h p⟩

end FormalOps
