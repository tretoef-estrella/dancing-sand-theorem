module

public import RequestProject.Conjugation.Defs

/-!
# `C45_conjugation_and_general_eta.md`: Part C, (C1) — `cj u` is a ring endomorphism

* operators: `cj_one`, `cj_add`, `cj_mul`, `cj_smul`, `cj_cj`, `cj_one_left`, `agree_cj`
  (and `cj_zero`, `cj_sub`, `cj_sum`, the ring hom `cjHom`);
* systems: `cjSys_one`, `cjSys_mul`, `cjSys_sub`, `cjSys_smul`, `magree_cjSys`;
* everything collected in `C1`.
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset

variable {A : Type*} [CommRing A]

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj u 1 = 1`. -/
theorem cj_one (u : A) : cj u (1 : Bf A) = 1 := by
  ext j f; simp only [coef_cj, Bf.coef_one]; split_ifs with h <;> simp [h]

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj u (x + y) = cj u x + cj u y`. -/
theorem cj_add (u : A) (x y : Bf A) : cj u (x + y) = cj u x + cj u y := by
  ext j f; simp [mul_add]

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj u (x * y) = cj u x * cj u y`. -/
theorem cj_mul (u : A) (x y : Bf A) : cj u (x * y) = cj u x * cj u y := by
  ext m f
  simp only [coef_cj, Bf.coef_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have h : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hp : u ^ m = u ^ a * u ^ (m - a) := by rw [← pow_add, Nat.add_sub_cancel' h]
  rw [hp]; ring

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj u (a • x) = a • cj u x`. -/
theorem cj_smul (u a : A) (x : Bf A) : cj u (a • x) = a • cj u x := by
  ext j f; simp; ring

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj u (cj v x) = cj (u * v) x`. -/
theorem cj_cj (u v : A) (x : Bf A) : cj u (cj v x) = cj (u * v) x := by
  ext j f; simp [mul_pow]; ring

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj 1 x = x`. -/
theorem cj_one_left (x : Bf A) : cj 1 x = x := by
  ext j f; simp

/-- (C1) of `C45_conjugation_and_general_eta.md`: `Agree x y → Agree (cj u x) (cj u y)`. -/
theorem agree_cj (u : A) {x y : Bf A} (h : Agree x y) : Agree (cj u x) (cj u y) :=
  fun m f hf => by simp [h m f hf]

/-- (C1) of `C45_conjugation_and_general_eta.md` (auxiliary): `cj u 0 = 0`. -/
lemma cj_zero (u : A) : cj u (0 : Bf A) = 0 := by ext j f; simp

/-- (C1) of `C45_conjugation_and_general_eta.md` (auxiliary): `cj u (x - y) = cj u x - cj u y`. -/
lemma cj_sub (u : A) (x y : Bf A) : cj u (x - y) = cj u x - cj u y := by
  ext j f; simp [mul_sub]

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cj u` as a ring endomorphism of `Bf A`. -/
def cjHom (u : A) : Bf A →+* Bf A where
  toFun := cj u
  map_one' := cj_one u
  map_mul' := cj_mul u
  map_zero' := cj_zero u
  map_add' := cj_add u

/-- (C1) of `C45_conjugation_and_general_eta.md` (auxiliary): `cj u` commutes with finite
sums. -/
lemma cj_sum {ι : Type*} (s : Finset ι) (u : A) (x : ι → Bf A) :
    cj u (∑ i ∈ s, x i) = ∑ i ∈ s, cj u (x i) :=
  map_sum (cjHom u) x s

/-! ### Systems -/

section Sys

variable {n : Type*}

/-- (C1) of `C45_conjugation_and_general_eta.md`: `cjSys 1 u w 1 = 1`. -/
theorem cjSys_one [DecidableEq n] (u : Aˣ) (w : n → Aˣ) :
    cjSys 1 u w (1 : Matrix n n (Bf A)) = 1 := by
  funext s s'
  by_cases h : s = s'
  · subst h; simp [cjSys, cj_one]
  · simp [cjSys, h, cj_zero]

/-- (C1) of `C45_conjugation_and_general_eta.md`:
`cjSys c u w G * cjSys c' u w H = cjSys (c * c') u w (G * H)`. -/
theorem cjSys_mul [Fintype n] (c c' u : Aˣ) (w : n → Aˣ) (G H : Matrix n n (Bf A)) :
    cjSys c u w G * cjSys c' u w H = cjSys (c * c') u w (G * H) := by
  funext s s'
  simp only [Matrix.mul_apply, cjSys_apply, Bf.smul_mul, Bf.mul_smul, smul_smul, cj_sum,
    Finset.smul_sum, cj_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  rw [← Units.val_mul]
  congr 1
  apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel

/-- (C1) of `C45_conjugation_and_general_eta.md`:
`cjSys c u w (G − H) = cjSys c u w G − cjSys c u w H`. -/
theorem cjSys_sub (c u : Aˣ) (w : n → Aˣ) (G H : Matrix n n (Bf A)) :
    cjSys c u w (G - H) = cjSys c u w G - cjSys c u w H := by
  funext s s'
  simp [cjSys_apply, cj_sub, smul_sub]

/-- (C1) of `C45_conjugation_and_general_eta.md`:
`cjSys c u w (a • G) = a • cjSys c u w G`. -/
theorem cjSys_smul (c u : Aˣ) (w : n → Aˣ) (a : A) (G : Matrix n n (Bf A)) :
    cjSys c u w (a • G) = a • cjSys c u w G := by
  funext s s'
  simp only [cjSys_apply, Matrix.smul_apply, cj_smul]
  exact smul_comm _ _ _

/-- (C1) of `C45_conjugation_and_general_eta.md`:
`MAgree G H → MAgree (cjSys c u w G) (cjSys c u w H)`. -/
theorem magree_cjSys (c u : Aˣ) (w : n → Aˣ) {G H : Matrix n n (Bf A)} (h : MAgree G H) :
    MAgree (cjSys c u w G) (cjSys c u w H) :=
  fun s s' => (agree_cj _ (h s s')).smul _

end Sys

/-- **(C1)** of `C45_conjugation_and_general_eta.md` (`cj u` is a ring endomorphism), collected:
`cj u 1 = 1`, `cj u (x + y) = cj u x + cj u y`, `cj u (x * y) = cj u x * cj u y`,
`cj u (a • x) = a • cj u x`, `cj u (cj v x) = cj (u * v) x`, `cj 1 x = x`,
`Agree x y → Agree (cj u x) (cj u y)`; and for systems over a `Fintype n` with `DecidableEq`:
`cjSys 1 u w 1 = 1`, `cjSys c u w G * cjSys c' u w H = cjSys (c * c') u w (G * H)`,
`cjSys c u w (G − H) = cjSys c u w G − cjSys c u w H`, `cjSys c u w (a • G) = a • cjSys c u w G`,
`MAgree G H → MAgree (cjSys c u w G) (cjSys c u w H)`. -/
theorem C1 (n : Type*) [Fintype n] [DecidableEq n] :
    (∀ u : A, cj u (1 : Bf A) = 1) ∧
    (∀ (u : A) (x y : Bf A), cj u (x + y) = cj u x + cj u y) ∧
    (∀ (u : A) (x y : Bf A), cj u (x * y) = cj u x * cj u y) ∧
    (∀ (u a : A) (x : Bf A), cj u (a • x) = a • cj u x) ∧
    (∀ (u v : A) (x : Bf A), cj u (cj v x) = cj (u * v) x) ∧
    (∀ x : Bf A, cj 1 x = x) ∧
    (∀ (u : A) (x y : Bf A), Agree x y → Agree (cj u x) (cj u y)) ∧
    (∀ (u : Aˣ) (w : n → Aˣ), cjSys 1 u w (1 : Matrix n n (Bf A)) = 1) ∧
    (∀ (c c' u : Aˣ) (w : n → Aˣ) (G H : Matrix n n (Bf A)),
      cjSys c u w G * cjSys c' u w H = cjSys (c * c') u w (G * H)) ∧
    (∀ (c u : Aˣ) (w : n → Aˣ) (G H : Matrix n n (Bf A)),
      cjSys c u w (G - H) = cjSys c u w G - cjSys c u w H) ∧
    (∀ (c u : Aˣ) (w : n → Aˣ) (a : A) (G : Matrix n n (Bf A)),
      cjSys c u w (a • G) = a • cjSys c u w G) ∧
    (∀ (c u : Aˣ) (w : n → Aˣ) (G H : Matrix n n (Bf A)),
      MAgree G H → MAgree (cjSys c u w G) (cjSys c u w H)) :=
  ⟨cj_one, cj_add, cj_mul, cj_smul, cj_cj, cj_one_left, fun u _ _ h => agree_cj u h, cjSys_one,
    cjSys_mul, cjSys_sub, cjSys_smul, fun c u w _ _ h => magree_cjSys c u w h⟩

end Conjugation
