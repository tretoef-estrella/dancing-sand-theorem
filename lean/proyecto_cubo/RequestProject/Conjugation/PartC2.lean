module

public import RequestProject.Conjugation.PartC1

/-!
# `C45_conjugation_and_general_eta.md`: Part C, (C2) and (C3) — the twist map, the `V`-split,
# a clean move

* (C2) `twP_cjSys`, `twC_cjSys`, `twB_cjSys`, `twD_cjSys`, `vsplit_cjSys` (exact equalities),
  collected in `C2`;
* (C3) `cleanStep_cjSys`, `cleanStep_vsplit_cjSys`, collected in `C3`.
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset

variable {A : Type*} [CommRing A] {n : Type*}

/-- (C2) of `C45_conjugation_and_general_eta.md` (exact equality):
`twP (cjSys c u w G) = cjSys (c * u) (u ^ 2) w (twP G)`. -/
theorem twP_cjSys (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) :
    twP (cjSys c u w G) = cjSys (c * u) (u ^ 2) w (twP G) := by
  funext s s'; ext q f
  simp only [twP, cjSys_apply, coef_tw10, Bf.coef_smul, coef_cj]
  push_cast
  ring

/-- (C2) of `C45_conjugation_and_general_eta.md` (exact equality):
`twC (cjSys c u w G) = cjSys c (u ^ 2) w (twC G)`. -/
theorem twC_cjSys (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) :
    twC (cjSys c u w G) = cjSys c (u ^ 2) w (twC G) := by
  funext s s'; ext q f
  simp only [twC, cjSys_apply, coef_tw11, Bf.coef_smul, coef_cj]
  push_cast
  ring

/-- (C2) of `C45_conjugation_and_general_eta.md` (exact equality):
`twB (cjSys c u w G) = cjSys c (u ^ 2) w (twB G)`. -/
theorem twB_cjSys (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) :
    twB (cjSys c u w G) = cjSys c (u ^ 2) w (twB G) := by
  funext s s'; ext q f
  simp only [twB, cjSys_apply, coef_tw00, Bf.coef_smul, coef_cj]
  push_cast
  ring

/-- (C2) of `C45_conjugation_and_general_eta.md` (exact equality):
`twD (cjSys c u w G) = cjSys (c * u⁻¹) (u ^ 2) w (twD G)`. -/
theorem twD_cjSys (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) :
    twD (cjSys c u w G) = cjSys (c * u⁻¹) (u ^ 2) w (twD G) := by
  funext s s'; ext q f
  rcases q with _ | q
  · simp [twD, cjSys_apply]
  · have key : ((c * u⁻¹ * w s * (w s')⁻¹ : Aˣ) : A) * ((u ^ 2 : Aˣ) : A) ^ (q + 1) =
        ((c * w s * (w s')⁻¹ : Aˣ) : A) * (u : A) ^ (2 * q + 1) := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
        ← Units.val_mul]
      congr 1
      rw [← pow_mul, show 2 * (q + 1) = (2 * q + 1) + 1 by ring, pow_succ]
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
    simp only [twD, cjSys_apply, coef_tw01_succ, Bf.coef_smul, coef_cj]
    linear_combination (-(((2 * q + 2 : ℕ) : A) * Doubling.dfi (q + 1) *
      (G s s').coef (2 * q + 1) (2 * f))) * key

/-- (C2) of `C45_conjugation_and_general_eta.md` (exact equality):
`vsplit (cjSys c u w G) = cjSys c u (fun q => w q.1 * u ^ (q.2 : ℕ)) (vsplit G)`. -/
theorem vsplit_cjSys (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) :
    vsplit (cjSys c u w G) = cjSys c u (fun q => w q.1 * u ^ (q.2 : ℕ)) (vsplit G) := by
  funext q q'
  obtain ⟨s, b⟩ := q
  obtain ⟨s', b'⟩ := q'
  fin_cases b <;> fin_cases b'
  · simp [vsplit, cjSys_apply]
  · simp [vsplit, cjSys_apply, cj_zero]
  · ext m g
    simp [vsplit, cjSys_apply]
    ring
  · ext m g
    simp [vsplit, cjSys_apply]
    linear_combination (-((c : A) * (w s : A) * ((w s')⁻¹ : Aˣ) *
      ((u : A) ^ m * (G s s').coef m (g + 1)))) * Units.mul_inv u

/-- **(C2)** of `C45_conjugation_and_general_eta.md` (the twist map and the `V`-split), collected;
all five are exact equalities. -/
theorem C2 (c u : Aˣ) (w : n → Aˣ) (G : Matrix n n (Bf A)) :
    twP (cjSys c u w G) = cjSys (c * u) (u ^ 2) w (twP G) ∧
    twC (cjSys c u w G) = cjSys c (u ^ 2) w (twC G) ∧
    twB (cjSys c u w G) = cjSys c (u ^ 2) w (twB G) ∧
    twD (cjSys c u w G) = cjSys (c * u⁻¹) (u ^ 2) w (twD G) ∧
    vsplit (cjSys c u w G) = cjSys c u (fun q => w q.1 * u ^ (q.2 : ℕ)) (vsplit G) :=
  ⟨twP_cjSys c u w G, twC_cjSys c u w G, twB_cjSys c u w G, twD_cjSys c u w G,
    vsplit_cjSys c u w G⟩

/-- (C3) of `C45_conjugation_and_general_eta.md` (a clean move):
`CleanStep G G' → CleanStep (cjSys c u w G) (cjSys (c * u⁻¹) (u ^ 2) w G')`. -/
theorem cleanStep_cjSys [Fintype n] [DecidableEq n] (c u : Aˣ) (w : n → Aˣ)
    {G G' : Matrix n n (Bf A)} (h : CleanStep G G') :
    CleanStep (cjSys c u w G) (cjSys (c * u⁻¹) (u ^ 2) w G') := by
  obtain ⟨Q, hPQ, hQP, hS⟩ := h
  refine ⟨cjSys (c * u)⁻¹ (u ^ 2) w Q, ?_, ?_, ?_⟩
  · rw [twP_cjSys, cjSys_mul, mul_inv_cancel, ← cjSys_one (u ^ 2) w]
    exact magree_cjSys _ _ _ hPQ
  · rw [twP_cjSys, cjSys_mul, inv_mul_cancel, ← cjSys_one (u ^ 2) w]
    exact magree_cjSys _ _ _ hQP
  · have hc : c * (c * u)⁻¹ * c = c * u⁻¹ := by
      apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
    rw [twD_cjSys, twB_cjSys, twC_cjSys, cjSys_mul, cjSys_mul, hc, ← cjSys_sub,
      ← cjSys_smul]
    exact magree_cjSys _ _ _ hS

/-- (C3) of `C45_conjugation_and_general_eta.md` (a split move):
`CleanStep (vsplit G) G'' → CleanStep (vsplit (cjSys c u w G))
(cjSys (c * u⁻¹) (u ^ 2) (fun q => w q.1 * u ^ (q.2 : ℕ)) G'')`. -/
theorem cleanStep_vsplit_cjSys [Fintype n] [DecidableEq n] (c u : Aˣ) (w : n → Aˣ)
    {G : Matrix n n (Bf A)} {G'' : Matrix (n × Fin 2) (n × Fin 2) (Bf A)}
    (h : CleanStep (vsplit G) G'') :
    CleanStep (vsplit (cjSys c u w G))
      (cjSys (c * u⁻¹) (u ^ 2) (fun q => w q.1 * u ^ (q.2 : ℕ)) G'') := by
  rw [vsplit_cjSys]
  exact cleanStep_cjSys _ _ _ h

/-- **(C3)** of `C45_conjugation_and_general_eta.md` (a clean move and a split move), collected. -/
theorem C3 [Fintype n] [DecidableEq n] (c u : Aˣ) (w : n → Aˣ) :
    (∀ G G' : Matrix n n (Bf A), CleanStep G G' →
      CleanStep (cjSys c u w G) (cjSys (c * u⁻¹) (u ^ 2) w G')) ∧
    (∀ (G : Matrix n n (Bf A)) (G'' : Matrix (n × Fin 2) (n × Fin 2) (Bf A)),
      CleanStep (vsplit G) G'' → CleanStep (vsplit (cjSys c u w G))
        (cjSys (c * u⁻¹) (u ^ 2) (fun q => w q.1 * u ^ (q.2 : ℕ)) G'')) :=
  ⟨fun _ _ h => cleanStep_cjSys c u w h, fun _ _ h => cleanStep_vsplit_cjSys c u w h⟩

end Conjugation
