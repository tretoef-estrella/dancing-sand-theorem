module

public import RequestProject.RingK.PartK

/-!
# `C47_the_ring_K_and_covariant_systems.md`: Part S — the homomorphism `Θ` (Lemma 10.13 (b))

(S0)–(S5). `p̄`, `q̄` denote `p.map red`, `q.map red`, seen in `PowerSeries (ZMod 2)`.
-/

@[expose] public section

noncomputable section

namespace RingK

open Polynomial FormalOps TrivSqZeroExt

/-- Helper for Part S of `C47_the_ring_K_and_covariant_systems.md`: the constant coefficient of
`q̄` is nonzero. -/
lemma constantCoeff_qbar (r : KRep) :
    PowerSeries.constantCoeff ((r.q.map red : PowerSeries (ZMod 2))) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, coeff_map]
  exact (isUnit_iff_red_ne_zero _).1 r.hq

/-- Helper for (S0) of `C47_the_ring_K_and_covariant_systems.md`: `P Q' = P' Q` gives
`P/Q = P'/Q'` in `PowerSeries (ZMod 2)`. -/
lemma ps_frac_eq (P Q P' Q' : (ZMod 2)[X])
    (hQ : PowerSeries.constantCoeff (Q : PowerSeries (ZMod 2)) ≠ 0)
    (hQ' : PowerSeries.constantCoeff (Q' : PowerSeries (ZMod 2)) ≠ 0) (h : P * Q' = P' * Q) :
    (P : PowerSeries (ZMod 2)) * (Q : PowerSeries (ZMod 2))⁻¹ =
      (P' : PowerSeries (ZMod 2)) * (Q' : PowerSeries (ZMod 2))⁻¹ := by
  have e1 := PowerSeries.mul_inv_cancel _ hQ
  have e2 := PowerSeries.mul_inv_cancel _ hQ'
  have h' : (P : PowerSeries (ZMod 2)) * Q' = P' * Q := by
    rw [← Polynomial.coe_mul, h, Polynomial.coe_mul]
  linear_combination ((Q : PowerSeries (ZMod 2))⁻¹ * (Q' : PowerSeries (ZMod 2))⁻¹) * h'
    - ((P : PowerSeries (ZMod 2)) * (Q : PowerSeries (ZMod 2))⁻¹) * e2
    + ((P' : PowerSeries (ZMod 2)) * (Q' : PowerSeries (ZMod 2))⁻¹) * e1

/-- Helper for Part S of `C47_the_ring_K_and_covariant_systems.md`: `fst (thetaRep r) = red a`. -/
@[simp] lemma thetaRep_fst (r : KRep) : (thetaRep r).fst = red r.a := by simp [thetaRep]

/-- Helper for Part S of `C47_the_ring_K_and_covariant_systems.md`: `snd (thetaRep r) = p̄ q̄⁻¹`. -/
@[simp] lemma thetaRep_snd (r : KRep) :
    (thetaRep r).snd = (r.p.map red : PowerSeries (ZMod 2)) * (r.q.map red : PowerSeries (ZMod 2))⁻¹ := by
  simp [thetaRep]

/-- **(S0)** of `C47_the_ring_K_and_covariant_systems.md`: if `r.eval = r'.eval` then
`thetaRep r = thetaRep r'`. -/
theorem S0 (r r' : KRep) (h : r.eval = r'.eval) : thetaRep r = thetaRep r' := by
  obtain ⟨ha, hpq⟩ := K2 r r' h
  refine TrivSqZeroExt.ext (by simp [ha]) ?_
  simp only [thetaRep_snd]
  exact ps_frac_eq _ _ _ _ (constantCoeff_qbar r) (constantCoeff_qbar r')
    (by rw [← Polynomial.map_mul, hpq, Polynomial.map_mul])

/-- **(S0)** of `C47_the_ring_K_and_covariant_systems.md`, second half:
`theta (r.eval) = thetaRep r` for every `r`. -/
theorem S0_theta (r : KRep) : theta r.eval = thetaRep r := by
  have hm : r.eval ∈ Kr := ⟨r, rfl⟩
  rw [theta, dif_pos hm]
  exact S0 _ _ (Classical.choose_spec hm)

/-- **(S1)** of `C47_the_ring_K_and_covariant_systems.md`: `theta` is additive on `Kr`. -/
theorem S1_add {ϑ ϑ' : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (h' : ϑ' ∈ Kr) :
    theta (ϑ + ϑ') = theta ϑ + theta ϑ' := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨r', rfl⟩ := h'
  obtain ⟨s, hs, ha, hp, hq⟩ := K3_add_rep r r'
  rw [← hs, S0_theta, S0_theta, S0_theta]
  have e1 := PowerSeries.mul_inv_cancel _ (constantCoeff_qbar r)
  have e2 := PowerSeries.mul_inv_cancel _ (constantCoeff_qbar r')
  refine TrivSqZeroExt.ext (by simp [ha]) ?_
  simp only [thetaRep_snd, snd_add, hp, hq, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.coe_add, Polynomial.coe_mul, PowerSeries.mul_inv_rev]
  linear_combination
    ((r.p.map red : PowerSeries (ZMod 2)) * (r.q.map red : PowerSeries (ZMod 2))⁻¹) * e2
    + ((r'.p.map red : PowerSeries (ZMod 2)) * (r'.q.map red : PowerSeries (ZMod 2))⁻¹) * e1

/-- **(S1)** of `C47_the_ring_K_and_covariant_systems.md`: `theta` is multiplicative on `Kr`. -/
theorem S1_mul {ϑ ϑ' : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (h' : ϑ' ∈ Kr) :
    theta (ϑ * ϑ') = theta ϑ * theta ϑ' := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨r', rfl⟩ := h'
  obtain ⟨s, hs, ha, hp, hq⟩ := K3_mul_rep r r'
  rw [← hs, S0_theta, S0_theta, S0_theta]
  have e1 := PowerSeries.mul_inv_cancel _ (constantCoeff_qbar r)
  have e2 := PowerSeries.mul_inv_cancel _ (constantCoeff_qbar r')
  refine TrivSqZeroExt.ext (by simp [ha]) ?_
  simp only [thetaRep_snd, snd_mul, thetaRep_fst, hp, hq, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C,
    PowerSeries.mul_inv_rev, op_smul_eq_smul, PowerSeries.smul_eq_C_mul, red_two, map_zero,
    zero_mul, add_zero]
  linear_combination
    (PowerSeries.C (red r.a) * (r'.p.map red : PowerSeries (ZMod 2)) *
      (r'.q.map red : PowerSeries (ZMod 2))⁻¹) * e1
    + (PowerSeries.C (red r'.a) * (r.p.map red : PowerSeries (ZMod 2)) *
      (r.q.map red : PowerSeries (ZMod 2))⁻¹) * e2

/-- **(S1)** of `C47_the_ring_K_and_covariant_systems.md`: `theta (fun _ => a) = inl (red a)`. -/
theorem S1_const (c : ℤ_[2]) : theta (fun _ => c) = inl (red c) := by
  let r : KRep := ⟨c, 0, 1, by simp, by simp⟩
  have hr : r.eval = fun _ => c := by funext y; simp [r, KRep.eval]
  rw [← hr, S0_theta]
  exact TrivSqZeroExt.ext (by simp [r]) (by simp [r])

/-- **(S1)** of `C47_the_ring_K_and_covariant_systems.md`: `theta 1 = 1`. -/
theorem S1_one : theta 1 = 1 := by
  have := S1_const 1
  rw [map_one, inl_one] at this
  exact this

/-- **(S1)** of `C47_the_ring_K_and_covariant_systems.md`:
`theta (fun y => a * ϑ y) = inl (red a) * theta ϑ` on `Kr`. -/
theorem S1_smul (c : ℤ_[2]) {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) :
    theta (fun y => c * ϑ y) = inl (red c) * theta ϑ := by
  rw [← S1_const c, ← S1_mul (K3_const c) h]
  rfl

/-- **(S1)** of `C47_the_ring_K_and_covariant_systems.md`, all together. -/
theorem S1 :
    (∀ ϑ ∈ Kr, ∀ ϑ' ∈ Kr, theta (ϑ + ϑ') = theta ϑ + theta ϑ') ∧
    (∀ ϑ ∈ Kr, ∀ ϑ' ∈ Kr, theta (ϑ * ϑ') = theta ϑ * theta ϑ') ∧
    theta 1 = 1 ∧
    (∀ a : ℤ_[2], theta (fun _ => a) = inl (red a)) ∧
    (∀ a : ℤ_[2], ∀ ϑ ∈ Kr, theta (fun y => a * ϑ y) = inl (red a) * theta ϑ) :=
  ⟨fun _ h _ h' => S1_add h h', fun _ h _ h' => S1_mul h h', S1_one, S1_const,
    fun a _ h => S1_smul a h⟩

/-- **(S2)** of `C47_the_ring_K_and_covariant_systems.md` (shift invariance):
`theta (fun y => ϑ (y − e)) = theta ϑ` on `Kr`. -/
theorem S2 {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (e : ℤ_[2]) :
    theta (fun y => ϑ (y - e)) = theta ϑ := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨s, hs, ha, hp, hq⟩ := K4_rep r e
  rw [← hs, S0_theta, S0_theta]
  have hcomp : ∀ P : ℤ_[2][X], (P.comp (X - C (2 * e))).map red = P.map red := by
    intro P
    rw [Polynomial.map_comp]
    simp [red_two]
  have hpe : red (r.p.eval (-(2 * e))) = 0 := by
    rw [← mul_neg, red_eval_two_mul, r.hp, map_zero]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [ha, red_two]
  · simp only [thetaRep_snd]
    refine ps_frac_eq _ _ _ _ (constantCoeff_qbar s) (constantCoeff_qbar r) ?_
    rw [hp, hq]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, hcomp, hpe, map_zero,
      zero_mul, sub_zero]
    ring

/-- **(S3)** of `C47_the_ring_K_and_covariant_systems.md` (kernel): for `ϑ ∈ Kr`,
`theta ϑ = 0 ↔ ∃ ψ ∈ Kr, ϑ = fun y => 2 * ψ y`. -/
theorem S3 {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) :
    theta ϑ = 0 ↔ ∃ ψ ∈ Kr, ϑ = fun y => 2 * ψ y := by
  constructor
  · obtain ⟨r, rfl⟩ := h
    rw [S0_theta]
    intro h0
    have hf := congrArg TrivSqZeroExt.fst h0
    have hsn := congrArg TrivSqZeroExt.snd h0
    simp only [thetaRep_fst, thetaRep_snd, fst_zero, snd_zero] at hf hsn
    obtain ⟨a₁, ha₁⟩ := (red_eq_zero_iff _).1 hf
    have hP : (r.p.map red : PowerSeries (ZMod 2)) = 0 := by
      have e1 := PowerSeries.mul_inv_cancel _ (constantCoeff_qbar r)
      linear_combination (r.q.map red : PowerSeries (ZMod 2)) * hsn
        - (r.p.map red : PowerSeries (ZMod 2)) * e1
    rw [Polynomial.coe_eq_zero_iff] at hP
    have hmem : r.p ∈ Ideal.span {C (2 : ℤ_[2])} := by
      have : Ideal.span {C (2 : ℤ_[2])} = (Ideal.span {(2 : ℤ_[2])}).map C := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [this, Ideal.mem_map_C_iff]
      intro n
      have hn : red (r.p.coeff n) = 0 := by rw [← coeff_map, hP, coeff_zero]
      obtain ⟨z, hz⟩ := (red_eq_zero_iff _).1 hn
      exact Ideal.mem_span_singleton.2 ⟨z, hz⟩
    obtain ⟨p₁, hp₁⟩ := Ideal.mem_span_singleton.1 hmem
    have hp₁0 : p₁.coeff 0 = 0 := by
      have := r.hp
      rw [hp₁, coeff_C_mul] at this
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    refine ⟨KRep.eval ⟨a₁, p₁, r.q, hp₁0, r.hq⟩, ⟨_, rfl⟩, ?_⟩
    funext y
    simp only [KRep.eval, ha₁, hp₁, eval_mul, eval_C]
    ring
  · rintro ⟨ψ, hψ, rfl⟩
    rw [S1_smul 2 hψ, red_two, inl_zero, zero_mul]

/-- **(S4)** of `C47_the_ring_K_and_covariant_systems.md`: for `ϑ = r.eval` with `IsUnit r.a`,
`theta (fun y => Ring.inverse (ϑ y)) * theta ϑ = 1`. -/
theorem S4 (r : KRep) (hu : IsUnit r.a) :
    theta (fun y => Ring.inverse (r.eval y)) * theta r.eval = 1 := by
  rw [← S1_mul (K5 r hu).2 ⟨r, rfl⟩]
  have : (fun y => Ring.inverse (r.eval y)) * r.eval = 1 :=
    funext fun y => Ring.inverse_mul_cancel _ ((K5 r hu).1 y)
  rw [this, S1_one]

/-- **(S5)** of `C47_the_ring_K_and_covariant_systems.md` (the constant term):
`fst (theta ϑ) = red r.a`, and `theta ϑ * theta ϑ = 0` when `r.a` is even. -/
theorem S5 (r : KRep) :
    (theta r.eval).fst = red r.a ∧
      ((∃ z, r.a = 2 * z) → theta r.eval * theta r.eval = 0) := by
  rw [S0_theta]
  refine ⟨thetaRep_fst r, ?_⟩
  intro hz
  have hred : red r.a = 0 := (red_eq_zero_iff _).2 hz
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [hred]
  · simp [hred]

end RingK
