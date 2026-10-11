module

public import RequestProject.RingK.Defs

/-!
# `C47_the_ring_K_and_covariant_systems.md`: Part K — the class `𝒦_r` (Lemma 10.13 (a), (c))

(K1)–(K6). The representations of sums, products, shifts and inverses are the formulas of the
file.
-/

@[expose] public section

noncomputable section

namespace RingK

open Polynomial FormalOps

/-- Helper for Part K of `C47_the_ring_K_and_covariant_systems.md`: `red x = 0` iff `x` is
even. -/
lemma red_eq_zero_iff (x : ℤ_[2]) : red x = 0 ↔ ∃ z, x = 2 * z := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  simp [dvd_def]

/-- Helper for Part K of `C47_the_ring_K_and_covariant_systems.md`: `x` is a unit iff
`red x ≠ 0`. -/
lemma isUnit_iff_red_ne_zero (x : ℤ_[2]) : IsUnit x ↔ red x ≠ 0 := by
  rw [ne_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not]

/-- Helper for Part K of `C47_the_ring_K_and_covariant_systems.md`: `red 2 = 0`. -/
lemma red_two : red 2 = 0 := by
  rw [map_ofNat]; rfl

/-- Helper for (K1) of `C47_the_ring_K_and_covariant_systems.md`: `P(2y) ≡ P(0) (mod 2)`. -/
lemma red_eval_two_mul (P : ℤ_[2][X]) (y : ℤ_[2]) : red (P.eval (2 * y)) = red (P.coeff 0) := by
  rw [← eval_map_apply, map_mul, red_two, zero_mul, ← coeff_zero_eq_eval_zero, coeff_map]

/-- **(K1)** of `C47_the_ring_K_and_covariant_systems.md`: `q(2y)` is a unit, so
`Ring.inverse (q(2y)) * q(2y) = 1`. -/
theorem K1 (r : KRep) (y : ℤ_[2]) :
    IsUnit (r.q.eval (2 * y)) ∧ Ring.inverse (r.q.eval (2 * y)) * r.q.eval (2 * y) = 1 := by
  have hu : IsUnit (r.q.eval (2 * y)) := by
    rw [isUnit_iff_red_ne_zero, red_eval_two_mul]
    exact (isUnit_iff_red_ne_zero _).1 r.hq
  exact ⟨hu, Ring.inverse_mul_cancel _ hu⟩

/-- Helper for (K1) of `C47_the_ring_K_and_covariant_systems.md`:
`q(2y) * Ring.inverse (q(2y)) = 1`. -/
lemma K1' (r : KRep) (y : ℤ_[2]) : r.q.eval (2 * y) * Ring.inverse (r.q.eval (2 * y)) = 1 :=
  Ring.mul_inverse_cancel _ (K1 r y).1

/-- **(K6)** of `C47_the_ring_K_and_covariant_systems.md` (values modulo 4):
`ϑ y − a ∈ 4 ℤ_[2]`; in particular `ϑ y` is a unit iff `a` is. -/
theorem K6 (r : KRep) (y : ℤ_[2]) :
    (∃ z, r.eval y - r.a = 4 * z) ∧ (IsUnit (r.eval y) ↔ IsUnit r.a) := by
  obtain ⟨p₁, hp₁⟩ := X_dvd_iff.2 r.hp
  have h4 : r.eval y - r.a = 4 * (y * p₁.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))) := by
    simp only [KRep.eval, hp₁, eval_mul, eval_X]; ring
  refine ⟨⟨_, h4⟩, ?_⟩
  have hr : red (r.eval y) = red r.a := by
    have : r.eval y = r.a + 4 * (y * p₁.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))) := by
      rw [← h4]; ring
    rw [this, map_add, map_mul, map_ofNat]
    have : (4 : ZMod 2) = 0 := rfl
    rw [this, zero_mul, add_zero]
  rw [isUnit_iff_red_ne_zero, isUnit_iff_red_ne_zero, hr]

/-- **(K2)** of `C47_the_ring_K_and_covariant_systems.md` (uniqueness): if `r.eval = r'.eval`
then `r.a = r'.a` and `r.p * r'.q = r'.p * r.q`. -/
theorem K2 (r r' : KRep) (h : r.eval = r'.eval) : r.a = r'.a ∧ r.p * r'.q = r'.p * r.q := by
  set Q : ℤ_[2][X] := C (r.a - r'.a) * r.q * r'.q + C 2 * (r.p * r'.q - r'.p * r.q) with hQdef
  have hroot : ∀ y : ℤ_[2], Q.eval (2 * y) = 0 := by
    intro y
    have := congrFun h y
    simp only [KRep.eval] at this
    have e1 := K1' r y
    have e2 := K1' r' y
    simp only [hQdef, eval_add, eval_mul, eval_C, eval_sub]
    linear_combination (r.q.eval (2 * y) * r'.q.eval (2 * y)) * this
      - (2 * r.p.eval (2 * y) * r'.q.eval (2 * y)) * e1
      + (2 * r'.p.eval (2 * y) * r.q.eval (2 * y)) * e2
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun y : ℤ_[2] => 2 * y) :=
      mul_right_injective₀ two_ne_zero
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨y, rfl⟩
    exact hroot y
  have h0 := congrArg (fun P => P.coeff 0) hQ
  simp only [hQdef, coeff_add, mul_coeff_zero, coeff_C_zero, coeff_sub, r.hp, r'.hp,
    coeff_zero] at h0
  have ha : r.a = r'.a := by
    have : (r.a - r'.a) * r.q.coeff 0 * r'.q.coeff 0 = 0 := by simpa using h0
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact sub_eq_zero.1 h2
      · exact absurd h2 r.hq.ne_zero
    · exact absurd h1 r'.hq.ne_zero
  refine ⟨ha, ?_⟩
  rw [hQdef, ha, sub_self, map_zero, zero_mul, zero_mul, zero_add] at hQ
  rcases mul_eq_zero.1 hQ with h1 | h1
  · exact absurd h1 (by simp)
  · exact sub_eq_zero.1 h1

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: the constant functions are in `Kr`
(representation `(a, 0, 1)`). -/
theorem K3_const (c : ℤ_[2]) : (fun _ : ℤ_[2] => c) ∈ Kr :=
  ⟨⟨c, 0, 1, by simp, by simp⟩, by funext y; simp [KRep.eval]⟩

/-- Helper for (K3) of `C47_the_ring_K_and_covariant_systems.md`: the representation of a sum,
`(a, p, q) + (b, p', q') = (a + b, p q' + p' q, q q')`. -/
lemma K3_add_rep (r r' : KRep) : ∃ s : KRep, s.eval = r.eval + r'.eval ∧ s.a = r.a + r'.a ∧
    s.p = r.p * r'.q + r'.p * r.q ∧ s.q = r.q * r'.q := by
  refine ⟨⟨r.a + r'.a, r.p * r'.q + r'.p * r.q, r.q * r'.q,
    by simp [mul_coeff_zero, r.hp, r'.hp], by rw [mul_coeff_zero]; exact r.hq.mul r'.hq⟩,
    ?_, rfl, rfl, rfl⟩
  funext y
  have e1 := K1' r y
  have e2 := K1' r' y
  simp only [KRep.eval, Pi.add_apply, eval_add, eval_mul, Ring.mul_inverse_rev]
  linear_combination (2 * r.p.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))) * e2
    + (2 * r'.p.eval (2 * y) * Ring.inverse (r'.q.eval (2 * y))) * e1

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: `Kr` is closed under `+`
(representation `(a + b, p q' + p' q, q q')`). -/
theorem K3_add {ϑ ϑ' : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (h' : ϑ' ∈ Kr) : ϑ + ϑ' ∈ Kr := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨r', rfl⟩ := h'
  obtain ⟨s, hs, -⟩ := K3_add_rep r r'
  exact ⟨s, hs⟩

/-- Helper for (K3) of `C47_the_ring_K_and_covariant_systems.md`: the representation of a
product, `(a, p, q)(b, p', q') = (ab, a p' q + b p q' + 2 p p', q q')`. -/
lemma K3_mul_rep (r r' : KRep) : ∃ s : KRep, s.eval = r.eval * r'.eval ∧ s.a = r.a * r'.a ∧
    s.p = C r.a * r'.p * r.q + C r'.a * r.p * r'.q + C 2 * r.p * r'.p ∧ s.q = r.q * r'.q := by
  refine ⟨⟨r.a * r'.a, C r.a * r'.p * r.q + C r'.a * r.p * r'.q + C 2 * r.p * r'.p, r.q * r'.q,
    by simp [mul_coeff_zero, r.hp, r'.hp], by rw [mul_coeff_zero]; exact r.hq.mul r'.hq⟩,
    ?_, rfl, rfl, rfl⟩
  funext y
  have e1 := K1' r y
  have e2 := K1' r' y
  simp only [KRep.eval, Pi.mul_apply, eval_add, eval_mul, eval_C, Ring.mul_inverse_rev]
  linear_combination (2 * r.a * r'.p.eval (2 * y) * Ring.inverse (r'.q.eval (2 * y))) * e1
    + (2 * r'.a * r.p.eval (2 * y) * Ring.inverse (r.q.eval (2 * y))) * e2

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: `Kr` is closed under `*`
(representation `(ab, a p' q + b p q' + 2 p p', q q')`). -/
theorem K3_mul {ϑ ϑ' : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (h' : ϑ' ∈ Kr) : ϑ * ϑ' ∈ Kr := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨r', rfl⟩ := h'
  obtain ⟨s, hs, -⟩ := K3_mul_rep r r'
  exact ⟨s, hs⟩

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: `Kr` is closed under multiplication
by a constant of `ℤ_[2]`. -/
theorem K3_smul (c : ℤ_[2]) {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) : (fun y => c * ϑ y) ∈ Kr :=
  K3_mul (K3_const c) h

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: `Kr` is closed under negation. -/
theorem K3_neg {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) : -ϑ ∈ Kr := by
  have := K3_smul (-1) h
  convert this using 1
  funext y; simp

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: `Kr` is closed under `−`. -/
theorem K3_sub {ϑ ϑ' : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (h' : ϑ' ∈ Kr) : ϑ - ϑ' ∈ Kr := by
  rw [sub_eq_add_neg]; exact K3_add h (K3_neg h')

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`: `y ↦ 2^α y` is in `Kr` for `α ≥ 2`
(representation `(0, 2^{α−2} X, 1)`). -/
theorem K3_pow_mul (α : ℕ) (hα : 2 ≤ α) : (fun y : ℤ_[2] => 2 ^ α * y) ∈ Kr := by
  obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
  refine ⟨⟨0, C (2 ^ k) * X, 1, by simp, by simp⟩, ?_⟩
  funext y
  simp only [KRep.eval, eval_mul, eval_C, eval_X, eval_one, Ring.inverse_one]
  ring

/-- **(K3)** of `C47_the_ring_K_and_covariant_systems.md`, all together: constants, `+`, `−`, `*`,
constant multiples, and `y ↦ 2^α y` (`α ≥ 2`). -/
theorem K3 :
    (∀ c : ℤ_[2], (fun _ : ℤ_[2] => c) ∈ Kr) ∧
    (∀ ϑ ∈ Kr, ∀ ϑ' ∈ Kr, ϑ + ϑ' ∈ Kr) ∧
    (∀ ϑ ∈ Kr, ∀ ϑ' ∈ Kr, ϑ - ϑ' ∈ Kr) ∧
    (∀ ϑ ∈ Kr, ∀ ϑ' ∈ Kr, ϑ * ϑ' ∈ Kr) ∧
    (∀ c : ℤ_[2], ∀ ϑ ∈ Kr, (fun y => c * ϑ y) ∈ Kr) ∧
    (∀ α : ℕ, 2 ≤ α → (fun y : ℤ_[2] => 2 ^ α * y) ∈ Kr) :=
  ⟨K3_const, fun _ h _ h' => K3_add h h', fun _ h _ h' => K3_sub h h',
    fun _ h _ h' => K3_mul h h', fun c _ h => K3_smul c h, K3_pow_mul⟩

/-- Helper for (K4) of `C47_the_ring_K_and_covariant_systems.md`: the representation of a shift. -/
lemma K4_rep (r : KRep) (e : ℤ_[2]) : ∃ s : KRep, s.eval = (fun y => r.eval (y - e)) ∧
    s.a = r.a + 2 * r.p.eval (-(2 * e)) * Ring.inverse (r.q.eval (-(2 * e))) ∧
    s.p = C (r.q.eval (-(2 * e))) * r.p.comp (X - C (2 * e))
      - C (r.p.eval (-(2 * e))) * r.q.comp (X - C (2 * e)) ∧
    s.q = C (r.q.eval (-(2 * e))) * r.q.comp (X - C (2 * e)) := by
  have e0 := K1' r (-e)
  have hu0 := (K1 r (-e)).1
  rw [mul_neg] at e0 hu0
  refine ⟨⟨r.a + 2 * r.p.eval (-(2 * e)) * Ring.inverse (r.q.eval (-(2 * e))),
    C (r.q.eval (-(2 * e))) * r.p.comp (X - C (2 * e))
      - C (r.p.eval (-(2 * e))) * r.q.comp (X - C (2 * e)),
    C (r.q.eval (-(2 * e))) * r.q.comp (X - C (2 * e)), ?_, ?_⟩, ?_, rfl, rfl, rfl⟩
  · simp [coeff_zero_eq_eval_zero, eval_comp, mul_comm]
  · rw [coeff_zero_eq_eval_zero]
    simpa [eval_comp] using hu0.mul hu0
  · funext y
    have e1 := K1' r (y - e)
    rw [mul_sub] at e1
    simp only [KRep.eval, eval_sub, eval_mul, eval_C, eval_comp, eval_X,
      Ring.mul_inverse_rev, mul_sub]
    linear_combination (2 * r.p.eval (2 * y - 2 * e) * Ring.inverse (r.q.eval (2 * y - 2 * e)))
        * e0
      - (2 * r.p.eval (-(2 * e)) * Ring.inverse (r.q.eval (-(2 * e)))) * e1

/-- **(K4)** of `C47_the_ring_K_and_covariant_systems.md` (shifts): `y ↦ ϑ (y − e)` is in `Kr`
(representation `a' = a + 2 p(−2e)/q(−2e)`, `p' = q(−2e) p(X − 2e) − p(−2e) q(X − 2e)`,
`q' = q(−2e) q(X − 2e)`). -/
theorem K4 {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (e : ℤ_[2]) : (fun y => ϑ (y - e)) ∈ Kr := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨s, hs, -⟩ := K4_rep r e
  exact ⟨s, hs⟩

/-- **(K5)** of `C47_the_ring_K_and_covariant_systems.md` (inverses): if `IsUnit r.a`, every
value `r.eval y` is a unit and `y ↦ Ring.inverse (r.eval y)` is in `Kr`
(representation `a' = a⁻¹`, `p' = −p`, `q' = a (a q + 2 p)`). -/
theorem K5 (r : KRep) (hu : IsUnit r.a) :
    (∀ y, IsUnit (r.eval y)) ∧ (fun y => Ring.inverse (r.eval y)) ∈ Kr := by
  have hw : ∀ y, IsUnit (r.eval y) := fun y => (K6 r y).2.2 hu
  refine ⟨hw, ⟨⟨Ring.inverse r.a, -r.p, C r.a * (C r.a * r.q + C 2 * r.p), by simp [r.hp], ?_⟩, ?_⟩⟩
  · simpa [r.hp] using hu.mul (hu.mul r.hq)
  · funext y
    have e1 := K1' r y
    have ea := Ring.mul_inverse_cancel _ hu
    have hv : IsUnit (r.a * r.q.eval (2 * y) + 2 * r.p.eval (2 * y)) := by
      have : r.a * r.q.eval (2 * y) + 2 * r.p.eval (2 * y) = r.q.eval (2 * y) * r.eval y := by
        simp only [KRep.eval]
        linear_combination (-(2 * r.p.eval (2 * y))) * e1
      rw [this]; exact (K1 r y).1.mul (hw y)
    have ev := Ring.mul_inverse_cancel _ hv
    set T := Ring.inverse r.a + 2 * (-r.p).eval (2 * y) *
      Ring.inverse ((C r.a * (C r.a * r.q + C 2 * r.p)).eval (2 * y)) with hT
    have hwT : r.eval y * T = 1 := by
      simp only [hT, KRep.eval, eval_neg, eval_mul, eval_add, eval_C, Ring.mul_inverse_rev]
      linear_combination (-(r.a) * (Ring.inverse r.a + 2 * -r.p.eval (2 * y) *
          (Ring.inverse (r.a * r.q.eval (2 * y) + 2 * r.p.eval (2 * y)) * Ring.inverse r.a))
          + r.a * Ring.inverse r.a) * e1
        + (-2 * r.p.eval (2 * y) * Ring.inverse r.a * Ring.inverse (r.q.eval (2 * y))) * ev + ea
    change T = Ring.inverse (r.eval y)
    symm
    calc Ring.inverse (r.eval y) = Ring.inverse (r.eval y) * (r.eval y * T) := by rw [hwT, mul_one]
      _ = T := by rw [← mul_assoc, Ring.inverse_mul_cancel _ (hw y), one_mul]

end RingK
