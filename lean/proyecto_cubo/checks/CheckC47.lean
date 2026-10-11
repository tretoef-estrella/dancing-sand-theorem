import RequestProject.RingK.All

/-! Auditor's check file for Lean piece C47: the ring 𝒦 in rational form, Θ, R_𝒮 and the
covariant systems (Grepy Escribano, 9 Oct 2026). Restated by hand from
`C47_the_ring_K_and_covariant_systems.md`; then `#print axioms`. -/

open FormalOps Finset RingK Polynomial

-- the definitions, by `rfl`
example (r : KRep) (y : ℤ_[2]) :
    r.eval y = r.a + 2 * r.p.eval (2 * y) * Ring.inverse (r.q.eval (2 * y)) := rfl
example (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (D D' : Dn P) (m : ℕ) (f : ℤ) :
    (covSys P h c Γ D D').coef m f =
      if D'.1 ⊆ D.1 then Γ (D.1 \ D'.1) m ((2 : ℤ_[2]) ^ h * f + oS D.1 + c) else 0 := rfl
example (β γ : RS) (Δ : Finset ℕ) (q : ℕ) :
    (β * γ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
      (Nat.choose q a : S) * β Δ₁ a * γ (Δ \ Δ₁) (q - a) := rfl
example (D : Finset ℕ) : oS D = ∑ t ∈ D, 2 ^ t := rfl

-- (K2) uniqueness of the representation
example (r r' : KRep) (h : r.eval = r'.eval) : r.a = r'.a ∧ r.p * r'.q = r'.p * r.q := K2 r r' h

-- (K4) shifts
example {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (e : ℤ_[2]) : (fun y => ϑ (y - e)) ∈ Kr := K4 h e

-- (K5) inverses
example (r : KRep) (hu : IsUnit r.a) :
    (∀ y, IsUnit (r.eval y)) ∧ (fun y => Ring.inverse (r.eval y)) ∈ Kr := K5 r hu

-- (K6)
example (r : KRep) (y : ℤ_[2]) :
    (∃ z, r.eval y - r.a = 4 * z) ∧ (IsUnit (r.eval y) ↔ IsUnit r.a) := K6 r y

-- (K3) the payment 2^α y
example (α : ℕ) (hα : 2 ≤ α) : (fun y : ℤ_[2] => 2 ^ α * y) ∈ Kr := K3_pow_mul α hα

-- (S0) Θ is well defined on the class
example (r : KRep) : theta r.eval = thetaRep r := S0_theta r

-- (S1) Θ is a ring map on 𝒦_r
example {ϑ ϑ' : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (h' : ϑ' ∈ Kr) :
    theta (ϑ * ϑ') = theta ϑ * theta ϑ' ∧ theta (ϑ + ϑ') = theta ϑ + theta ϑ' :=
  ⟨S1_mul h h', S1_add h h'⟩

-- (S2) Θ does not see shifts
example {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) (e : ℤ_[2]) :
    theta (fun y => ϑ (y - e)) = theta ϑ := S2 h e

-- (S3) the kernel of Θ is 2·𝒦_r
example {ϑ : ℤ_[2] → ℤ_[2]} (h : ϑ ∈ Kr) :
    theta ϑ = 0 ↔ ∃ ψ ∈ Kr, ϑ = fun y => 2 * ψ y := S3 h

-- (R1), (R2)
example : (∀ β γ : RS, β * γ = γ * β) ∧ (2 : RS) = 0 := ⟨R1.1, R1.2.2⟩
example (β : RS) (Δ : Finset ℕ) (q : ℕ) :
    (β * β) Δ q = if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0 := R2 β Δ q

-- (T1) the product formula
example (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    covSys P h c Γ * covSys P h c Γ' = covSys P h c (prodFun h Γ Γ') := T1_mul P h c Γ Γ'

-- (T3)
example (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : ∀ Δ m, Γ Δ m ∈ Kr)
    (hΓ' : ∀ Δ m, Γ' Δ m ∈ Kr) :
    thetaSys (prodFun h Γ Γ') = thetaSys Γ * thetaSys Γ' := (T3 h Γ Γ' hΓ hΓ').1

#print axioms RingK.K1
#print axioms RingK.K2
#print axioms RingK.K3
#print axioms RingK.K4
#print axioms RingK.K5
#print axioms RingK.K6
#print axioms RingK.S0
#print axioms RingK.S0_theta
#print axioms RingK.S1
#print axioms RingK.S2
#print axioms RingK.S3
#print axioms RingK.S4
#print axioms RingK.S5
#print axioms RingK.R1
#print axioms RingK.R2
#print axioms RingK.T0
#print axioms RingK.T1
#print axioms RingK.T2
#print axioms RingK.T3
