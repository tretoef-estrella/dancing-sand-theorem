import RequestProject.FormalOps.All

/-! Auditor's check file for Lean piece C40, the formal operators (Grepy Escribano, 9 Oct 2026).
Restated by hand from `C40_the_formal_operators.md`: the definitions by `rfl`; Parts B, T, V, S
with the file's statements; then `#print axioms`. -/

open DPLattice Doubling FormalOps Finset
open scoped Pointwise

section defs
variable {A : Type} [CommRing A]

example (x y : Bf A) (m : ℕ) (f : ℤ) :
    (x * y).coef m f = ∑ a ∈ range (m + 1), (Nat.choose m a : A) * x.coef a f * y.coef (m - a) (f - a) :=
  rfl
example (m : ℕ) (f : ℤ) : (1 : Bf A).coef m f = if m = 0 then 1 else 0 := rfl
example (m m' : ℕ) (f : ℤ) : (Bf.fd m : Bf A).coef m' f = if m' = m then 1 else 0 := rfl
example (p : ℤ → A) (m : ℕ) (f : ℤ) : (Bf.dg p).coef m f = if m = 0 then p f else 0 := rfl
example (N : DPLattice A) (W : ℤ) (p : ℤ → A) (v : N.ι → A) (i : N.ι) :
    flD N W p v i = p ((W - N.wt i) / 2) * v i := rfl
example (N : DPLattice A) (W : ℤ) (B : ℕ) (x : Bf A) :
    act N W B x = ∑ m ∈ range B, flD N W (x.coef m) * N.Fd m := rfl
example (x : Bf A) (q : ℕ) (f : ℤ) : (tw00 x).coef q f = dfi q * x.coef (2 * q) (2 * f) := rfl
example (x : Bf A) (q : ℕ) (f : ℤ) : (tw11 x).coef q f = dfi q * x.coef (2 * q) (2 * f + 1) := rfl
example (x : Bf A) (q : ℕ) (f : ℤ) :
    (tw10 x).coef q f = dfi (q + 1) * x.coef (2 * q + 1) (2 * f + 1) := rfl
example (x : Bf A) (f : ℤ) : (tw01 x).coef 0 f = 0 := rfl
example (x : Bf A) (q : ℕ) (f : ℤ) :
    (tw01 x).coef (q + 1) f = ((2 * q + 2 : ℕ) : A) * dfi (q + 1) * x.coef (2 * q + 1) (2 * f) := rfl
example (x : Bf A) (m : ℕ) (g : ℤ) : (vplus x).coef m g = x.coef m (g + 1) := rfl
example (x : Bf A) (m : ℕ) (g : ℤ) : (vprime x).coef m g = x.coef (m + 1) (g + 1) := rfl
end defs

section S
variable {A : Type} [CommRing A] {L₁ L₂ K₁ K₂ : Type} [AddCommGroup L₁] [Module A L₁]
  [AddCommGroup L₂] [Module A L₂] [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₂] [Module A K₂]
  (P : L₁ ≃ₗ[A] K₁) (C : L₂ →ₗ[A] K₁) (Bb : L₁ →ₗ[A] K₂) (Dd : L₂ →ₗ[A] K₂)

example (u : L₁) (v : L₂) : blockOp P C Bb Dd (u, v) = (P u + C v, Bb u + Dd v) := by simp
example : schur P C Bb Dd = Dd - Bb ∘ₗ (P.symm : K₁ →ₗ[A] L₁) ∘ₗ C := rfl

-- (S1)
example (c : A) : Nonempty (((K₁ × K₂) ⧸ LinearMap.range (c • blockOp P C Bb Dd)) ≃ₗ[A]
    (K₁ ⧸ (c • ⊤ : Submodule A K₁)) × (K₂ ⧸ LinearMap.range (c • schur P C Bb Dd))) :=
  S1 P C Bb Dd c
-- (S2)
example : Nonempty (((K₁ × K₂) ⧸ LinearMap.range (blockOp P C Bb Dd)) ≃ₗ[A]
    (K₂ ⧸ LinearMap.range (schur P C Bb Dd))) := S2 P C Bb Dd
-- (S3)
example (G' : L₂ →ₗ[A] K₂) (hG : schur P C Bb Dd = (2 : A) • G') (h : ℕ) :
    Nonempty (((K₁ × K₂) ⧸ LinearMap.range ((2 : A) ^ h • blockOp P C Bb Dd)) ≃ₗ[A]
      (K₁ ⧸ ((2 : A) ^ h • ⊤ : Submodule A K₁)) ×
        (K₂ ⧸ LinearMap.range ((2 : A) ^ (h + 1) • G'))) := S3 P C Bb Dd G' hG h
end S

section B
variable {A : Type} [CommRing A] (N : DPLattice A) (W : ℤ)

-- (B1) the ring and the algebra exist with the product above
example : Ring (Bf A) := inferInstance
example : Algebra A (Bf A) := inferInstance
example (a : A) (x y : Bf A) : (a • x) * y = a • (x * y) := Bf.smul_mul a x y
example (a : A) (x y : Bf A) : x * (a • y) = a • (x * y) := Bf.mul_smul a x y
example (x y z : Bf A) : x * y * z = x * (y * z) := mul_assoc x y z
-- (B2)
example : flD N W 1 = 1 ∧ (∀ p q : ℤ → A, flD N W (p + q) = flD N W p + flD N W q) ∧
    (∀ p q : ℤ → A, flD N W (p * q) = flD N W p * flD N W q) := B2 N W
-- (B3), with no (top W) (more general)
example (a : ℕ) (p : ℤ → A) : N.Fd a * flD N W p = flD N W (fun f => p (f - a)) * N.Fd a :=
  B3 N W a p
-- (B4) under (nil BN)
example (BN : ℕ) (hnil : ∀ s ≥ BN, N.Fd s = 0) (B B' : ℕ) (hB : BN ≤ B) (hB' : BN ≤ B') :
    (∀ x : Bf A, act N W B x = act N W B' x) ∧
    (1 ≤ B → act N W B (1 : Bf A) = 1) ∧
    (∀ x y : Bf A, act N W B (x + y) = act N W B x + act N W B y) ∧
    (∀ (a : A) (x : Bf A), act N W B (a • x) = a • act N W B x) ∧
    (∀ x y : Bf A, act N W B (x * y) = act N W B x * act N W B y) ∧
    (∀ m : ℕ, act N W B (Bf.fd m : Bf A) = N.Fd m) ∧
    (1 ≤ B → ∀ p : ℤ → A, act N W B (Bf.dg p) = flD N W p) := B4 hnil hB hB'
end B

section T
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]
  (N : DPLattice A) (W : ℤ) (BN : ℕ)
-- (T0)
example (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) :
    ∀ i, (phi N).wt i ≤ 2 * W + 1 ∧ Even (2 * W + 1 - (phi N).wt i) := T0 htop
-- (T1)
example (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (x : Bf A) (n : N.ι → A) (B B' : ℕ) (hB : 2 * BN ≤ B) (hB' : BN ≤ B') :
    act (phi N) (2 * W + 1) B x (bvec 0 n) =
      bvec 0 (act N W B' (tw00 x) n) + bvec 1 (act N W B' (tw10 x) n) ∧
    act (phi N) (2 * W + 1) B x (bvec 1 n) =
      bvec 0 (act N W B' (tw01 x) n) + bvec 1 (act N W B' (tw11 x) n) :=
  T1 htop hnil x n hB hB'
end T

section V
variable {A : Type} [CommRing A] (M : DPLattice A) (W : ℤ) (BN : ℕ)
-- (V0)
example (htop : ∀ i, M.wt i ≤ W ∧ Even (W - M.wt i)) (hnil : ∀ s ≥ BN, M.Fd s = 0) :
    (∀ i, (tensorV M).wt i ≤ W + 1 ∧ Even (W + 1 - (tensorV M).wt i)) ∧
    (∀ s ≥ BN + 1, (tensorV M).Fd s = 0) := V0 htop hnil
-- (V1), with no (top W) (more general)
example (hnil : ∀ s ≥ BN, M.Fd s = 0) (x : Bf A) (y : M.ι → A) (B B' : ℕ)
    (hB : BN + 1 ≤ B) (hB' : BN ≤ B') :
    act (tensorV M) (W + 1) B x (bvec 0 y) =
      bvec 0 (act M W B' x y) + bvec 1 (act M W B' (vprime x) y) ∧
    act (tensorV M) (W + 1) B x (bvec 1 y) = bvec 1 (act M W B' (vplus x) y) :=
  V1 hnil x y hB hB'
end V

#print axioms FormalOps.Bf.instRing
#print axioms FormalOps.Bf.instAlgebra
#print axioms FormalOps.B2
#print axioms FormalOps.B3
#print axioms FormalOps.B4
#print axioms FormalOps.T0
#print axioms FormalOps.T1
#print axioms FormalOps.V0
#print axioms FormalOps.V1
#print axioms FormalOps.S1
#print axioms FormalOps.S2
#print axioms FormalOps.S3
