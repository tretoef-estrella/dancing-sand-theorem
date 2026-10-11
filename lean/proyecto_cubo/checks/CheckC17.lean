import RequestProject.CubeLaplacian.All

/-! Auditor's check file for Lean piece C17 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C17_the_laplacian_in_the_group_ring.md` and closed by `rfl`;
the main statements restated by hand with every object unfolded and closed by the certified
theorems; then `#print axioms`. -/

open Finset CubeLaplacian
open scoped TensorProduct

-- G, the generators, the ring, x_i, s_i, s_S, σ
example (n : ℕ) : G n = (Fin n → ZMod 2) := rfl
example (n : ℕ) (i : Fin n) : e n i = Pi.single i 1 := rfl
example (n : ℕ) : R n = AddMonoidAlgebra ℤ (Fin n → ZMod 2) := rfl
example (n : ℕ) (i : Fin n) : x n i = AddMonoidAlgebra.single (Pi.single i 1 : Fin n → ZMod 2) 1 := rfl
example (n : ℕ) (i : Fin n) : s n i = 1 - x n i := rfl
example (n : ℕ) (S : Finset (Fin n)) : sS n S = ∏ i ∈ S, (1 - x n i) := rfl
example (n : ℕ) : sigma n = ∑ i, (1 - x n i) := rfl
-- the Laplacian, its cokernel, K(Q_n), Syl_2
example (n : ℕ) (f : G n → ℤ) (g : G n) :
    L n f g = (n : ℤ) * f g - ∑ i, f (g + Pi.single i 1) := rfl
example (n : ℕ) : K n = Submodule.torsion ℤ ((G n → ℤ) ⧸ LinearMap.range (lap ℤ n)) := rfl
example (T : Type) [AddCommGroup T] (y : T) : y ∈ Syl2 T ↔ ∃ k : ℕ, (2 ^ k : ℕ) • y = 0 := Iff.rfl
example (n : ℕ) : Rplus n = Submodule.span ℤ (sS n '' {S | S ≠ ∅}) := rfl

-- (A1), (A2), (A3)
example (n : ℕ) (j : Fin n) : (1 - x n j) * (1 - x n j) = 2 * (1 - x n j) := A1 n j
example (n : ℕ) (j : Fin n) (S : Finset (Fin n)) (hj : j ∉ S) :
    (1 - x n j) * ∏ i ∈ S, (1 - x n i) = ∏ i ∈ S ∪ {j}, (1 - x n i) := (A2 n j S).1 hj
example (n : ℕ) (j : Fin n) (S : Finset (Fin n)) (hj : j ∈ S) :
    (1 - x n j) * ∏ i ∈ S, (1 - x n i) = 2 * ∏ i ∈ S, (1 - x n i) := (A2 n j S).2 hj
example (n : ℕ) (S : Finset (Fin n)) :
    (∑ i, (1 - x n i)) * ∏ i ∈ S, (1 - x n i) =
      ∑ j ∈ Sᶜ, ∏ i ∈ S ∪ {j}, (1 - x n i) + (2 * (S.card : ℤ)) • ∏ i ∈ S, (1 - x n i) := A3 n S
-- (A4)
example (n : ℕ) : ∃ b : Module.Basis (Finset (Fin n)) ℤ (AddMonoidAlgebra ℤ (Fin n → ZMod 2)),
    ∀ S, b S = ∏ i ∈ S, (1 - x n i) := A4 n
-- (B1)
example (n : ℕ) (f : R n) (g : G n) :
    ((∑ i, (1 - x n i)) * f) g = n * f g - ∑ i, f (g + Pi.single i 1) := B1 n f g
-- (C1)
example (n : ℕ) (f : R n) : (sBasis n).repr ((∑ i, (1 - x n i)) * f) ∅ = 0 := C1 n f
-- (C2) injectivity and the diagonal
example (n : ℕ) : Function.Injective (sigmaPlus n) := C2_injective n
example (n : ℕ) (S : Finset (Fin n)) : (sBasis n).repr (sigma n * sS n S) S = 2 * (S.card : ℤ) :=
  (C2_diagonal n S).1
-- (C4), with the cokernel and K written out
example (n : ℕ) :
    Finite (Submodule.torsion ℤ ((G n → ℤ) ⧸ LinearMap.range (lap ℤ n))) ∧
    Nonempty (((G n → ℤ) ⧸ LinearMap.range (lap ℤ n)) ≃ₗ[ℤ]
      ℤ × Submodule.torsion ℤ ((G n → ℤ) ⧸ LinearMap.range (lap ℤ n))) :=
  ⟨(C4 n).2.1, (C4 n).2.2⟩
-- (D1)
example (T : Type) [AddCommGroup T] [Finite T] : Nonempty (T ⊗[ℤ] ℤ_[2] ≃+ Syl2 T) := D1 T
-- (D2), the last claim of §2.1, with σ_A written out
example (n : ℕ) :
    Nonempty ((G n → ℤ_[2]) ⧸ LinearMap.range (lap ℤ_[2] n) ≃+
      ℤ_[2] × Syl2 (Submodule.torsion ℤ ((G n → ℤ) ⧸ LinearMap.range (lap ℤ n)))) := D2 n
example (n : ℕ) (f : G n → ℤ_[2]) (g : G n) :
    lap ℤ_[2] n f g = (n : ℤ_[2]) * f g - ∑ i, f (g + Pi.single i 1) := rfl

#print axioms A1
#print axioms A2
#print axioms A3
#print axioms A4
#print axioms B1
#print axioms B2
#print axioms C1
#print axioms C2_triangular
#print axioms C2_diagonal
#print axioms C2_injective
#print axioms C2_finiteIndex
#print axioms C3
#print axioms C4
#print axioms D1
#print axioms D2
