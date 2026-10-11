import RequestProject.DPLattice.All

/-! Auditor's check file for Lean piece C18 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C18_divided_power_lattices_and_the_dictionary.md` and closed
by `rfl` or by the axioms of the structure; the main statements restated by hand with every
object unfolded and closed by the certified theorems; then `#print axioms`. -/

open Finset DPLattice CubeLaplacian

-- The axioms of a DP-lattice, read off the structure in the words of the file
example {A : Type} [CommRing A] (M : DPLattice A) (i : M.ι) (r : ℕ) (j : M.ι)
    (h : M.wt j ≠ M.wt i - 2 * r) : M.Fd r (Pi.single i 1) j = 0 := M.isDP.W_F i r j h
example {A : Type} [CommRing A] (M : DPLattice A) (i : M.ι) (r : ℕ) (j : M.ι)
    (h : M.wt j ≠ M.wt i + 2 * r) : M.Ed r (Pi.single i 1) j = 0 := M.isDP.W_E i r j h
example {A : Type} [CommRing A] (M : DPLattice A) : M.Fd 0 = 1 ∧ M.Ed 0 = 1 :=
  ⟨M.isDP.P0_F, M.isDP.P0_E⟩
example {A : Type} [CommRing A] (M : DPLattice A) (a b : ℕ) :
    M.Fd a ∘ₗ M.Fd b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • M.Fd (a + b) := M.isDP.P1_F a b
example {A : Type} [CommRing A] (M : DPLattice A) (a b : ℕ) :
    M.Ed a ∘ₗ M.Ed b = ((Ring.choose ((a : ℤ) + b) a : ℤ) : A) • M.Ed (a + b) := M.isDP.P1_E a b
example {A : Type} [CommRing A] (M : DPLattice A) (i : M.ι) (r s : ℕ) :
    M.Ed s (M.Fd r (Pi.single i 1)) =
      ∑ j ∈ range (min r s + 1),
        ((Ring.choose (M.wt i + s - r) j : ℤ) : A) • M.Fd (r - j) (M.Ed (s - j) (Pi.single i 1)) :=
  M.isDP.K i r s
-- H
example {A : Type} [CommRing A] (M : DPLattice A) (f : M.ι → A) (i : M.ι) :
    H M f i = (M.wt i : A) * f i := rfl

-- 𝟙, V
example {A : Type} [CommRing A] : (one A).ι = Unit := rfl
example {A : Type} [CommRing A] (r : ℕ) : (one A).Fd r = if r = 0 then 1 else 0 := rfl
example {A : Type} [CommRing A] (r : ℕ) : (one A).Ed r = if r = 0 then 1 else 0 := rfl
example {A : Type} [CommRing A] : (V A).ι = Fin 2 := rfl
example {A : Type} [CommRing A] : (V A).wt (0 : Fin 2) = 1 ∧ (V A).wt (1 : Fin 2) = -1 := V_wt
example {A : Type} [CommRing A] :
    (V A).Fd 1 (Pi.single (0 : Fin 2) 1) = Pi.single (1 : Fin 2) 1 ∧
    (V A).Fd 1 (Pi.single (1 : Fin 2) 1) = 0 ∧
    (V A).Ed 1 (Pi.single (1 : Fin 2) 1) = Pi.single (0 : Fin 2) 1 ∧
    (V A).Ed 1 (Pi.single (0 : Fin 2) 1) = 0 :=
  ⟨V_Fd_one_b0, V_Fd_one_b1, V_Ed_one_b1, V_Ed_one_b0⟩
example {A : Type} [CommRing A] (r : ℕ) (hr : 2 ≤ r) : (V A).Fd r = 0 ∧ (V A).Ed r = 0 :=
  ⟨V_Fd_ge_two r hr, V_Ed_ge_two r hr⟩

-- V ⊗ M, with b_e m written out
example {A : Type} [CommRing A] {ι : Type} (e : Fin 2) (m : ι → A) :
    bvec e m = fun p => if p.1 = e then m p.2 else 0 := rfl
example {A : Type} [CommRing A] (M : DPLattice A) : (tensorV M).ι = (Fin 2 × M.ι) := rfl
example {A : Type} [CommRing A] (M : DPLattice A) (e : Fin 2) (i : M.ι) :
    (tensorV M).wt (e, i) = (if e = 0 then 1 else -1) + M.wt i := rfl
example {A : Type} [CommRing A] (M : DPLattice A) (r : ℕ) (hr : 1 ≤ r) (m : M.ι → A) :
    (tensorV M).Fd r (fun p => if p.1 = 0 then m p.2 else 0) =
      (fun p => if p.1 = 0 then M.Fd r m p.2 else 0) +
      (fun p => if p.1 = 1 then M.Fd (r - 1) m p.2 else 0) := tensorV_Fd_b0 M r hr m
example {A : Type} [CommRing A] (M : DPLattice A) (r : ℕ) (m : M.ι → A) :
    (tensorV M).Fd r (fun p => if p.1 = 1 then m p.2 else 0) =
      (fun p => if p.1 = 1 then M.Fd r m p.2 else 0) := tensorV_Fd_b1 M r m
example {A : Type} [CommRing A] (M : DPLattice A) (r : ℕ) (hr : 1 ≤ r) (m : M.ι → A) :
    (tensorV M).Ed r (fun p => if p.1 = 1 then m p.2 else 0) =
      (fun p => if p.1 = 1 then M.Ed r m p.2 else 0) +
      (fun p => if p.1 = 0 then M.Ed (r - 1) m p.2 else 0) := tensorV_Ed_b1 M r hr m
example {A : Type} [CommRing A] (M : DPLattice A) (r : ℕ) (m : M.ι → A) :
    (tensorV M).Ed r (fun p => if p.1 = 0 then m p.2 else 0) =
      (fun p => if p.1 = 0 then M.Ed r m p.2 else 0) := tensorV_Ed_b0 M r m
-- V^{⊗n}
example {A : Type} [CommRing A] : tensorPow A 0 = one A := rfl
example {A : Type} [CommRing A] (n : ℕ) : tensorPow A (n + 1) = tensorV (tensorPow A n) := rfl

-- Weyl lattices
example {A : Type} [CommRing A] (l : ℕ) : (delta A l).ι = Fin (l + 1) ∧ (nabla A l).ι = Fin (l + 1) :=
  ⟨rfl, rfl⟩
example {A : Type} [CommRing A] (l : ℕ) (r : Fin (l + 1)) :
    (delta A l).wt r = l - 2 * (r : ℤ) ∧ (nabla A l).wt r = l - 2 * (r : ℤ) := weyl_wt l r
example {A : Type} [CommRing A] (l t : ℕ) (r : Fin (l + 1)) :
    (delta A l).Fd t (Pi.single r 1) = if h : (r : ℕ) + t ≤ l then
      (((r : ℕ) + t).choose t : A) • (Pi.single (⟨r + t, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 :=
  delta_Fd_single l t r
example {A : Type} [CommRing A] (l s : ℕ) (r : Fin (l + 1)) :
    (delta A l).Ed s (Pi.single r 1) = if h : s ≤ (r : ℕ) then
      ((l - r + s).choose s : A) • (Pi.single (⟨r - s, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 :=
  delta_Ed_single l s r
example {A : Type} [CommRing A] (l t : ℕ) (r : Fin (l + 1)) :
    (nabla A l).Fd t (Pi.single r 1) = if h : (r : ℕ) + t ≤ l then
      ((l - r).choose t : A) • (Pi.single (⟨r + t, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 :=
  nabla_Fd_single l t r
example {A : Type} [CommRing A] (l s : ℕ) (r : Fin (l + 1)) :
    (nabla A l).Ed s (Pi.single r 1) = if h : s ≤ (r : ℕ) then
      ((r : ℕ).choose s : A) • (Pi.single (⟨r - s, by omega⟩ : Fin (l + 1)) (1 : A) : Fin (l + 1) → A) else 0 :=
  nabla_Ed_single l s r
-- (T5)
example {A : Type} [CommRing A] : delta A 1 = V A ∧ nabla A 1 = V A := ⟨T5_delta_one, T5_nabla_one⟩

-- (L1), with the pure tensor index written out
example {A : Type} [CommRing A] (n : ℕ) (S : Finset (Fin (n + 1))) :
    pt A (n + 1) S = ((if (0 : Fin (n + 1)) ∈ S then 1 else 0 : Fin 2),
      pt A n (univ.filter fun i : Fin n => i.succ ∈ S)) := rfl
example {A : Type} [CommRing A] (n : ℕ) : Function.Bijective (pt A n) := pt_bijective n
example {A : Type} [CommRing A] (n : ℕ) (S : Finset (Fin n)) :
    (tensorPow A n).Fd 1 (Pi.single (pt A n S) 1) = ∑ j ∈ Sᶜ, Pi.single (pt A n (insert j S)) 1 :=
  L1_F n S
example {A : Type} [CommRing A] (n : ℕ) (S : Finset (Fin n)) :
    H (tensorPow A n) (Pi.single (pt A n S) 1) =
      (((n : ℤ) - 2 * S.card : ℤ) : A) •
        (Pi.single (pt A n S) (1 : A) : (tensorPow A n).ι → A) := L1_H n S

-- (L2), Lemma 2.2, with the Laplacian of C17 and F^{(1)} + n − H written out
example {A : Type} [CommRing A] (n : ℕ) (f : G n → A) (g : G n) :
    lap A n f g = (n : A) * f g - ∑ i, f (g + Pi.single i 1) := rfl
example {A : Type} [CommRing A] (n : ℕ) :
    ∃ Ψ : (G n → A) ≃ₗ[A] ((tensorPow A n).ι → A),
      Ψ.toLinearMap ∘ₗ lap A n =
        ((tensorPow A n).Fd 1 + (n : A) • LinearMap.id - H (tensorPow A n)) ∘ₗ Ψ.toLinearMap :=
  L2 n

-- (C1), (C2), Corollary 2.3
example {A : Type} [CommRing A] (n : ℕ) {J : Type} [Fintype J] [DecidableEq J]
    (M : J → DPLattice A) (Θ : ((tensorPow A n).ι → A) ≃ₗ[A] ((j : J) → (M j).ι → A))
    (hF : ∀ x, Θ ((tensorPow A n).Fd 1 x) = fun j => (M j).Fd 1 (Θ x j))
    (hH : ∀ x, Θ (H (tensorPow A n) x) = fun j => H (M j) (Θ x j)) :
    Nonempty (((G n → A) ⧸ LinearMap.range (lap A n)) ≃ₗ[A]
      ((j : J) → ((M j).ι → A) ⧸ LinearMap.range ((M j).Fd 1 + (n : A) • LinearMap.id - H (M j)))) :=
  DPLattice.C1 n M Θ hF hH
example (n : ℕ) {J : Type} [Fintype J] [DecidableEq J] (M : J → DPLattice ℤ_[2])
    (Θ : ((tensorPow ℤ_[2] n).ι → ℤ_[2]) ≃ₗ[ℤ_[2]] ((j : J) → (M j).ι → ℤ_[2]))
    (hF : ∀ x, Θ ((tensorPow ℤ_[2] n).Fd 1 x) = fun j => (M j).Fd 1 (Θ x j))
    (hH : ∀ x, Θ (H (tensorPow ℤ_[2] n) x) = fun j => H (M j) (Θ x j)) :
    Nonempty (ℤ_[2] × Syl2 (Submodule.torsion ℤ ((G n → ℤ) ⧸ LinearMap.range (lap ℤ n))) ≃+
      ((j : J) → ((M j).ι → ℤ_[2]) ⧸
        LinearMap.range ((M j).Fd 1 + (n : ℤ_[2]) • LinearMap.id - H (M j)))) :=
  C2 n M Θ hF hH

#print axioms T1
#print axioms T2
#print axioms T3
#print axioms T4
#print axioms T5_delta_zero
#print axioms T5_nabla_zero
#print axioms T5_delta_one
#print axioms T5_nabla_one
#print axioms delta_Fd_single
#print axioms nabla_Ed_single
#print axioms tensorV_Fd_b0
#print axioms tensorV_Ed_b1
#print axioms pt_bijective
#print axioms L1_F
#print axioms L1_H
#print axioms L2
#print axioms DPLattice.C1
#print axioms C2
