module

public import RequestProject.FormalDance.PartC

/-!
# `C40c_the_action_of_a_system_and_one_move.md`: Definitions (new) — `sysAct`, `pack`, `vpack`

Encodings (namespace `FormalAct`), reusing C18's `DPLattice`, `bvec`, `slice` and C40's `act`:

* A system is a matrix `G : Matrix n n (Bf A)` (Mathlib's matrices over C40's `Bf A`), with
  `[Fintype n] [DecidableEq n]`. A vector of `N^{⊕n}` is a function `n → N.ι → A` (slot `s`, then
  the basis index of `N`).
* `sysAct N W B G : (n → N.ι → A) →ₗ[A] (n → N.ι → A)` is exactly the map of the file,
  `(sysAct N W B G v) s = Σ_{s'} act N W B (G s s') (v s')` (`sysAct_apply`).
* `pack : (n → ι → A) × (n → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A)` is
  `pack (u, v) = fun s => bvec 0 (u s) + bvec 1 (v s)`, with inverse
  `w ↦ (fun s => slice 0 (w s), fun s => slice 1 (w s))`.
* `vpack : (n × Fin 2 → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A)` is
  `vpack w = fun s => bvec 0 (w (s, 0)) + bvec 1 (w (s, 1))`, with inverse
  `w ↦ fun q => slice q.2 (w q.1)`.
* A cokernel `coker f` is the quotient `M ⧸ LinearMap.range f`; the submodule `c M` is
  `(c • ⊤ : Submodule A M)` (pointwise scalar multiple of `⊤`), as in C40.
* (top W) is the hypothesis `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)` and (nil BN) is
  `∀ s ≥ BN, N.Fd s = 0`, written out in each statement.
-/

@[expose] public section

noncomputable section

namespace FormalAct

open DPLattice FormalOps Finset

variable {A : Type*} [CommRing A]

section sysAct

variable {n : Type*} [Fintype n]

/-- Definitions (new) 1 of `C40c_the_action_of_a_system_and_one_move.md`: the action of a system,
`(sysAct N W B G v) s = Σ_{s'} act N W B (G s s') (v s')` (`G[s, s']` maps the source slot `s'`
to the coordinate slot `s`). -/
def sysAct (N : DPLattice A) (W : ℤ) (B : ℕ) (G : Matrix n n (Bf A)) :
    (n → N.ι → A) →ₗ[A] (n → N.ι → A) where
  toFun v s := ∑ s', act N W B (G s s') (v s')
  map_add' v w := by funext s; simp [Finset.sum_add_distrib]
  map_smul' c v := by funext s; simp [Finset.smul_sum]

/-- Definitions (new) 1 of `C40c_the_action_of_a_system_and_one_move.md`: the defining formula of
`sysAct`. -/
@[simp] lemma sysAct_apply (N : DPLattice A) (W : ℤ) (B : ℕ) (G : Matrix n n (Bf A))
    (v : n → N.ι → A) (s : n) :
    sysAct N W B G v s = ∑ s', act N W B (G s s') (v s') := rfl

end sysAct

section pack

variable {n ι : Type*}

/-- Definitions (new) 2 of `C40c_the_action_of_a_system_and_one_move.md`: packing the two halves,
`pack (u, v) = fun s => bvec 0 (u s) + bvec 1 (v s)` (inverse: `slice 0`, `slice 1`). -/
def pack : ((n → ι → A) × (n → ι → A)) ≃ₗ[A] (n → Fin 2 × ι → A) where
  toFun p s := bvec 0 (p.1 s) + bvec 1 (p.2 s)
  invFun w := (fun s => slice 0 (w s), fun s => slice 1 (w s))
  map_add' p q := by funext s; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; abel
  map_smul' c p := by funext s; simp
  left_inv p := by ext s i <;> simp
  right_inv w := by funext s; exact (eq_bvec_slice (w s)).symm

/-- Definitions (new) 2 of `C40c_the_action_of_a_system_and_one_move.md`: the defining formula of
`pack`. -/
@[simp] lemma pack_apply (u v : n → ι → A) (s : n) :
    pack (A := A) (u, v) s = bvec 0 (u s) + bvec 1 (v s) := rfl

/-- Definitions (new) 2 of `C40c_the_action_of_a_system_and_one_move.md`: packing the slots of
the V-split, `vpack w = fun s => bvec 0 (w (s, 0)) + bvec 1 (w (s, 1))` (inverse: read the slot
`e` of `w s` with `slice e`). -/
def vpack : (n × Fin 2 → ι → A) ≃ₗ[A] (n → Fin 2 × ι → A) where
  toFun w s := bvec 0 (w (s, 0)) + bvec 1 (w (s, 1))
  invFun w q := slice q.2 (w q.1)
  map_add' p q := by funext s; simp only [Pi.add_apply, map_add]; abel
  map_smul' c p := by funext s; simp
  left_inv w := by
    funext ⟨s, e⟩ i
    fin_cases e <;> simp
  right_inv w := by funext s; exact (eq_bvec_slice (w s)).symm

/-- Definitions (new) 2 of `C40c_the_action_of_a_system_and_one_move.md`: the defining formula of
`vpack`. -/
@[simp] lemma vpack_apply (w : n × Fin 2 → ι → A) (s : n) :
    vpack (A := A) w s = bvec 0 (w (s, 0)) + bvec 1 (w (s, 1)) := rfl

end pack

section conj

variable {M M' K K' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
  [AddCommGroup K] [Module A K] [AddCommGroup K'] [Module A K']

/-- Auxiliary: if `f' ∘ e₁ = e₂ ∘ f` for linear equivalences `e₁`, `e₂`, the cokernels of `f`
and `f'` are isomorphic. -/
def quotEquivConj (e₁ : M ≃ₗ[A] M') (e₂ : K ≃ₗ[A] K') (f : M →ₗ[A] K) (f' : M' →ₗ[A] K')
    (h : f' ∘ₗ (e₁ : M →ₗ[A] M') = (e₂ : K →ₗ[A] K') ∘ₗ f) :
    (K ⧸ LinearMap.range f) ≃ₗ[A] (K' ⧸ LinearMap.range f') :=
  Submodule.Quotient.equiv _ _ e₂ (by
    show Submodule.map (e₂ : K →ₗ[A] K') (LinearMap.range f) = _
    rw [← LinearMap.range_comp, ← h, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top])

end conj

end FormalAct
