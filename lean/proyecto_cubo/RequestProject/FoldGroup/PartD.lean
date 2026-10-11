module

public import RequestProject.FoldGroup.PartK

/-!
# `C38b_the_folded_cube_and_proposition_103.md`: Part D — Corollary 10.2 as groups

* (D1) `D1` (list form): (K3), C38 `G3equiv` over `ℤ_[2]`, C38 `C2`.
* (D2) `D2` (shift form): on the support `λ + 2 · ((n − λ) / 2) = n` (`add_two_mul_shift`, from
  C31 (M3) and `L 0 = [0]`).
* (D3) `D3` (multiplicity form): (D2) and the reindexing of C32 (T3) (`Families.famReindex`,
  the counting form of C31 (M4)).

Groups are indexed exactly as in the file: `Fin (FamDec.L n).length` with `λ_j = (FamDec.L n).get j`
in (D1), (D2), and `Σ λ : Fin (n + 1), Fin (FamDec.m λ n)` in (D3).
-/

@[expose] public section

noncomputable section

namespace FoldGroup

open CubeLaplacian Fold

variable (n : ℕ)

/-- **(D1)** of `C38b_the_folded_cube_and_proposition_103.md` (list form): for every `n`,
`ℤ_[2] × Syl2 (KBar n) ≃+ Π_{j : Fin (FamDec.L n).length}
  Fold.Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1)`. -/
theorem D1 :
    Nonempty (ℤ_[2] × Syl2 (KBar n) ≃+
      ((j : Fin (FamDec.L n).length) →
        Fold.Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1))) := by
  obtain ⟨k3⟩ := K3 n
  obtain ⟨c2⟩ := Fold.C2 n
  exact ⟨k3.symm.trans ((G3equiv ℤ_[2] n).toAddEquiv.trans c2.toAddEquiv)⟩

/-- (D2, sketch) the support: for `λ ∈ FamDec.L n`, `λ + 2 · ((n − λ) / 2) = n` (from C31 (M3),
and `L 0 = [0]`). -/
lemma add_two_mul_shift {lam : ℕ} (h : lam ∈ FamDec.L n) : lam + 2 * ((n - lam) / 2) = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [FamDec.mem_L_zero] at h; subst h; rfl
  · have := FamDec.M3 n hn lam h
    omega

/-- Transport of `Fold.Xbar M c B` along equalities of `c` and `B` (auxiliary for (D2)). -/
def castXbar {A : Type*} [CommRing A] (M : DPLattice A) {c c' : ℤ} {B B' : ℕ} (hc : c = c')
    (hB : B = B') : Fold.Xbar M c B ≃ₗ[A] Fold.Xbar M c' B' := by
  subst hc hB; exact LinearEquiv.refl _ _

/-- (D2, auxiliary) for `λ ∈ FamDec.L n`,
`Fold.Xbar (Filt.T ℤ_[2] λ) n (n + 1) ≃ₗ[ℤ_[2]] XbarFam λ ((n − λ) / 2)`. -/
def xbarShift {lam : ℕ} (h : lam ∈ FamDec.L n) :
    Fold.Xbar (Filt.T ℤ_[2] lam) n (n + 1) ≃ₗ[ℤ_[2]] XbarFam lam ((n - lam) / 2) :=
  castXbar _ (by have := add_two_mul_shift n h; omega) (by have := add_two_mul_shift n h; omega)

/-- **(D2)** of `C38b_the_folded_cube_and_proposition_103.md` (shift form): for every `n`,
`ℤ_[2] × Syl2 (KBar n) ≃+ Π_{j : Fin (FamDec.L n).length}
  XbarFam ((FamDec.L n).get j) ((n − (FamDec.L n).get j) / 2)`. -/
theorem D2 :
    Nonempty (ℤ_[2] × Syl2 (KBar n) ≃+
      ((j : Fin (FamDec.L n).length) →
        XbarFam ((FamDec.L n).get j) ((n - (FamDec.L n).get j) / 2))) := by
  obtain ⟨d1⟩ := D1 n
  exact ⟨d1.trans (AddEquiv.piCongrRight fun j =>
    (xbarShift n (List.get_mem (FamDec.L n) j)).toAddEquiv)⟩

/-- Transport of `XbarFam a ((n − a) / 2)` along an equality of `a` (auxiliary for (D3)). -/
def castXbarFam {a b : ℕ} (h : a = b) :
    XbarFam a ((n - a) / 2) ≃ₗ[ℤ_[2]] XbarFam b ((n - b) / 2) := by
  subst h; exact LinearEquiv.refl _ _

/-- **(D3)** of `C38b_the_folded_cube_and_proposition_103.md` (multiplicity form, the paper's
`ℤ_2 ⊕ Syl_2 K̄(n) ≅ ⊕_λ X̄(λ, (n − λ)/2)^{m_λ(n)}`): for every `n`,
`ℤ_[2] × Syl2 (KBar n) ≃+ Π_{q : Σ λ : Fin (n + 1), Fin (FamDec.m λ n)} XbarFam q.1 ((n − q.1) / 2)`. -/
theorem D3 :
    Nonempty (ℤ_[2] × Syl2 (KBar n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) → XbarFam q.1 ((n - q.1) / 2))) := by
  obtain ⟨e⟩ := D2 n
  have hl : ∀ x ∈ FamDec.L n, x < n + 1 := fun x hx =>
    Nat.lt_succ_of_le (FamDec.le_of_mem_L n x hx)
  let r := Families.famReindex (FamDec.L n) (n + 1) hl
  let P : ℕ → Type := fun a => XbarFam a ((n - a) / 2)
  let e1 : ((j : Fin (FamDec.L n).length) → P ((FamDec.L n).get j)) ≃ₗ[ℤ_[2]]
      ((q : Σ a : Fin (n + 1), Fin ((FamDec.L n).count a.val)) → P q.1) :=
    (LinearEquiv.piCongrLeft ℤ_[2] (fun j => P ((FamDec.L n).get j)) r.symm).symm.trans
      (LinearEquiv.piCongrRight fun q =>
        castXbarFam n (Families.famReindex_get (FamDec.L n) (n + 1) hl q))
  exact ⟨e.trans e1.toAddEquiv⟩

end FoldGroup
