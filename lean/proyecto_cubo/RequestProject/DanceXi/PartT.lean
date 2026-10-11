module

public import RequestProject.Cleanliness.All
public import RequestProject.FormalDance.All

/-!
# `C48b_the_dance_of_Xi_is_clean.md`: Part T — transport along the dance

Namespace `DanceXi`. Nothing of the project is redefined: `Good`, `splitDn`, `G0`, (W5), (V3),
(L1), (O1), (O2) are C48's (`Cleanliness`), `Dn`, `covSys` are C47's (`RingK`), `Bf`, `vplus`,
`vprime` are C40's (`FormalOps`), `MAgree`, `vsplit`, `CleanStep`, `DanceRel` are C40b's
(`FormalDance`), `slots`, `splitIso` are C13's (`Dance`) and `XiOpZ` is C46's (`Smith2`).

* (T1) `T1`: an equality of matrices (proved by `rfl`: the case split of `vsplit` only reads
  `q.2`, `q'.2`).
* (T2) `T2`: induction on `ds`, generalizing `r, h, P, Γ, e, G`, exactly as in the sketch. In the
  split clause the new equivalence is
  `e₂ = (splitIso r).symm ≫ ofLex ≫ (e × id) ≫ splitDn P h hP : Fin (r * 2) ≃ Dn (insert h P)`.
* (T3) `T3`: (T2) with `r = 1`, `h = 0`, `P = ∅`, `Γ = G0 α η z` and the unique equivalence
  `Fin 1 ≃ Dn ∅` (`finOneDnEmpty`).
-/

@[expose] public section

noncomputable section

namespace DanceXi

open RingK FormalOps FormalDance Cleanliness Finset

/-- **(T1)** of `C48b_the_dance_of_Xi_is_clean.md` (the `V`-split commutes with reindexing): for
any commutative ring `A`, `Fintype`s `n, n'` with `DecidableEq`, `e : n ≃ n'` and
`G : Matrix n' n' (Bf A)`,
`vsplit (fun j j' => G (e j) (e j')) = fun q q' => vsplit G (e q.1, q.2) (e q'.1, q'.2)`
(an equality). -/
theorem T1 {A : Type*} [CommRing A] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G : Matrix n' n' (Bf A)) :
    vsplit (fun j j' => G (e j) (e j')) = fun q q' => vsplit G (e q.1, q.2) (e q'.1, q'.2) :=
  rfl

/-- **(T2)** of `C48b_the_dance_of_Xi_is_clean.md` (transport): for every `ds : List Bool`,
`r h : ℕ`, `P : Finset ℕ` with `∀ t ∈ P, t < h`, `c : ℤ_[2]`, `Γ` with `Cleanliness.Good Γ`,
`e : Fin r ≃ Dn P` and `G : Matrix (Fin r) (Fin r) (Bf ℤ_[2])` with
`G = fun j j' => covSys P h c Γ (e j) (e j')`, there is `Gk` with `DanceRel ds r G Gk`. -/
theorem T2 (ds : List Bool) (r h : ℕ) (P : Finset ℕ) (hP : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (e : Fin r ≃ Dn P)
    (G : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hG : G = fun j j' => covSys P h c Γ (e j) (e j')) :
    ∃ Gk, DanceRel ds r G Gk := by
  induction ds generalizing r h P Γ G with
  | nil => exact ⟨G, fun s s' m f _ => rfl⟩
  | cons d rest ih =>
    cases d with
    | false =>
      obtain ⟨Γ', hΓ', hC, -⟩ := W5 P h c Γ hΓ
      have hC' := L1 e _ _ hC
      rw [← hG] at hC'
      obtain ⟨Gk, hGk⟩ := ih r (h + 1) P (fun t ht => Nat.lt_succ_of_lt (hP t ht)) Γ' hΓ' e _ rfl
      exact ⟨Gk, _, hC', hGk⟩
    | true =>
      have hhP : h ∉ P := fun hh => lt_irrefl h (hP h hh)
      obtain ⟨Γ', hΓ', hC⟩ := V3 P h c Γ hhP hΓ
      have hC' := L1 (Equiv.prodCongr e (Equiv.refl (Fin 2))) _ _ hC
      have hV : vsplit G = fun q q' =>
          vsplit (covSys P h c Γ) ((Equiv.prodCongr e (Equiv.refl (Fin 2))) q)
            ((Equiv.prodCongr e (Equiv.refl (Fin 2))) q') := by
        rw [hG, T1]; rfl
      rw [← hV] at hC'
      let e₂ : Fin (r * 2) ≃ Dn (insert h P) :=
        ((Dance.splitIso r).symm.toEquiv.trans ofLex).trans
          ((Equiv.prodCongr e (Equiv.refl (Fin 2))).trans (splitDn P h hhP))
      have hP' : ∀ t ∈ insert h P, t < h + 1 := fun t ht => by
        rcases mem_insert.1 ht with rfl | ht
        · exact Nat.lt_succ_self t
        · exact Nat.lt_succ_of_lt (hP t ht)
      obtain ⟨Gk, hGk⟩ := ih (r * 2) (h + 1) (insert h P) hP' Γ' hΓ' e₂ _ rfl
      exact ⟨Gk, _, hC', hGk⟩

/-- (T3) of `C48b_the_dance_of_Xi_is_clean.md`, auxiliary: the unique equivalence
`Fin 1 ≃ Dn ∅`. -/
def finOneDnEmpty : Fin 1 ≃ Dn ∅ where
  toFun _ := ⟨∅, Finset.empty_subset _⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv D := Subtype.ext (Finset.subset_empty.1 D.2).symm

/-- **(T3)** of `C48b_the_dance_of_Xi_is_clean.md` (the dance of `Ξ`): for every `ds : List Bool`,
`α c : ℕ` with `2 ≤ α`, `η : ℤ_[2]` with `IsUnit η`, and `z : ℕ → ℤ_[2]`, there is `GkZ` with
`DanceRel ds 1 (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)) GkZ`. -/
theorem T3 (ds : List Bool) (α c : ℕ) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η)
    (z : ℕ → ℤ_[2]) :
    ∃ GkZ, DanceRel ds 1 (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)) GkZ :=
  T2 ds 1 0 ∅ (fun t ht => absurd ht (Finset.notMem_empty t)) (c : ℤ_[2]) (G0 α η z)
    (O1 α η hα hη z) finOneDnEmpty _ (funext fun _ => funext fun _ => (O2 α c η z).symm)

end DanceXi
