import RequestProject.DanceXi.All

/-! Auditor's check file for Lean piece C48b: the dance of Ξ is clean, and Theorem 10.16 for
c ≥ 1 (Grepy Escribano, 10 Oct 2026). Restated by hand from `C48b_the_dance_of_Xi_is_clean.md`;
then `#print axioms`. -/

open RingK FormalOps FormalDance Cleanliness Finset

-- (T1), by `rfl`
example {A : Type} [CommRing A] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (e : n ≃ n') (G : Matrix n' n' (Bf A)) :
    vsplit (fun j j' => G (e j) (e j')) = fun q q' => vsplit G (e q.1, q.2) (e q'.1, q'.2) :=
  rfl

-- (T2), transport
example (ds : List Bool) (r h : ℕ) (P : Finset ℕ) (hP : ∀ t ∈ P, t < h) (c : ℤ_[2])
    (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (e : Fin r ≃ Dn P)
    (G : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hG : G = fun j j' => covSys P h c Γ (e j) (e j')) :
    ∃ Gk, DanceRel ds r G Gk :=
  DanceXi.T2 ds r h P hP c Γ hΓ e G hG

-- (T3), the dance of Ξ
example (ds : List Bool) (α c : ℕ) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2]) :
    ∃ GkZ, DanceRel ds 1 (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)) GkZ :=
  DanceXi.T3 ds α c hα η hη z

-- (R0), l = 0, every c, every ζ
example (α c : ℕ) (hα : 1 ≤ α) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) (B : ℕ) (hB : 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] 0).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] 0) (0 : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η ζ))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds 0) α c) :=
  DanceXi.R0 α c hα η ζ B hB

-- (R2), Theorem 10.16 for c ≥ 1, every l
example (l α c : ℕ) (hα : 2 ≤ α) (hc : 1 ≤ c) (η : ℤ_[2]) (hη : IsUnit η)
    (z : ℕ → ℤ_[2]) (B : ℕ) (hB : l + 1 ≤ B) :
    Nonempty (((Fin 1 → (Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (FormalAct.sysAct (Filt.T ℤ_[2] l) (l : ℤ) B
          (fun _ _ => Smith2.XiOpZ α c η (fun m _ => z m)))) ≃ₗ[ℤ_[2]]
      FamilyGroup.X (Families.ds l) α c) :=
  DanceXi.R2 l α c hα hc η hη z B hB

#print axioms DanceXi.T1
#print axioms DanceXi.T2
#print axioms DanceXi.T3
#print axioms DanceXi.R0
#print axioms DanceXi.R1
#print axioms DanceXi.R2
