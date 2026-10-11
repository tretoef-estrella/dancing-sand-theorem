import RequestProject.FormalAct.All

/-! Auditor's check file for Lean piece C40c, the action of a system and one move of the dance
(Grepy Escribano, 9 Oct 2026). Restated by hand from
`C40c_the_action_of_a_system_and_one_move.md`: the definitions by `rfl`; Parts N, A, T, S with the
file's statements; then `#print axioms`. -/

open DPLattice Doubling FormalOps FormalDance FormalAct Filt Finset
open scoped Pointwise

section defs
variable {A : Type} [CommRing A]
example {n : Type} [Fintype n] (N : DPLattice A) (W : ℤ) (B : ℕ) (G : Matrix n n (Bf A))
    (v : n → N.ι → A) (s : n) :
    sysAct N W B G v s = ∑ s', act N W B (G s s') (v s') := rfl
example {n ι : Type} (u v : n → ι → A) (s : n) :
    pack (A := A) (u, v) s = bvec 0 (u s) + bvec 1 (v s) := rfl
example {n ι : Type} (w : n × Fin 2 → ι → A) (s : n) :
    vpack (A := A) w s = bvec 0 (w (s, 0)) + bvec 1 (w (s, 1)) := rfl
end defs

section N
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]
-- (N1)
example (N : DPLattice A) (BN : ℕ) (hnil : ∀ s ≥ BN, N.Fd s = 0) :
    ∀ s ≥ 2 * BN, (phi N).Fd s = 0 := N1 hnil
-- (N2)
example (l : ℕ) :
    (∀ i, (T A l).wt i ≤ (l : ℤ) ∧ Even ((l : ℤ) - (T A l).wt i)) ∧
      (∀ s ≥ l + 1, (T A l).Fd s = 0) := N2 l
end N

section Apart
variable {A : Type} [CommRing A] {n : Type} [Fintype n] (N : DPLattice A) (W : ℤ)
-- (A1)
example (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (G H : Matrix n n (Bf A))
    (h : MAgree G H) (B : ℕ) : sysAct N W B G = sysAct N W B H := A1 htop h B
-- (A2)
example [DecidableEq n] (BN B : ℕ) (hnil : ∀ s ≥ BN, N.Fd s = 0) (hB : BN ≤ B) (hB1 : 1 ≤ B)
    (G H : Matrix n n (Bf A)) (a : A) :
    sysAct N W B (1 : Matrix n n (Bf A)) = LinearMap.id ∧
    sysAct N W B (G * H) = sysAct N W B G ∘ₗ sysAct N W B H ∧
    sysAct N W B (G + H) = sysAct N W B G + sysAct N W B H ∧
    sysAct N W B (G - H) = sysAct N W B G - sysAct N W B H ∧
    sysAct N W B (a • G) = a • sysAct N W B G :=
  let h := A2 (N := N) (W := W) (n := n) hnil hB hB1
  ⟨h.1, h.2.1 G H, h.2.2.1 G H, h.2.2.2.1 G H, h.2.2.2.2 a G⟩
-- (A3)
example {n' : Type} [Fintype n'] (B : ℕ) (e : n ≃ n') (G : Matrix n' n' (Bf A)) :
    sysAct N W B (fun j j' => G (e j) (e j')) =
      (LinearEquiv.funCongrLeft A (N.ι → A) e : (n' → N.ι → A) →ₗ[A] (n → N.ι → A)) ∘ₗ
        sysAct N W B G ∘ₗ
        ((LinearEquiv.funCongrLeft A (N.ι → A) e).symm : (n → N.ι → A) →ₗ[A] (n' → N.ι → A)) :=
  A3_conj B e G
example {n' : Type} [Fintype n'] (B : ℕ) (e : n ≃ n') (G : Matrix n' n' (Bf A)) (c : A) :
    Nonempty (((n → N.ι → A) ⧸ LinearMap.range (c • sysAct N W B (fun j j' => G (e j) (e j'))))
      ≃ₗ[A] ((n' → N.ι → A) ⧸ LinearMap.range (c • sysAct N W B G))) := A3 B e G c
-- (A4)
example (B : ℕ) (hB : 1 ≤ B) (G : Matrix n n (Bf A)) (v : n → Unit → A) (s : n) :
    sysAct (one A) 0 B G v s () = ∑ s', finalM G s s' * v s' () := A4_apply hB G v s
example (B : ℕ) (hB : 1 ≤ B) (G : Matrix n n (Bf A)) (c : A) :
    Nonempty (((n → Unit → A) ⧸ LinearMap.range (c • sysAct (one A) 0 B G)) ≃ₗ[A]
      ((n → A) ⧸ LinearMap.range (c • Matrix.mulVecLin (finalM G)))) := A4 hB G c
end Apart

section Tpart
variable {A : Type} [CommRing A] {n : Type} [Fintype n]
-- (T1)
example [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (W : ℤ) (BN B B' : ℕ)
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (hnil : ∀ s ≥ BN, N.Fd s = 0)
    (hB : 2 * BN ≤ B) (hB' : BN ≤ B') (G : Matrix n n (Bf A)) (u v : n → N.ι → A) :
    sysAct (phi N) (2 * W + 1) B G (pack (u, v)) =
      pack (sysAct N W B' (twB G) u + sysAct N W B' (twD G) v,
        sysAct N W B' (twP G) u + sysAct N W B' (twC G) v) := T1 htop hnil hB hB' G u v
-- (T2)
example (M : DPLattice A) (W : ℤ) (BN B B' : ℕ) (hnil : ∀ s ≥ BN, M.Fd s = 0)
    (hB : BN + 1 ≤ B) (hB' : BN ≤ B') (G : Matrix n n (Bf A)) :
    sysAct (tensorV M) (W + 1) B G ∘ₗ (vpack : (n × Fin 2 → M.ι → A) ≃ₗ[A] _).toLinearMap =
      (vpack : (n × Fin 2 → M.ι → A) ≃ₗ[A] _).toLinearMap ∘ₗ sysAct M W B' (vsplit G) :=
  T2 hnil hB hB' G
end Tpart

section Spart
variable {A : Type} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]
  {n : Type} [Fintype n] [DecidableEq n]
-- (S1)
example (N : DPLattice A) (W : ℤ) (BN B B' : ℕ) (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i))
    (hnil : ∀ s ≥ BN, N.Fd s = 0) (hB : 2 * BN ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B')
    (G G' : Matrix n n (Bf A)) (hC : CleanStep G G') (h : ℕ) :
    Nonempty (((n → (phi N).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (phi N) (2 * W + 1) B G)) ≃ₗ[A]
      (((n → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n → N.ι → A))) ×
        ((n → N.ι → A) ⧸ LinearMap.range ((2 : A) ^ (h + 1) • sysAct N W B' G')))) :=
  S1 htop hnil hB hB' hB1 hC h
-- (S2)
example (N : DPLattice A) (W : ℤ) (BN B B' : ℕ) (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i))
    (hnil : ∀ s ≥ BN, N.Fd s = 0) (hB : 2 * BN + 1 ≤ B) (hB' : BN ≤ B') (hB1 : 1 ≤ B')
    (G : Matrix n n (Bf A)) (G'' : Matrix (n × Fin 2) (n × Fin 2) (Bf A))
    (hC : CleanStep (vsplit G) G'') (h : ℕ) :
    Nonempty (((n → (tensorV (phi N)).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (tensorV (phi N)) (2 * W + 2) B G)) ≃ₗ[A]
      (((n × Fin 2 → N.ι → A) ⧸ ((2 : A) ^ h • ⊤ : Submodule A (n × Fin 2 → N.ι → A))) ×
        ((n × Fin 2 → N.ι → A) ⧸ LinearMap.range ((2 : A) ^ (h + 1) • sysAct N W B' G'')))) :=
  S2 htop hnil hB hB' hB1 hC h
end Spart

#print axioms FormalAct.N1
#print axioms FormalAct.N2
#print axioms FormalAct.A1
#print axioms FormalAct.A2
#print axioms FormalAct.A3_conj
#print axioms FormalAct.A3
#print axioms FormalAct.A4_apply
#print axioms FormalAct.A4
#print axioms FormalAct.T1
#print axioms FormalAct.T2
#print axioms FormalAct.S1
#print axioms FormalAct.S2
