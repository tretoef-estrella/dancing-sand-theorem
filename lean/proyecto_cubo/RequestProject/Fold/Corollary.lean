module

public import RequestProject.Fold.PartL
public import RequestProject.Fold.Transport

/-!
# `C38_the_fold_in_the_group_ring.md`: Part C — Corollary 10.2, module form

* `foldEquivXbar n : (G n → A) ⧸ foldSub A n ≃ₗ[A] Xbar (tensorPow A n) n (n + 1)`, induced by C18's
  `psi A n`, from C18 `psi_comm`, `Tn A n = tauOp (tensorPow A n) n` (`Tn_eq_tauOp`) and (L1).
* (C1) under the hypotheses of C30 (A1): C32 (Q0), C31 (D2), (L3) (with C25 (P1)) and (L4).
* (C2) the case `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod`, with the hypotheses from C28
  `Lift2.Z1` and C21 `Twist.C3_hyp`.

The hypotheses of C30 (A1) are C28's explicit propositions `Lift2.H1 φ`, `Lift2.H2 φ`,
`Lift2.H3 A`, `Lift2.OneAddTwoUnit A` and `h2 : (2 : B) = 0`, with
`[IsDomain A] [CharZero A] [OddUnits A]`; all are used (through C31 (D2)).
-/

@[expose] public section

noncomputable section

namespace Fold

open CubeLaplacian DPLattice Doubling LemmaW Families

variable {A : Type*} [CommRing A]

/-- (C1, sketch) `Tn A n = tauOp (tensorPow A n) n`. -/
lemma Tn_eq_tauOp (n : ℕ) : Tn A n = tauOp (tensorPow A n) n := by
  unfold Tn tauOp
  rw [Int.cast_natCast]
  rfl

/-- (C1, sketch) `(G n → A) ⧸ foldSub A n ≃ₗ[A] Xbar (tensorPow A n) n (n + 1)`, induced by
`psi A n` (C18), for every commutative ring `A` and every `n`. -/
def foldEquivXbar (n : ℕ) :
    ((G n → A) ⧸ foldSub A n) ≃ₗ[A] Xbar (tensorPow A n) n (n + 1) :=
  quotTransport (DPLattice.psi A n) (T₁ := lap A n) (T₂ := transl A n - 1)
    (by rw [DPLattice.psi_comm, Tn_eq_tauOp]) (comm_sub_one _ (L1 n))

/-- **(C1)** of `C38_the_fold_in_the_group_ring.md` (Corollary 10.2, module form): under the
hypotheses of C30 (A1) (`H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A`, `(2 : B) = 0`, with
`[IsDomain A] [CharZero A] [OddUnits A]`), for every `n`,
`(G n → A) ⧸ foldSub A n ≃ₗ[A] Π_{j : Fin (FamDec.L n).length}
  Xbar (Filt.T A ((FamDec.L n).get j)) n (n + 1)`. -/
theorem C1 {B : Type*} [CommRing B] [IsDomain A] [CharZero A] [OddUnits A] {φ : A →+* B}
    (h1 : Lift2.H1 φ) (hk : Lift2.H2 φ) (h3 : Lift2.H3 A) (hU : Lift2.OneAddTwoUnit A)
    (h2 : (2 : B) = 0) (n : ℕ) :
    Nonempty (((G n → A) ⧸ foldSub A n) ≃ₗ[A]
      ((j : Fin (FamDec.L n).length) → Xbar (Filt.T A ((FamDec.L n).get j)) n (n + 1))) := by
  obtain ⟨u⟩ := FamDec.D2 h1 hk h3 hU h2 n
  rw [Q0] at u
  exact ⟨(foldEquivXbar n).trans ((L3equiv u (P1 u.hom) n (n + 1)).trans
    (L4equiv (Filt.T A) (FamDec.L n) n (n + 1)))⟩

/-- **(C2)** of `C38_the_fold_in_the_group_ring.md`: for `A = ℤ_[2]` (with `B = ZMod 2`,
`φ = PadicInt.toZMod`; hypotheses from C28 `Lift2.Z1` and C21 `Twist.C3_hyp`), for every `n`,
`(G n → ℤ_[2]) ⧸ foldSub ℤ_[2] n ≃ₗ[ℤ_[2]] Π_{j : Fin (FamDec.L n).length}
  Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1)`. -/
theorem C2 (n : ℕ) :
    Nonempty (((G n → ℤ_[2]) ⧸ foldSub ℤ_[2] n) ≃ₗ[ℤ_[2]]
      ((j : Fin (FamDec.L n).length) →
        Xbar (Filt.T ℤ_[2] ((FamDec.L n).get j)) n (n + 1))) :=
  C1 (φ := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) Lift2.Z1.1 Lift2.Z1.2.1 Lift2.Z1.2.2.1
    Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 n

end Fold
