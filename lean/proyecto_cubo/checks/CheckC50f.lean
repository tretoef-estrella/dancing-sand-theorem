import RequestProject.GlueEven.All

/-! Auditor's check file for Lean piece C50f: the glued system on `T(l)`
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50f_the_glued_system_on_T.md`;
then `#print axioms`. -/

open FormalOps FormalAct FormalDance GlueEven Pointwise

-- the new definitions, by `rfl`
example (i : ℕ) : ZF i = -(1 : Bf ℤ_[2]) - ((-1 : ℤ_[2]) ^ i) • FoldOdd.ShInvF := rfl
example (V : Type*) [AddCommGroup V] [Module ℤ_[2] V] (v : Fin 2 → V) :
    pairE V v = (v 0, v 1) := rfl
example (l r h : ℕ) : PF l r h =
    ((a : Fin (Families.ds l).length) →
      (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → ℤ_[2]) ⧸
        (2 : ℤ_[2]) ^ (h + (a : ℕ)) • (⊤ : Submodule ℤ_[2]
          (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) →
            ℤ_[2]))) := rfl

-- (S1)
example (h21 : (2 : ℕ) = 2 * 1) (N : DPLattice ℤ_[2]) (W : ℤ) (B : ℕ) (x y z : Bf ℤ_[2])
    (v : Fin 2 → N.ι → ℤ_[2]) :
    pairE _ (FormalAct.sysAct N W B
        (GlueDance.glueC h21 (fun _ _ => x) (fun _ _ => y) (fun _ _ => z)) v) =
      FoldHalf.glueOp (act N W B x) (act N W B y) (act N W B z) (pairE _ v) :=
  S1 h21 N W B x y z v

-- (S2)
example (h21 : (2 : ℕ) = 2 * 1) (N : DPLattice ℤ_[2]) (W : ℤ) (B : ℕ) (x y z : Bf ℤ_[2])
    (h : ℕ) :
    Nonempty (((Fin 2 → N.ι → ℤ_[2]) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h •
        FormalAct.sysAct N W B
          (GlueDance.glueC h21 (fun _ _ => x) (fun _ _ => y) (fun _ _ => z)))) ≃ₗ[ℤ_[2]]
      (((N.ι → ℤ_[2]) × (N.ι → ℤ_[2])) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ h •
        FoldHalf.glueOp (act N W B x) (act N W B y) (act N W B z)))) :=
  S2 h21 N W B x y z h

-- (O1)
example (l i B : ℕ) (hB : l + 1 ≤ B) :
    (2 : ℤ_[2]) • ZF i = FoldOdd.PsiF i - FoldOdd.PsiF (i + 1) ∧
    act (Filt.T ℤ_[2] l) (l : ℤ) B (ZF i) =
      FoldHalf.Zop (Filt.T ℤ_[2] l) ((l : ℤ) + i) (l + 1) := O1 l i B hB

-- (O2)
example (l i B : ℕ) (hB : l + 1 ≤ B) (U U' ZU : Bf ℤ_[2])
    (hU : (2 : ℤ_[2]) • U =
      FoldOdd.PsiF (i + 1) * (FoldOdd.PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hU' : (2 : ℤ_[2]) • U' = FoldOdd.PsiF i * (FoldOdd.PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hZU : Agree (U' - U) ((2 : ℤ_[2]) • ZU)) :
    act (Filt.T ℤ_[2] l) (l : ℤ) B U =
        FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) -
          FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) ∧
      act (Filt.T ℤ_[2] l) (l : ℤ) B U' =
        FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) +
          FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) ∧
      act (Filt.T ℤ_[2] l) (l : ℤ) B ZU =
        FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) :=
  O2 l i B hB U U' ZU hU hU' hZU

-- (Q1) the glued Proposition 10.7
example (h21 : (2 : ℕ) = 2 * 1) (l B h : ℕ) (hB : l + 1 ≤ B) (X Y Z : Bf ℤ_[2])
    (Xk Yk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hP : GlueDance.PairRel (Families.ds l) 1 (fun _ _ => X) (fun _ _ => Y) Xk Yk)
    (hZ : Agree (Y - X) ((2 : ℤ_[2]) • Z)) :
    ∃ Zk, MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧
      Nonempty (((((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ h • FoldHalf.glueOp (act (Filt.T ℤ_[2] l) (l : ℤ) B X)
            (act (Filt.T ℤ_[2] l) (l : ℤ) B Y) (act (Filt.T ℤ_[2] l) (l : ℤ) B Z))) ≃ₗ[ℤ_[2]]
        PF l 2 h × ((Fin (Dance.slots (Families.ds l) 2) → ℤ_[2]) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ (h + (Families.ds l).length) •
            Matrix.mulVecLin (finalM
              (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk))))) :=
  Q1 h21 l B h hB X Y Z Xk Yk hP hZ

-- (Q2) the fold side, operators exactly as in `FoldHalf.A4_even`
example (h21 : (2 : ℕ) = 2 * 1) (l h i : ℕ) :
    ∃ Xk Yk Zk, GlueDance.PairRel (Families.ds l) 1 (fun _ _ => FoldOdd.PsiF (i + 1))
        (fun _ _ => FoldOdd.PsiF i) Xk Yk ∧
      MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧
      Nonempty (((((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ h •
            FoldHalf.glueOp (FoldHalf.Psi (Filt.T ℤ_[2] l) (l + i + 1) (l + 1))
              (FoldHalf.Psi (Filt.T ℤ_[2] l) (l + i) (l + 1))
              (FoldHalf.Zop (Filt.T ℤ_[2] l) (l + i) (l + 1)))) ≃ₗ[ℤ_[2]]
        PF l 2 h × ((Fin (Dance.slots (Families.ds l) 2) → ℤ_[2]) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ (h + (Families.ds l).length) •
            Matrix.mulVecLin (finalM
              (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk))))) :=
  Q2 h21 l h i

-- the fold-side operator of (Q2) is literally the one of `FoldHalf.A4_even`
example (l i : ℕ) :
    Nonempty (FoldGroup.XbarFam (2 * l + 2) i ≃ₗ[ℤ_[2]]
      (((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
        LinearMap.range (FoldHalf.glueOp (FoldHalf.Psi (Filt.T ℤ_[2] l) (l + i + 1) (l + 1))
          (FoldHalf.Psi (Filt.T ℤ_[2] l) (l + i) (l + 1))
          (FoldHalf.Zop (Filt.T ℤ_[2] l) (l + i) (l + 1)))) := FoldHalf.A4_even l i

-- (Q3) the cube side
example (h21 : (2 : ℕ) = 2 * 1) (l h i : ℕ) (U U' ZU : Bf ℤ_[2])
    (hU : (2 : ℤ_[2]) • U =
      FoldOdd.PsiF (i + 1) * (FoldOdd.PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hU' : (2 : ℤ_[2]) • U' = FoldOdd.PsiF i * (FoldOdd.PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])))
    (hZU : Agree (U' - U) ((2 : ℤ_[2]) • ZU))
    (Uk U'k : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hP : GlueDance.PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k) :
    ∃ Zk, MAgree (U'k - Uk) ((2 : ℤ_[2]) • Zk) ∧
      Nonempty (((((Filt.T ℤ_[2] l).ι → ℤ_[2]) × ((Filt.T ℤ_[2] l).ι → ℤ_[2])) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ h • FoldHalf.glueOp
            (FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) -
              FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2))
            (FoldCube.thX (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2) +
              FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2))
            (FoldCube.thY (Filt.T ℤ_[2] l) (l + 1) ((l : ℤ) + i) (2 * l + 2)))) ≃ₗ[ℤ_[2]]
        PF l 2 h × ((Fin (Dance.slots (Families.ds l) 2) → ℤ_[2]) ⧸
          LinearMap.range ((2 : ℤ_[2]) ^ (h + (Families.ds l).length) •
            Matrix.mulVecLin (finalM
              (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Uk U'k Zk))))) :=
  Q3 h21 l h i U U' ZU hU hU' hZU Uk U'k hP

-- (Q4)
example (l i : ℕ) :
    ∃ (U₀ U₀' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (U U' ZU : Bf ℤ_[2])
      (Uk U'k : Matrix (Fin (Dance.slots (Families.ds l) 1))
        (Fin (Dance.slots (Families.ds l) 1)) (Bf ℤ_[2])),
      Cleanliness.Good U₀ ∧ Cleanliness.Good U₀' ∧ DanceMod2.Cong2 U₀ U₀' ∧
      U = RingK.covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U₀ ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ ∧
      U' = RingK.covSys ∅ 0 (((i + 1) / 2 : ℕ) : ℤ_[2]) U₀' ⟨∅, Finset.empty_subset _⟩
        ⟨∅, Finset.empty_subset _⟩ ∧
      (2 : ℤ_[2]) • U =
        FoldOdd.PsiF (i + 1) * (FoldOdd.PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      (2 : ℤ_[2]) • U' = FoldOdd.PsiF i * (FoldOdd.PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧
      Agree (U' - U) ((2 : ℤ_[2]) • ZU) ∧
      GlueDance.PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k := Q4 l i

#print axioms GlueEven.S1
#print axioms GlueEven.S2
#print axioms GlueEven.O1
#print axioms GlueEven.O2
#print axioms GlueEven.Q1
#print axioms GlueEven.Q2
#print axioms GlueEven.Q3
#print axioms GlueEven.Q4
