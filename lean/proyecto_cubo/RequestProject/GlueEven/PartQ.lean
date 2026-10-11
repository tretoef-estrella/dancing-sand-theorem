module

public import RequestProject.GlueEven.PartO

/-!
# `C50f_the_glued_system_on_T.md`: Part Q — the glued Proposition 10.7

(Q1) the general glued Proposition 10.7 on `T(l)`; (Q2) the fold side; (Q3) the cube side;
(Q4) the cube-side arms exist (with the data of C50c `E2`).

In (Q2), (Q3) and (Q4) the bound `B` of the Part does not occur in the statement (the operators
are `FoldHalf.Psi`, `FoldHalf.Zop`, `FoldCube.thX`, `FoldCube.thY`, which do not depend on `B`),
so these statements are given for all `l h i` without `B`; the proofs use `B = l + 1`.
-/

@[expose] public section

noncomputable section

namespace GlueEven

open FormalOps FormalAct FormalDance

/-- **(Q1)** of `C50f_the_glued_system_on_T.md` (the glued Proposition 10.7, general): for
`l B h : ℕ` with `l + 1 ≤ B`, `X Y Z : Bf ℤ_[2]` and matrices `Xk Yk` on
`Fin (Dance.slots (Families.ds l) 1)` with
`PairRel (Families.ds l) 1 (fun _ _ => X) (fun _ _ => Y) Xk Yk` and `Agree (Y - X) (2 • Z)`,
there is `Zk` with `MAgree (Yk - Xk) (2 • Zk)` and
`(T × T) ⧸ range (2 ^ h • glueOp (act X) (act Y) (act Z)) ≃ₗ[ℤ_[2]]
PF l 2 h × (Fin (slots ds 2) → ℤ_[2]) ⧸ range (2 ^ (h + k) • finalM (glueC (S4 ds h21) Xk Yk Zk))`.
-/
theorem Q1 (h21 : (2 : ℕ) = 2 * 1) (l B h : ℕ) (hB : l + 1 ≤ B) (X Y Z : Bf ℤ_[2])
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
              (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk))))) := by
  obtain ⟨Zk, hZk, hD⟩ := GlueDance.D2 (Families.ds l) h21 hP (fun _ _ => Z) (fun _ _ => hZ)
  obtain ⟨e1⟩ := FormalProp.Q1 (A := ℤ_[2]) l 2 _ _ hD B hB h
  obtain ⟨e2⟩ := S2 h21 (Filt.T ℤ_[2] l) (l : ℤ) B X Y Z h
  exact ⟨Zk, hZk, ⟨e2.symm.trans e1⟩⟩

/-- **(Q2)** of `C50f_the_glued_system_on_T.md` (the fold side): for every `l h i`, there are
`Xk Yk Zk` with `PairRel (Families.ds l) 1 (fun _ _ => PsiF (i + 1)) (fun _ _ => PsiF i) Xk Yk`,
`MAgree (Yk - Xk) (2 • Zk)` and
`(T × T) ⧸ range (2 ^ h • glueOp (Psi T (l + i + 1) (l + 1)) (Psi T (l + i) (l + 1))
(Zop T (l + i) (l + 1))) ≃ₗ[ℤ_[2]] PF l 2 h × …` (the right side as in (Q1)). The bound `B` of
the Part does not occur in the statement and is omitted (more general). -/
theorem Q2 (h21 : (2 : ℕ) = 2 * 1) (l h i : ℕ) :
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
              (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Xk Yk Zk))))) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨Xk, Yk, hP⟩, -⟩ := ArmsEven.E2 i (Families.ds l)
  have hZ : Agree (FoldOdd.PsiF i - FoldOdd.PsiF (i + 1)) ((2 : ℤ_[2]) • ZF i) := by
    rw [two_smul_ZF]; intro _ _ _; rfl
  obtain ⟨Zk, hZk, e⟩ := Q1 h21 l (l + 1) h le_rfl _ _ (ZF i) Xk Yk hP hZ
  rw [(FoldOdd.F4 l (i + 1) 0 (l + 1) le_rfl).1, (FoldOdd.F4 l i 0 (l + 1) le_rfl).1,
    (O1 l i (l + 1) le_rfl).2,
    show ((l : ℤ) + ((i + 1 : ℕ) : ℤ)) = (l : ℤ) + i + 1 by push_cast; ring] at e
  exact ⟨Xk, Yk, Zk, hP, hZk, e⟩

/-- **(Q3)** of `C50f_the_glued_system_on_T.md` (the cube side): for `l h i`, `U U' ZU` as in
(O2) and `Uk U'k` with `PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k`, there is
`Zk` with `MAgree (U'k - Uk) (2 • Zk)` and
`(T × T) ⧸ range (2 ^ h • glueOp (thX - thY) (thX + thY) thY) ≃ₗ[ℤ_[2]] PF l 2 h × …`, with
`thX = FoldCube.thX (T l) (l + 1) (l + i) (2 * l + 2)`, `thY` likewise (the arguments of
`FoldCube.V6`). The bound `B` of the Part does not occur in the statement and is omitted (more
general). -/
theorem Q3 (h21 : (2 : ℕ) = 2 * 1) (l h i : ℕ) (U U' ZU : Bf ℤ_[2])
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
              (GlueDance.glueC (GlueDance.S4 (Families.ds l) h21) Uk U'k Zk))))) := by
  obtain ⟨Zk, hZk, e⟩ := Q1 h21 l (l + 1) h le_rfl U U' ZU Uk U'k hP hZU
  obtain ⟨h1, h2, h3⟩ := O2 l i (l + 1) le_rfl U U' ZU hU hU' hZU
  rw [h1, h2, h3] at e
  exact ⟨Zk, hZk, e⟩

/-- **(Q4)** of `C50f_the_glued_system_on_T.md` (the cube-side arms exist): for every `l i`, with
`c = ((i + 1) / 2 : ℕ)` and `e∅ = ⟨∅, Finset.empty_subset _⟩`, there are
`U₀ U₀' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]`, `U U' ZU : Bf ℤ_[2]` and `Uk U'k` with `Good U₀`,
`Good U₀'`, `Cong2 U₀ U₀'`, `U = covSys ∅ 0 c U₀ e∅ e∅`, `U' = covSys ∅ 0 c U₀' e∅ e∅`, the two
equations of (O2), `Agree (U' - U) (2 • ZU)` and
`PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k`. -/
theorem Q4 (l i : ℕ) :
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
      GlueDance.PairRel (Families.ds l) 1 (fun _ _ => U) (fun _ _ => U') Uk U'k := by
  obtain ⟨U₀, U₀', hg, hg', hc, hE, hE', -, Uk, U'k, hP⟩ := ArmsEven.E2 i (Families.ds l)
  obtain ⟨Zm, hZm⟩ := hP.head
  refine ⟨U₀, U₀', _, _, Zm 0 0, Uk, U'k, hg, hg', hc, rfl, rfl, hE, hE', ?_, hP⟩
  intro m f hmf
  simpa only [Matrix.sub_apply, Matrix.smul_apply, pow_one] using hZm 0 0 m f hmf

end GlueEven
