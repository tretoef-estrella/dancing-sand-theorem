module

public import RequestProject.FormalProp.PartQ1

/-!
# `C40d_proposition_10_7.md`: (Q1)–(Q4)

* (Q1) `Q1`: Proposition 10.7 in the scaled form, for every `h` (from `Q1_aux`).
* (Q2) `Q2` (`k ≥ 1`) and `Q2_zero` (`k = 0`, i.e. `l = 0`): the form with `h = 0`; the factor
  `a = 0` of (Q1) is the zero module `M ⧸ 2^0·⊤` and is dropped (`pqZeroProd`), the others are
  reindexed by `a ↦ a + 1`.
* (Q3) `Q3`: associated final matrices give isomorphic cokernels, by (Q1) for both systems and
  `cokerUnitMul`.
* (Q4) `Q4`: the operator `σ`, by C40b's `L4_sigma_clean`, (Q1) with `r = 1` and the cast
  `Fin (slots ds 1) ≃ Fin (1 * 2 ^ m)` (`cokerReindex` along `finCongr (slots_eq ds 1).symm`).
-/

@[expose] public section

noncomputable section

namespace FormalProp

open DPLattice Doubling Filt FormalOps FormalDance FormalAct Pointwise

variable {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [OddUnits A]

/-- **(Q1) Proposition 10.7, scaled**, of `C40d_proposition_10_7.md`: with
`k = (Families.ds l).length`, `m = Dance.mCount (Families.ds l)`, if
`DanceRel (Families.ds l) r G Gk` and `B ≥ l + 1`, then for every `h` the cokernel of
`(2 : A) ^ h • sysAct (T A l) l B G` is isomorphic to
`Π_{a < k} (Fin (r * 2 ^ (k + m − 1 − a)) → A) ⧸ 2^(h + a)·⊤` times the cokernel of
`(2 : A) ^ (h + k) • finalM Gk`. -/
theorem Q1 (l r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r))
      (Bf A))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B) (h : ℕ) :
    Nonempty (((Fin r → (T A l).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B G)) ≃ₗ[A]
      (((a : Fin (Families.ds l).length) →
          (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → A) ⧸
            (2 : A) ^ (h + (a : ℕ)) • (⊤ : Submodule A
              (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) →
                A))) ×
        ((Fin (Dance.slots (Families.ds l) r) → A) ⧸
          LinearMap.range ((2 : A) ^ (h + (Families.ds l).length) •
            Matrix.mulVecLin (finalM Gk))))) :=
  Q1_aux _ l rfl r G Gk hG B hB h

/-- (Q2) of `C40d_proposition_10_7.md`, auxiliary: dropping the factor `a = 0` (the zero module
`M ⧸ 2^0·⊤`) and reindexing `a ↦ a + 1`. -/
def dropFirst (k j m r : ℕ) (hj : j + 1 = k) :
    ((a : Fin k) → Dance.PQ A (r * 2 ^ (k + m - 1 - a)) (0 + a)) ≃ₗ[A]
      ((a : Fin j) → Dance.PQ A (r * 2 ^ (k + m - 2 - a)) ((a : ℕ) + 1)) := by
  subst hj
  exact (Fin.consLinearEquiv A
      (fun a : Fin (j + 1) => Dance.PQ A (r * 2 ^ (j + 1 + m - 1 - a)) (0 + a))).symm.trans
    ((LinearEquiv.prodCongr (Dance.pqCast rfl (by simp) :
        Dance.PQ A (r * 2 ^ (j + 1 + m - 1 - ((0 : Fin (j + 1)) : ℕ)))
          (0 + ((0 : Fin (j + 1)) : ℕ)) ≃ₗ[A]
        Dance.PQ A (r * 2 ^ (j + 1 + m - 1 - ((0 : Fin (j + 1)) : ℕ))) 0)
      (LinearEquiv.piCongrRight fun a => Dance.pqCast
        (by simp only [Fin.val_succ]; congr 2; omega)
        (by simp only [Fin.val_succ]; omega))).trans (pqZeroProd _ _))

/-- **(Q2) Proposition 10.7 as printed**, case `k ≥ 1`, of `C40d_proposition_10_7.md`: with
`k = (Families.ds l).length ≥ 1`, `m = Dance.mCount (Families.ds l)`, the cokernel of
`sysAct (T A l) l B G` is isomorphic to
`Π_{a < k − 1} (Fin (r * 2 ^ (k + m − 2 − a)) → A) ⧸ 2^(a + 1)·⊤` times the cokernel of
`(2 : A) ^ k • finalM Gk`. -/
theorem Q2 (l r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r))
      (Bf A))
    (hG : DanceRel (Families.ds l) r G Gk) (B : ℕ) (hB : l + 1 ≤ B)
    (hk : 1 ≤ (Families.ds l).length) :
    Nonempty (((Fin r → (T A l).ι → A) ⧸ LinearMap.range (sysAct (T A l) (l : ℤ) B G)) ≃ₗ[A]
      (((a : Fin ((Families.ds l).length - 1)) →
          (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 2 - a)) → A) ⧸
            (2 : A) ^ ((a : ℕ) + 1) • (⊤ : Submodule A
              (Fin (r * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 2 - a)) →
                A))) ×
        ((Fin (Dance.slots (Families.ds l) r) → A) ⧸
          LinearMap.range ((2 : A) ^ (Families.ds l).length • Matrix.mulVecLin (finalM Gk))))) := by
  obtain ⟨e⟩ := Q1 l r G Gk hG B hB 0
  exact ⟨(Submodule.quotEquivOfEq _ _ (by rw [pow_zero, one_smul])).trans (e.trans
    (LinearEquiv.prodCongr (dropFirst _ _ _ r (by omega))
      (Submodule.quotEquivOfEq _ _ (by rw [zero_add]))))⟩

/-- **(Q2) Proposition 10.7 as printed**, case `k = 0` (`l = 0`), of
`C40d_proposition_10_7.md`: for `B ≥ 1` (i.e. `B ≥ l + 1`), the cokernel of
`sysAct (T A 0) 0 B G` is isomorphic to the cokernel of `finalM G`. (No dance hypothesis is
needed: more general.) -/
theorem Q2_zero (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A)) (B : ℕ) (hB : 1 ≤ B) :
    Nonempty (((Fin r → (T A 0).ι → A) ⧸ LinearMap.range (sysAct (T A 0) 0 B G)) ≃ₗ[A]
      ((Fin r → A) ⧸ LinearMap.range (Matrix.mulVecLin (finalM G)))) := by
  rw [T_zero]
  have := A4 hB G (1 : A)
  rw [one_smul, one_smul] at this
  exact this

/-- **(Q3) Associated final matrices** of `C40d_proposition_10_7.md`: if
`DanceRel (Families.ds l) r G₁ Gk₁`, `DanceRel (Families.ds l) r G₂ Gk₂` and
`finalM Gk₂ = P * finalM Gk₁ * Q` with `IsUnit P.det`, `IsUnit Q.det`, then for every `B ≥ l + 1`
and every `h` the cokernels of `(2 : A) ^ h • sysAct (T A l) l B G₁` and
`(2 : A) ^ h • sysAct (T A l) l B G₂` are isomorphic. -/
theorem Q3 (l r : ℕ) {G₁ G₂ : Matrix (Fin r) (Fin r) (Bf A)}
    {Gk₁ Gk₂ : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r))
      (Bf A)}
    (h₁ : DanceRel (Families.ds l) r G₁ Gk₁) (h₂ : DanceRel (Families.ds l) r G₂ Gk₂)
    (P Q : Matrix (Fin (Dance.slots (Families.ds l) r)) (Fin (Dance.slots (Families.ds l) r)) A)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (hPQ : finalM Gk₂ = P * finalM Gk₁ * Q)
    (B : ℕ) (hB : l + 1 ≤ B) (h : ℕ) :
    Nonempty (((Fin r → (T A l).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B G₁)) ≃ₗ[A]
      ((Fin r → (T A l).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B G₂))) := by
  obtain ⟨e₁⟩ := Q1 l r G₁ Gk₁ h₁ B hB h
  obtain ⟨e₂⟩ := Q1 l r G₂ Gk₂ h₂ B hB h
  exact ⟨e₁.trans ((LinearEquiv.prodCongr (LinearEquiv.refl A _)
    ((cokerUnitMul (finalM Gk₁) P Q hP hQ _).trans
      (Submodule.quotEquivOfEq _ _ (by rw [hPQ])))).trans e₂.symm)⟩

/-- **(Q4) The operator `σ`** of `C40d_proposition_10_7.md`: with `ds = Families.ds l`,
`k = ds.length`, `m = Dance.mCount ds` and
`M = Dance.Mfin (Dance.dance ds 1 (pσ α i) κσ).1 (Dance.dance ds 1 (pσ α i) κσ).2` (a matrix on
`Fin (1 * 2 ^ m)`), for every `B ≥ l + 1` and every `h` the cokernel of
`(2 : A) ^ h • sysAct (T A l) l B (paySys (pσ α i) κσ)` is isomorphic to
`Π_{a < k} (Fin (1 * 2 ^ (k + m − 1 − a)) → A) ⧸ 2^(h + a)·⊤` times the cokernel of
`(2 : A) ^ (h + k) • M`. -/
theorem Q4 (l α i : ℕ) (B : ℕ) (hB : l + 1 ≤ B) (h : ℕ) :
    Nonempty (((Fin 1 → (T A l).ι → A) ⧸
        LinearMap.range ((2 : A) ^ h • sysAct (T A l) (l : ℤ) B
          (paySys (Dance.pσ (A := A) α i) Dance.κσ))) ≃ₗ[A]
      (((a : Fin (Families.ds l).length) →
          (Fin (1 * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) → A) ⧸
            (2 : A) ^ (h + (a : ℕ)) • (⊤ : Submodule A
              (Fin (1 * 2 ^ ((Families.ds l).length + Dance.mCount (Families.ds l) - 1 - a)) →
                A))) ×
        ((Fin (1 * 2 ^ Dance.mCount (Families.ds l)) → A) ⧸
          LinearMap.range ((2 : A) ^ (h + (Families.ds l).length) •
            Matrix.mulVecLin (Dance.Mfin
              (Dance.dance (Families.ds l) 1 (Dance.pσ (A := A) α i) Dance.κσ).1
              (Dance.dance (Families.ds l) 1 (Dance.pσ (A := A) α i) Dance.κσ).2))))) := by
  obtain ⟨-, Gk, hG, hM⟩ := L4_sigma_clean (A := A) (Families.ds l) α i
  obtain ⟨e⟩ := Q1 l 1 _ Gk hG B hB h
  exact ⟨e.trans (LinearEquiv.prodCongr (LinearEquiv.refl A _)
    (cokerReindex (finCongr (Dance.slots_eq (Families.ds l) 1).symm) (finalM Gk) _
      (fun t t' => hM t t') _))⟩

end FormalProp
