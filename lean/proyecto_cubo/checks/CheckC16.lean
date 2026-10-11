import RequestProject.FamilyGroup.All

/-! Auditor's check file for Lean piece C16 (Grepy Escribano, 7 Oct 2026).
Encodings written out by hand from `C16_the_family_group_over_Z2.md` and closed by `rfl`;
the main statements restated by hand with every object unfolded and closed by the certified
theorems; then `#print axioms`. -/

open Matrix Windows TheoremF FamilyGroup
open scoped Pointwise

-- The group of the tower, the small clocks, the big clocks
example (ds : List Bool) (α i : ℕ) :
    X ds α i = (Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α i)) := rfl
example (ds : List Bool) :
    SC ds = ((a : Fin ds.length) → (Fin (2 ^ (ds.length + Dance.mCount ds - 1 - a)) → ℤ_[2]) ⧸
      (2 : ℤ_[2]) ^ (a : ℕ) •
        (⊤ : Submodule ℤ_[2] (Fin (2 ^ (ds.length + Dance.mCount ds - 1 - a)) → ℤ_[2]))) := rfl
example (e : ℕ) : Q e = (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ e}) := rfl
-- The pooled raw clocks of §1.2
example (ds : List Bool) (i : ℕ) :
    yPool ds i = AntitonicFit.ifit (2 ^ Dance.mCount ds)
      (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j)) := rfl
example (ds : List Bool) :
    yPool0 ds = AntitonicFit.ifit (2 ^ Dance.mCount ds - 1)
      (fun j => Rulers.clock ds.length (Ids ds) 0 (dancer (Ids ds) (j + 1))) := rfl

-- (L1), over any commutative ring
example {R : Type} [CommRing R] {n : ℕ} (B P Q' : Matrix (Fin n) (Fin n) R) (d : Fin n → R)
    (hP : IsUnit P.det) (hQ : IsUnit Q'.det) (h : P * B * Q' = diagonal d) :
    Nonempty (((Fin n → R) ⧸ LinearMap.range (Matrix.toLin' B)) ≃ₗ[R]
      ((j : Fin n) → R ⧸ Ideal.span {d j})) :=
  L1 B P Q' d hP hQ h

-- (U1)
example (z : ℤ) (h : Odd z) : IsUnit (z : ℤ_[2]) := U1 h

-- (X1), with Q, SC, X and the clocks of C15 unfolded
example (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ p < 2 ^ Dance.mCount ds,
        (E p : ℤ) = ds.length + ((α : ℤ) * 2 ^ ds.length + Rulers.kappa (i - 1) (2 ^ ds.length)) +
          AntitonicFit.ifit (2 ^ Dance.mCount ds) (fun j =>
            GoldenMatching.xVal ds.length (Ids ds) (α : ℤ) (i - 1) (dancer (Ids ds) j)) p) ∧
      Nonempty ((Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α i)) ≃ₗ[ℤ_[2]]
        SC ds × ((p : Fin (2 ^ Dance.mCount ds)) → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ E p})) :=
  X1 ds hk α i hα hi

-- (X2)
example (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α) (hne : Ids ds ≠ ∅) :
    ∃ E : ℕ → ℕ, (∀ q < 2 ^ Dance.mCount ds - 1,
        (E q : ℤ) = ds.length + (α : ℤ) * 2 ^ ds.length +
          CellFloor.yhatSharp (Ids ds) ds.length (2 ^ ds.length - 1) α q) ∧
      Nonempty ((Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α 0)) ≃ₗ[ℤ_[2]]
        SC ds × (ℤ_[2] × ((q : Fin (2 ^ Dance.mCount ds - 1)) →
          ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ E q}))) :=
  X2 ds hk α hα hne

-- (X3)
example (ds : List Bool) (α : ℕ) (hα : 1 ≤ α) (hI : Ids ds = ∅) :
    Nonempty ((Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α 0)) ≃ₗ[ℤ_[2]]
      SC ds × ℤ_[2]) :=
  X3 ds α hα hI

-- (R0)
example (N : ℕ) (x : ℕ → ℤ) (c : ℤ) (j : ℕ) (hj : j < N) :
    AntitonicFit.ifit N (fun j => x j + c) j = AntitonicFit.ifit N x j + c :=
  R0 N x c j hj

-- (T1), the exponents are the pooled raw clocks written out
example (ds : List Bool) (hk : 1 ≤ ds.length) (i : ℕ) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ p < 2 ^ Dance.mCount ds, (E p : ℤ) =
        AntitonicFit.ifit (2 ^ Dance.mCount ds)
          (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j)) p) ∧
      Nonempty ((Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds 1 i)) ≃ₗ[ℤ_[2]]
        SC ds × ((p : Fin (2 ^ Dance.mCount ds)) → ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ E p})) :=
  T1 ds hk i hi

-- (T2)
example (ds : List Bool) (hk : 1 ≤ ds.length) (hne : Ids ds ≠ ∅) :
    ∃ E : ℕ → ℕ, (∀ q < 2 ^ Dance.mCount ds - 1, (E q : ℤ) =
        AntitonicFit.ifit (2 ^ Dance.mCount ds - 1)
          (fun j => Rulers.clock ds.length (Ids ds) 0 (dancer (Ids ds) (j + 1))) q) ∧
      Nonempty ((Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds 1 0)) ≃ₗ[ℤ_[2]]
        SC ds × (ℤ_[2] × ((q : Fin (2 ^ Dance.mCount ds - 1)) →
          ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ E q}))) :=
  T2 ds hk hne

#print axioms L1
#print axioms L2
#print axioms L3_unit
#print axioms L3_zero
#print axioms U1
#print axioms U2
#print axioms X1
#print axioms X2
#print axioms X3
#print axioms R0
#print axioms R1
#print axioms R2
#print axioms T1
#print axioms T2
#print axioms T2_empty
