import RequestProject.MainTheorem.All

/-! Auditor's check file for Lean piece C33, the Main Theorem (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C33_the_main_theorem.md` and §1.2 of paper v8: (S1)–(S5); XFam by `rfl` at
shift 0 and i + 1; the pooled clocks unfolded down to `φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`,
`h_t = next(t) − t`, by `rfl`; (G1), (G2); the Main Theorem (M1) with XFam unfolded at both shifts
inside the statement; (M2); (M3); then `#print axioms`. -/

open Families

-- (S1).
example (lam : ℕ) : Rulers.lam (ds lam).length (Windows.Ids (ds lam)) = lam ∧
    Rulers.oE (Windows.Ids (ds lam)) = ∑ t ∈ Windows.Ids (ds lam), 2 ^ t ∧
    lam + 1 = 2 ^ (ds lam).length + Rulers.oE (Windows.Ids (ds lam)) :=
  ⟨MainTheorem.S1_lam lam, MainTheorem.S1_oE lam, MainTheorem.S1_succ lam⟩
-- ξ_D of §1.2.
example (lam : ℕ) (D : Finset ℕ) :
    Rulers.xi (ds lam).length (Windows.Ids (ds lam)) D = lam + 1 - 2 * Rulers.oE D :=
  MainTheorem.S1_xi lam D

-- (S2), (S3).
example (lam : ℕ) : ds lam = [] ↔ lam = 0 := MainTheorem.S2 lam
example (lam : ℕ) (h : 1 ≤ lam) : 1 ≤ (ds lam).length := MainTheorem.S2_length lam h
example (lam : ℕ) : Windows.Ids (ds lam) ⊆ Finset.range (ds lam).length ∧
    (Windows.Ids (ds lam)).card = Dance.mCount (ds lam) :=
  ⟨MainTheorem.S3_subset lam, MainTheorem.S3_card lam⟩

-- (S4) the small clocks written out; the factor a = 0 is zero.
example (d : List Bool) : Nonempty (FamilyGroup.SC d ≃ₗ[ℤ_[2]]
    ((a : Fin d.length) → Fin (2 ^ (d.length + Dance.mCount d - 1 - a)) →
      (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ (a : ℕ)}))) := MainTheorem.S4 d
example : Subsingleton (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ 0}) := MainTheorem.S4_Q0

-- (S5) o-order of the dancers.
example (lam : ℕ) {p q : ℕ} (hpq : p < q) (hq : q < 2 ^ Dance.mCount (ds lam)) :
    Rulers.oE (TheoremF.dancer (Windows.Ids (ds lam)) p) <
      Rulers.oE (TheoremF.dancer (Windows.Ids (ds lam)) q) := MainTheorem.S5_order lam hpq hq
example (I : Finset ℕ) : TheoremF.dancer I 0 = ∅ := MainTheorem.S5_zero I
example (lam : ℕ) {D : Finset ℕ} (hD : D ⊆ Windows.Ids (ds lam)) :
    ∃! p, p < 2 ^ Dance.mCount (ds lam) ∧ TheoremF.dancer (Windows.Ids (ds lam)) p = D :=
  MainTheorem.S5_unique lam hD

-- (G0) by rfl, with the pooled raw clocks of §1.2 unfolded.
example (lam : ℕ) : MainTheorem.XFam lam 0 = (FamilyGroup.SC (ds lam) × (ℤ_[2] ×
    ((q : Fin (2 ^ Dance.mCount (ds lam) - 1)) →
      (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ (FamilyGroup.yPool0 (ds lam) q).toNat})))) := rfl
example (lam i : ℕ) : MainTheorem.XFam lam (i + 1) = (FamilyGroup.SC (ds lam) ×
    ((p : Fin (2 ^ Dance.mCount (ds lam))) →
      (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ (FamilyGroup.yPool (ds lam) (i + 1) p).toNat}))) := rfl
example (d : List Bool) (i : ℕ) : FamilyGroup.yPool d i =
    AntitonicFit.ifit (2 ^ Dance.mCount d) (fun j =>
      let D := TheoremF.dancer (Windows.Ids d) j
      let ξ := Rulers.lam d.length (Windows.Ids d) + 1 - 2 * Rulers.oE D
      ((ξ : ℤ) + Rulers.v2 ξ) +
        (Rulers.s2 (i + Rulers.oE D - 1) + Rulers.s2 ξ - Rulers.s2 (i + Rulers.oE D - 1 + ξ)) +
        (∑ t ∈ D, (Rulers.next d.length (Windows.Ids d) t - t : ℕ) : ℕ)) := rfl
example (d : List Bool) : FamilyGroup.yPool0 d =
    AntitonicFit.ifit (2 ^ Dance.mCount d - 1) (fun j =>
      Rulers.clock d.length (Windows.Ids d) 0 (TheoremF.dancer (Windows.Ids d) (j + 1))) := rfl

-- (G1).
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) (p : ℕ)
    (hp : p < 2 ^ Dance.mCount (ds lam)) : 0 ≤ FamilyGroup.yPool (ds lam) i p :=
  MainTheorem.G1_pos lam hlam i hi p hp
example (lam : ℕ) (hlam : 1 ≤ lam) (hne : Windows.Ids (ds lam) ≠ ∅) (q : ℕ)
    (hq : q < 2 ^ Dance.mCount (ds lam) - 1) : 0 ≤ FamilyGroup.yPool0 (ds lam) q :=
  MainTheorem.G1_zero lam hlam hne q hq

-- (G2).
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FamilyGroup.X (ds lam) 1 i ≃ₗ[ℤ_[2]] MainTheorem.XFam lam i) :=
  MainTheorem.G2 lam hlam i

-- (M1) THE MAIN THEOREM, multiplicity form.
example (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) →
        MainTheorem.XFam q.1 ((n - q.1) / 2))) :=
  MainTheorem.M1 n hn

-- (M2) list form.
example (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((j : Fin (FamDec.L n).length) →
        MainTheorem.XFam ((FamDec.L n).get j) ((n - (FamDec.L n).get j) / 2))) :=
  MainTheorem.M2 n hn

-- (M3).
example (n : ℕ) (hn : 1 ≤ n) (lam : ℕ) (h : FamDec.m lam n ≠ 0) :
    (1 ≤ lam ∧ lam ≤ n ∧ lam % 2 = n % 2) ∧ ((n - lam) / 2 = 0 ↔ lam = n) :=
  ⟨MainTheorem.M3_support n hn lam h, MainTheorem.M3_shift n hn lam h⟩
example (n : ℕ) (hn : 1 ≤ n) : FamDec.m n n = 1 ∧ FamDec.m 0 n = 0 :=
  ⟨MainTheorem.M3_self n hn, MainTheorem.M3_zero n hn⟩

#print axioms MainTheorem.S1_lam
#print axioms MainTheorem.S2
#print axioms MainTheorem.S3_subset
#print axioms MainTheorem.S4
#print axioms MainTheorem.S4_Q0
#print axioms MainTheorem.S5_order
#print axioms MainTheorem.S5_zero
#print axioms MainTheorem.S5_unique
#print axioms MainTheorem.G1_pos
#print axioms MainTheorem.G1_zero
#print axioms MainTheorem.G2
#print axioms MainTheorem.M1
#print axioms MainTheorem.M2
#print axioms MainTheorem.M3_support
#print axioms MainTheorem.M3_shift
#print axioms MainTheorem.M3_self
#print axioms MainTheorem.M3_zero
