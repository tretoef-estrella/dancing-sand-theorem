import RequestProject.MainTheorem.All
import RequestProject.BaiCounts.All
import RequestProject.PodiumCor.All
import RequestProject.Mirror.All
import RequestProject.FoldLaw.All
import RequestProject.OddParts.All
import RequestProject.Windows.All

/-! Final check file of the Lean project of «The Dancing Sand Theorem» (paper v8).
Grepy Escribano, 10 October 2026.

Every statement below is restated BY HAND (the types are written out, not copied from a `#check`)
and closed by the name of the certified theorem. If a statement in the project differed from the
paper's wording as restated here, this file would not compile. Then `#print axioms` for each
headline theorem: only `propext`, `Classical.choice`, `Quot.sound` may appear.

The objects first: the group `G n = (ℤ/2)^n`, the Laplacian of the cube `Q_n`, its sandpile group
`K(Q_n)` (the torsion of the cokernel), the `2`-part, and the same for the folded cube
`Q_n/⟨𝟙⟩`, all checked by `rfl` against their definitions. -/

-- ## 0. The objects, by `rfl`.
example (n : ℕ) : CubeLaplacian.G n = (Fin n → ZMod 2) := rfl
example (A : Type) [CommRing A] (n : ℕ) (f : CubeLaplacian.G n → A) (g : CubeLaplacian.G n) :
    CubeLaplacian.lap A n f g = (n : A) * f g - ∑ i, f (g + CubeLaplacian.e n i) := rfl
example (n : ℕ) (i : Fin n) : CubeLaplacian.e n i = Pi.single i 1 := rfl
example (n : ℕ) : CubeLaplacian.coker n =
    ((CubeLaplacian.G n → ℤ) ⧸ LinearMap.range (CubeLaplacian.lap ℤ n)) := rfl
example (n : ℕ) : CubeLaplacian.K n = Submodule.torsion ℤ (CubeLaplacian.coker n) := rfl
example (T : Type) [AddCommGroup T] (y : T) :
    (y ∈ CubeLaplacian.Syl2 T) = (∃ k : ℕ, (2 ^ k : ℕ) • y = 0) := rfl
example (n : ℕ) : Fold.aElt n = (fun _ => (1 : ZMod 2)) := rfl
example (n : ℕ) : Fold.Gbar n =
    (CubeLaplacian.G n ⧸ AddSubgroup.zmultiples (Fold.aElt n)) := rfl
example (A : Type) [CommRing A] (n : ℕ) (u : Fold.Gbar n → A) (x : Fold.Gbar n) :
    Fold.lapBar A n u x = (n : A) * u x - ∑ i, u (x + Fold.mk n (CubeLaplacian.e n i)) := rfl
example (n : ℕ) : Fold.KBar n =
    Submodule.torsion ℤ ((Fold.Gbar n → ℤ) ⧸ LinearMap.range (Fold.lapBar ℤ n)) := rfl
example (n : ℕ) : BaiCounts.aN n = 2 ^ (n - 2) - 2 ^ ((n - 2) / 2) := rfl
example (G : Type) [AddCommGroup G] :
    BaiCounts.l0 G = Nat.card (G ⧸ BaiCounts.twoPow G 1) := rfl

-- ## 1. THE MAIN THEOREM (paper §1.2, Theorem 3.8 + §8): the multiplicity form and the list form.
example (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) →
        MainTheorem.XFam q.1 ((n - q.1) / 2))) :=
  MainTheorem.M1 n hn
example (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((j : Fin (FamDec.L n).length) →
        MainTheorem.XFam ((FamDec.L n).get j) ((n - (FamDec.L n).get j) / 2))) :=
  MainTheorem.M2 n hn
-- the family group, with the pooled clocks written out (shift i + 1)
example (lam i : ℕ) : MainTheorem.XFam lam (i + 1) = (FamilyGroup.SC (Families.ds lam) ×
    ((p : Fin (2 ^ Dance.mCount (Families.ds lam))) →
      (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ (FamilyGroup.yPool (Families.ds lam) (i + 1) p).toNat}))) :=
  rfl
-- the family group is the cokernel family group X of the dance
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FamilyGroup.X (Families.ds lam) 1 i ≃ₗ[ℤ_[2]] MainTheorem.XFam lam i) :=
  MainTheorem.G2 lam hlam i
-- the support of the multiplicities
example (n : ℕ) (hn : 1 ≤ n) (lam : ℕ) (h : FamDec.m lam n ≠ 0) :
    (1 ≤ lam ∧ lam ≤ n ∧ lam % 2 = n % 2) ∧ ((n - lam) / 2 = 0 ↔ lam = n) :=
  ⟨MainTheorem.M3_support n hn lam h, MainTheorem.M3_shift n hn lam h⟩
example (n : ℕ) (hn : 1 ≤ n) : FamDec.m n n = 1 ∧ FamDec.m 0 n = 0 :=
  ⟨MainTheorem.M3_self n hn, MainTheorem.M3_zero n hn⟩

-- ## 2. THEOREM D (paper §4, the windows), over ℤ.
section TheoremD
open Finset Deficit Payment Split Dance Windows
open scoped Pointwise
example (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) :
    Nonempty ((SysT ℤ ds (Fin 1) ⧸ LinearMap.range (sigma ℤ ds α i)) ≃ₗ[ℤ]
      (((a : Fin ds.length) → (Fin (2 ^ (ds.length + mCount ds - 1 - (a : ℕ))) → ℤ) ⧸
          (2 : ℤ) ^ (a : ℕ) •
            (⊤ : Submodule ℤ (Fin (2 ^ (ds.length + mCount ds - 1 - (a : ℕ))) → ℤ))) ×
        ((Fin (2 ^ mCount ds) → ℤ) ⧸ LinearMap.range ((2 : ℤ) ^ ds.length •
          Matrix.toLin' ((Mfin (dance ds 1 (pσ (A := ℤ) α i) κσ).1
              (dance ds 1 (pσ (A := ℤ) α i) κσ).2).submatrix
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)
            (Fin.cast (one_mul (2 ^ mCount ds)).symm)))))) :=
  theorem_D_i ds α i hα
end TheoremD

-- ## 3. COROLLARY 1.5: Bai's two counts.
example (n : ℕ) (hn : 1 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (CubeLaplacian.K n)) = 2 ^ (2 ^ (n - 1) - 1) :=
  BaiCounts.B1 n hn
example (n : ℕ) (hn : 2 ≤ n) :
    BaiCounts.l1 (CubeLaplacian.Syl2 (CubeLaplacian.K n)) =
      2 ^ (2 ^ (n - 1) - 1 - (2 ^ (n - 2) - 2 ^ ((n - 2) / 2))) :=
  BaiCounts.B2 n hn

-- ## 4. COROLLARY 1.6: Gao et al. Thms 4.1–4.2, their Conjecture 4.14, the (n+1)-th factor.
example (n : ℕ) (hn : 3 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (PodiumCor.gmax n) ((Rulers.v2 n : ℤ) + n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n - 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = PodiumCor.gmax n :=
  PodiumCor.G1 n hn
example (n : ℕ) (hn : 3 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) n : ℤ) =
      max (PodiumCor.gmax (n - 1)) ((Rulers.v2 (n - 1) : ℤ) + n - 3) :=
  PodiumCor.G2 n hn
example (n : ℕ) (hn : 4 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) (n + 1) : ℤ) =
      PodiumCor.gmax (n - 1) :=
  PodiumCor.G3 n hn
-- the r-th largest exponent, as defined
example (G : Type) [AddCommGroup G] (r : ℕ) : PodiumCor.cExp G r =
    sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ PodiumCor.layer G (e - 1)} := rfl

-- ## 5. COROLLARY 1.7: Gao et al. Conjecture 5.4.
example (e : ℕ) (he : 1 ≤ e) :
    Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × ZMod (2 ^ (2 ^ e + e - 1))) :=
  Mirror.Y2 e he

-- ## 6. THEOREM DW (the fold law): Syl₂ K̄(n) ≅ 2·Syl₂ K(Q_n), and its consequences.
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    Nonempty (FoldGroup.XbarFam lam i ≃+
      FoldGroup.twoM (FamilyGroup.X (Families.ds lam) 1 i)) :=
  FoldLaw.H lam hlam i
example (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+
      FoldGroup.twoM (CubeLaplacian.Syl2 (CubeLaplacian.K n))) :=
  FoldLaw.DW n hn
example (n : ℕ) (hn : 2 ≤ n) :
    ∃ (H : Type) (_ : AddCommGroup H) (_ : Finite H),
      Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
        (Fin (2 ^ (n - 2) - 2 ^ ((n - 2) / 2)) → ZMod 2) × H) ∧
      Nonempty (CubeLaplacian.Syl2 (Fold.KBar n) ≃+ FoldGroup.twoM H) ∧
      BaiCounts.l0 H = BaiCounts.l1 H :=
  FoldLaw.DW' n hn
example (n : ℕ) (hn : 2 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (Fold.KBar n)) =
      2 ^ (2 ^ (n - 1) - 1 - (2 ^ (n - 2) - 2 ^ ((n - 2) / 2))) :=
  FoldLaw.L1 n hn
example (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) =
      2 ^ (n - 2) - 2 ^ ((n - 2) / 2) :=
  FoldLaw.R n hn

-- ## 7. THE ODD PARTS: Bai's odd part of K(Q_n), and Corollary 1.4 for the folded cube.
example (p : ℕ) (T : Type) [AddCommGroup T] (y : T) :
    (y ∈ OddParts.Sylp p T) = (∃ k : ℕ, (p ^ k : ℕ) • y = 0) := rfl
example (n p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (OddParts.Sylp p (CubeLaplacian.K n) ≃+
      OddParts.Sylp p ((j : Fin n) → Fin (n.choose (j + 1)) → ZMod (j + 1))) :=
  OddParts.B1 n p hp hp2
example (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (OddParts.Sylp p (Fold.KBar n) ≃+
      OddParts.Sylp p ((t : Fin (n / 2)) → Fin (n.choose (2 * (t + 1))) →
        ZMod (2 * (2 * (t + 1))))) :=
  OddParts.C5 n hn p hp hp2

-- ## Axioms of every headline theorem.
#print axioms MainTheorem.M1
#print axioms MainTheorem.M2
#print axioms MainTheorem.G2
#print axioms MainTheorem.M3_support
#print axioms MainTheorem.M3_shift
#print axioms MainTheorem.M3_self
#print axioms MainTheorem.M3_zero
#print axioms Windows.theorem_D_i
#print axioms BaiCounts.B1
#print axioms BaiCounts.B2
#print axioms PodiumCor.G1
#print axioms PodiumCor.G2
#print axioms PodiumCor.G3
#print axioms Mirror.Y2
#print axioms FoldLaw.H
#print axioms FoldLaw.DW
#print axioms FoldLaw.DW'
#print axioms FoldLaw.L1
#print axioms FoldLaw.R
#print axioms OddParts.B1
#print axioms OddParts.C5
