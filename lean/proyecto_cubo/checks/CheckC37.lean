import RequestProject.Mirror.All

/-! Auditor's check file for Lean piece C37, the mirror that doubles (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C37_the_mirror_that_doubles.md` (§9.3: Lemmas 9.8–9.9, Theorem 9.10,
Corollary 1.7 = Gao et al. Conjecture 5.4), with every hypothesis of the file kept; then
`#print axioms`. -/

open Families

-- (A1) families of N' + 1 for odd N'.
example (N' : ℕ) (hN : N' % 2 = 1) :
    (∀ lam ∈ FamDec.L N', lam % 2 = 1) ∧ FamDec.L (N' + 1) = (FamDec.L N').map (· + 1) ∧
      (∀ μ, FamDec.m (μ + 1) (N' + 1) = FamDec.m μ N') ∧ FamDec.m 0 (N' + 1) = 0 :=
  Mirror.A1 N' hN

-- (A2) ds (λ + 1) for odd λ.
example (lam : ℕ) (hlam : lam % 2 = 1) :
    (ds (lam + 1)).length = (ds lam).length ∧ 0 ∉ Windows.Ids (ds lam) ∧
      Windows.Ids (ds (lam + 1)) = insert 0 (Windows.Ids (ds lam)) ∧
        Dance.mCount (ds (lam + 1)) = Dance.mCount (ds lam) + 1 :=
  Mirror.A2 lam hlam

-- (A3) the dancers of insert 0 I.
example (I : Finset ℕ) (h0 : 0 ∉ I) (q : ℕ) :
    TheoremF.dancer (insert 0 I) (2 * q) = TheoremF.dancer I q ∧
      TheoremF.dancer (insert 0 I) (2 * q + 1) = insert 0 (TheoremF.dancer I q) :=
  Mirror.A3 I h0 q

-- (A4) the small exponents are doubled.
example (lam : ℕ) (hlam : lam % 2 = 1) :
    PodiumCor.smallExps (lam + 1) = PodiumCor.smallExps lam + PodiumCor.smallExps lam :=
  Mirror.A4 lam hlam

-- (A5) the gaps h of insert 0 I.
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range k) (h0 : 0 ∉ I) :
    (∀ t ∈ I, Rulers.h k (insert 0 I) t = Rulers.h k I t) ∧
      Rulers.h k (insert 0 I) 0 = Rulers.t1 k I ∧
      ∀ D ⊆ I, Rulers.hSum k (insert 0 I) D = Rulers.hSum k I D ∧
        Rulers.hSum k (insert 0 I) (insert 0 D) = Rulers.hSum k I D + Rulers.t1 k I :=
  Mirror.A5 k I hI h0

-- (B1) the cube N = 2^e − 1, with J = i + o_D and 1 ≤ J.
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range k) (D : Finset ℕ) (hD : D ⊆ I) (i e : ℕ)
    (hsum : 2 ^ k + Rulers.oE I + 2 * i = 2 ^ e) (hJ : 1 ≤ i + Rulers.oE D) :
    Rulers.clock k I i D = (2 : ℤ) ^ e - 2 * ((i + Rulers.oE D : ℕ) : ℤ) +
      (Rulers.v2 (i + Rulers.oE D) : ℤ) + (Rulers.s2 (i + Rulers.oE D) : ℤ) +
        (Rulers.hSum k I D : ℤ) :=
  Mirror.B1 k I hI hD i e hsum hJ

-- (B2) the cube n = 2^e.
example (k : ℕ) (I : Finset ℕ) (hI : I ⊆ Finset.range k) (D : Finset ℕ) (hD : D ⊆ I) (i e : ℕ)
    (hsum : 2 ^ k + Rulers.oE I + 2 * i = 2 ^ e + 1) (hJ : 1 ≤ i + Rulers.oE D) :
    Rulers.clock k I i D = (2 : ℤ) ^ e + 1 - 2 * ((i + Rulers.oE D : ℕ) : ℤ) +
      (Rulers.s2 (i + Rulers.oE D - 1) : ℤ) + (Rulers.hSum k I D : ℤ) :=
  Mirror.B2 k I hI hD i e hsum hJ

-- (C1) Theorem 9.10.
example (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1)
    (D : Finset ℕ) (hD : D ⊆ Windows.Ids (ds lam)) :
    let i := (2 ^ e - 1 - lam) / 2
    Rulers.clock (ds (lam + 1)).length (Windows.Ids (ds (lam + 1))) i D =
        Rulers.clock (ds lam).length (Windows.Ids (ds lam)) i D ∧
      Rulers.clock (ds (lam + 1)).length (Windows.Ids (ds (lam + 1))) i (insert 0 D) =
        Rulers.clock (ds lam).length (Windows.Ids (ds lam)) i D :=
  Mirror.C1 e he lam hodd hlt hD

-- (F1), (F2) the fit and integer fit of a doubled sequence.
example (N : ℕ) (x : ℕ → ℝ) (j : ℕ) (hj : j < 2 * N) :
    AntitonicFit.fit (2 * N) (fun j => x (j / 2)) j = AntitonicFit.fit N x (j / 2) :=
  Mirror.F1 N x j hj
example (N : ℕ) (x : ℕ → ℤ) (j : ℕ) :
    AntitonicFit.ifit (2 * N) (fun j => x (j / 2)) j = AntitonicFit.ifit N x (j / 2) :=
  Mirror.F2 N x j

-- (X1)–(X3) for odd λ < 2^e − 1 at the shift i = (2^e − 1 − λ)/2.
example (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) (j : ℕ) :
    FamilyGroup.yPool (ds (lam + 1)) ((2 ^ e - 1 - lam) / 2) j =
      FamilyGroup.yPool (ds lam) ((2 ^ e - 1 - lam) / 2) (j / 2) :=
  Mirror.X1 e he lam hodd hlt j
example (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) :
    PodiumCor.bigExps (lam + 1) ((2 ^ e - 1 - lam) / 2) =
      PodiumCor.bigExps lam ((2 ^ e - 1 - lam) / 2) + PodiumCor.bigExps lam ((2 ^ e - 1 - lam) / 2) :=
  Mirror.X2 e he lam hodd hlt
example (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) :
    PodiumCor.famExps (lam + 1) ((2 ^ e - 1 - lam) / 2) =
      PodiumCor.famExps lam ((2 ^ e - 1 - lam) / 2) + PodiumCor.famExps lam ((2 ^ e - 1 - lam) / 2) :=
  Mirror.X3 e he lam hodd hlt

-- (X4) the top family; (X5) the exponents of the cube 2^e.
example (e : ℕ) (he : 1 ≤ e) :
    PodiumCor.famExps (2 ^ e) 0 =
      PodiumCor.famExps (2 ^ e - 1) 0 + PodiumCor.famExps (2 ^ e - 1) 0 + {2 ^ e + e - 1} :=
  Mirror.X4 e he
example (e : ℕ) (he : 1 ≤ e) :
    PodiumCor.exps (2 ^ e) = PodiumCor.exps (2 ^ e - 1) + PodiumCor.exps (2 ^ e - 1) + {2 ^ e + e - 1} :=
  Mirror.X5 e he

-- (Y1), (Y2) Corollary 1.7 (Gao et al. Conjecture 5.4) as groups.
example (e : ℕ) (he : 1 ≤ e) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      ℤ_[2] × ((CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × FamilyGroup.Q (2 ^ e + e - 1))) :=
  Mirror.Y1 e he
example (e : ℕ) (he : 1 ≤ e) :
    Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × ZMod (2 ^ (2 ^ e + e - 1))) :=
  Mirror.Y2 e he

-- Instance: n = 4 (e = 2): S(4) ≅ S(3)² × ZMod 2^5.
example : Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 4) ≃+
    (CubeLaplacian.Syl2 (CubeLaplacian.K 3) × CubeLaplacian.Syl2 (CubeLaplacian.K 3)) × ZMod 32) := by
  simpa using Mirror.Y2 2 (by norm_num)

#print axioms Mirror.A1
#print axioms Mirror.A2
#print axioms Mirror.A3
#print axioms Mirror.A4
#print axioms Mirror.A5
#print axioms Mirror.B1
#print axioms Mirror.B2
#print axioms Mirror.C1
#print axioms Mirror.F1
#print axioms Mirror.F2
#print axioms Mirror.X1
#print axioms Mirror.X2
#print axioms Mirror.X3
#print axioms Mirror.X4
#print axioms Mirror.X5
#print axioms Mirror.Y1
#print axioms Mirror.Y2
#print axioms Mirror.QequivZMod
#print axioms Mirror.cancel_torsion
