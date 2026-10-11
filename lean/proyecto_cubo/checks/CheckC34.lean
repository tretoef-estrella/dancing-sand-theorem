import RequestProject.BaiCounts.All

/-! Auditor's check file for Lean piece C34, Bai's two counts (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C34_bais_counts.md`: the layers unfolded by `rfl`; (A1)–(A3); (F1), (F2) with c₁
unfolded; (S1)–(S3); (B1), (B2) with a_n unfolded; then `#print axioms`. -/

open Families

-- The layers, unfolded.
example (G : Type) [AddCommGroup G] (x : G) (j : ℕ) :
    x ∈ BaiCounts.twoPow G j ↔ ∃ y : G, 2 ^ j • y = x := Iff.rfl
example (G : Type) [AddCommGroup G] :
    BaiCounts.l0 G = Nat.card (G ⧸ BaiCounts.twoPow G 1) := rfl
example (G : Type) [AddCommGroup G] : BaiCounts.l1 G =
    Nat.card (BaiCounts.twoPow G 1 ⧸ (BaiCounts.twoPow G 2).addSubgroupOf (BaiCounts.twoPow G 1)) :=
  rfl

-- (A1) Lemma 9.1, and the general form.
example (k : ℕ) (hk : 1 ≤ k) (I : Finset ℕ) (hI : I ⊆ Finset.range k) (D : Finset ℕ) (hD : D ⊆ I)
    (i : ℕ) (h : 1 ≤ i ∨ D ≠ ∅) : 2 ≤ Rulers.clock k I i D := BaiCounts.A1 k hk I hI D hD i h
example (k : ℕ) (hk : 1 ≤ k) (I : Finset ℕ) (hI : I ⊆ Finset.range k) (D : Finset ℕ) (hD : D ⊆ I)
    (i : ℕ) : 2 ≤ Rulers.clock k I i D := BaiCounts.A1_general k hk I hI D hD i
example : Rulers.clock 0 ∅ 1 ∅ = 1 := BaiCounts.A1_k_zero
-- (A2).
example (N : ℕ) (x : ℕ → ℤ) (c : ℤ) (hx : ∀ j < N, c ≤ x j) (j : ℕ) (hj : j < N) :
    c ≤ AntitonicFit.ifit N x j := BaiCounts.A2 N x c hx j hj
-- (A3).
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) (p : ℕ)
    (hp : p < 2 ^ Dance.mCount (ds lam)) : 2 ≤ FamilyGroup.yPool (ds lam) i p :=
  BaiCounts.A3_pos lam hlam i hi p hp
example (lam : ℕ) (hlam : 1 ≤ lam) (q : ℕ) (hq : q < 2 ^ Dance.mCount (ds lam) - 1) :
    2 ≤ FamilyGroup.yPool0 (ds lam) q := BaiCounts.A3_zero lam hlam q hq

-- c₁ unfolded.
example (lam : ℕ) : BaiCounts.c1 lam =
    if 2 ≤ (ds lam).length then 2 ^ (Dance.mCount (ds lam) + (ds lam).length - 2) else 0 := rfl
-- (F1), (F2).
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    BaiCounts.l0 (MainTheorem.XFam lam i) = 2 ^ (2 ^ (Dance.mCount (ds lam) + (ds lam).length - 1)) :=
  BaiCounts.F1 lam hlam i
example (lam : ℕ) (hlam : 1 ≤ lam) (i : ℕ) :
    BaiCounts.l1 (MainTheorem.XFam lam i) = 2 ^ (2 ^ (Dance.mCount (ds lam) + (ds lam).length - 1) -
      (if 2 ≤ (ds lam).length then 2 ^ (Dance.mCount (ds lam) + (ds lam).length - 2) else 0)) :=
  BaiCounts.F2 lam hlam i
-- The layers of ℤ_2 and of ℤ/2^e.
example : BaiCounts.l0 ℤ_[2] = 2 ∧ BaiCounts.l1 ℤ_[2] = 2 := ⟨BaiCounts.l0_padic, BaiCounts.l1_padic⟩

-- (S1), (S2), (S3).
example (lam : ℕ) : Fintype.card (Dance.Idx (ds lam)) =
    2 ^ ((ds lam).length + Dance.mCount (ds lam)) := BaiCounts.S1 lam
example (n : ℕ) : ∑ j : Fin (FamDec.L n).length,
    2 ^ ((ds ((FamDec.L n).get j)).length + Dance.mCount (ds ((FamDec.L n).get j))) = 2 ^ n :=
  BaiCounts.S2 n
example (n : ℕ) (hn : 1 ≤ n) :
    (∑ j : Fin (FamDec.L n).length, BaiCounts.c1 ((FamDec.L n).get j) * 4) + 2 * FamDec.m 1 n +
      4 * FamDec.m 2 n = 2 ^ n := BaiCounts.S3 n hn
example (lam : ℕ) : (1 ≤ lam ∧ (ds lam).length ≤ 1) ↔ (lam = 1 ∨ lam = 2) := BaiCounts.S3_short lam

-- (B1), (B2): Bai's two counts, with a_n unfolded.
example (n : ℕ) (hn : 1 ≤ n) :
    BaiCounts.l0 (CubeLaplacian.Syl2 (CubeLaplacian.K n)) = 2 ^ (2 ^ (n - 1) - 1) := BaiCounts.B1 n hn
example (n : ℕ) (hn : 2 ≤ n) :
    BaiCounts.l1 (CubeLaplacian.Syl2 (CubeLaplacian.K n)) =
      2 ^ (2 ^ (n - 1) - 1 - (2 ^ (n - 2) - 2 ^ ((n - 2) / 2))) := BaiCounts.B2 n hn

#print axioms BaiCounts.A1
#print axioms BaiCounts.A1_general
#print axioms BaiCounts.A1_k_zero
#print axioms BaiCounts.A2
#print axioms BaiCounts.A3_pos
#print axioms BaiCounts.A3_zero
#print axioms BaiCounts.F1
#print axioms BaiCounts.F2
#print axioms BaiCounts.l0_padic
#print axioms BaiCounts.l1_padic
#print axioms BaiCounts.S1
#print axioms BaiCounts.S2
#print axioms BaiCounts.S3
#print axioms BaiCounts.S3_short
#print axioms BaiCounts.B1
#print axioms BaiCounts.B2
