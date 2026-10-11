import RequestProject.PodiumCor.All

/-! Auditor's check file for Lean piece C36, the podium corollary (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C36_the_podium_corollary.md`: layer, cExp and the exponent multisets unfolded
by `rfl`; (g0), (D0), (D1), (E1)–(E3), (L1)–(L3), (W1), (W2), (B0)–(B8), (P1)–(P3), (G1)–(G3);
then `#print axioms`. -/

open Families

-- The definitions, unfolded.
example (G : Type) [AddCommGroup G] (j : ℕ) : PodiumCor.layer G j =
    Nat.card (BaiCounts.twoPow G j ⧸
      (BaiCounts.twoPow G (j + 1)).addSubgroupOf (BaiCounts.twoPow G j)) := rfl
example (G : Type) [AddCommGroup G] (r : ℕ) : PodiumCor.cExp G r =
    sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ PodiumCor.layer G (e - 1)} := rfl
example (lam : ℕ) : PodiumCor.smallExps lam =
    ∑ a ∈ Finset.Ico 1 (ds lam).length,
      Multiset.replicate (2 ^ ((Windows.Ids (ds lam)).card + (ds lam).length - 1 - a)) a := rfl
example (lam : ℕ) : PodiumCor.bigExps lam 0 =
    (Finset.range (2 ^ (Windows.Ids (ds lam)).card - 1)).val.map
      (fun q => (FamilyGroup.yPool0 (ds lam) q).toNat) := rfl
example (lam i : ℕ) : PodiumCor.bigExps lam (i + 1) =
    (Finset.range (2 ^ (Windows.Ids (ds lam)).card)).val.map
      (fun p => (FamilyGroup.yPool (ds lam) (i + 1) p).toNat) := rfl
example (lam i : ℕ) : PodiumCor.famExps lam i = PodiumCor.smallExps lam + PodiumCor.bigExps lam i := rfl
example (n : ℕ) : PodiumCor.exps n =
    ((FamDec.L n).map (fun lam => PodiumCor.famExps lam ((n - lam) / 2))).sum := rfl

-- (g0).
example (N : ℕ) (hN : 2 ≤ N) :
    (∃ x, 1 ≤ x ∧ x < N ∧ PodiumCor.gmax N = Rulers.phi x) ∧
      ∀ x, 1 ≤ x → x < N → Rulers.phi x ≤ PodiumCor.gmax N := PodiumCor.g0 N hN

-- (D0), (D1).
example (G : Type) [AddCommGroup G] :
    PodiumCor.layer G 0 = BaiCounts.l0 G ∧ PodiumCor.layer G 1 = BaiCounts.l1 G := PodiumCor.D0 G
example (G H : Type) [AddCommGroup G] [AddCommGroup H] (j : ℕ) :
    PodiumCor.layer (G × H) j = PodiumCor.layer G j * PodiumCor.layer H j := PodiumCor.D1.2.1 G H j
example (j : ℕ) : PodiumCor.layer ℤ_[2] j = 2 := PodiumCor.D1.2.2.2.1 j
example (e j : ℕ) : PodiumCor.layer (FamilyGroup.Q e) j = if j < e then 2 else 1 :=
  PodiumCor.D1.2.2.2.2 e j

-- (E1)–(E3).
example (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    PodiumCor.layer (CubeLaplacian.Syl2 (CubeLaplacian.K n)) j =
      2 ^ ((PodiumCor.exps n).countP (fun e => j < e)) := PodiumCor.E1 n hn j
example (n : ℕ) (hn : 1 ≤ n) (r e : ℕ) (hr : 1 ≤ r) (he : 1 ≤ e) :
    e ≤ PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r ↔
      r ≤ (PodiumCor.exps n).countP (fun x => e ≤ x) := PodiumCor.E2 n hn r e hr he
example (n : ℕ) (hn : 1 ≤ n) (r : ℕ) (hr : 1 ≤ r) :
    PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r =
      ((PodiumCor.exps n).sort (fun a b => b ≤ a)).getD (r - 1) 0 := PodiumCor.E3 n hn r hr

-- (L1)–(L3).
example (n : ℕ) (hn : 1 ≤ n) : FamDec.m n n = 1 := PodiumCor.L1 n hn
example (n : ℕ) (hn : 2 ≤ n) : FamDec.m (n - 2) n = n - 1 - (if n % 2 = 0 then 1 else 0) :=
  PodiumCor.L2 n hn
example (n : ℕ) (hn : 5 ≤ n) (ho : n % 2 = 1) :
    FamDec.m (n - 4) n = (n - 1) * (n - 2) / 2 - 1 - (if n % 4 = 1 then 1 else 0) ∧
      4 ≤ FamDec.m (n - 4) n := PodiumCor.L3 n hn ho

-- (W1), (W2).
example (k : ℕ) (I D : Finset ℕ) (hk : 1 ≤ k) (h0 : 0 ∉ I) (hD : D ⊆ I) :
    Rulers.clock k I 2 D = Rulers.clock k I 1 D := PodiumCor.W1 k I D hk h0 hD
example (lam : ℕ) (ho : lam % 2 = 1) :
    FamilyGroup.yPool (ds lam) 2 = FamilyGroup.yPool (ds lam) 1 := PodiumCor.W2 lam ho

-- (B0)–(B8), n ≥ 4, G = gmax (n − 1).
example (n lam : ℕ) (hn : 4 ≤ n) (hl : 1 ≤ lam) (hm : FamDec.m lam n ≠ 0) :
    ((ds lam).length : ℤ) - 1 < PodiumCor.gmax (n - 1) := PodiumCor.B0 n lam hn hl hm
example (n lam : ℕ) (hn : 4 ≤ n) (hl : 1 ≤ lam) (hm : FamDec.m lam n ≠ 0)
    (hi : 2 ≤ (n - lam) / 2) (p : ℕ) (hp : p < 2 ^ Dance.mCount (ds lam)) :
    FamilyGroup.yPool (ds lam) ((n - lam) / 2) p ≤ PodiumCor.gmax (n - 1) :=
  PodiumCor.B1 n lam hn hl hm hi p hp
example (n : ℕ) (hn : 4 ≤ n) :
    FamilyGroup.yPool (ds (n - 2)) 1 0 = max (PodiumCor.gmax (n - 1)) (Rulers.phi (n - 1)) ∧
      ∀ p, 1 ≤ p → p < 2 ^ Dance.mCount (ds (n - 2)) →
        FamilyGroup.yPool (ds (n - 2)) 1 p ≤ PodiumCor.gmax (n - 1) := PodiumCor.B2 n hn
example (n : ℕ) (hn : 4 ≤ n) (_ : 1 ≤ (Windows.Ids (ds n)).card) :
    (∀ q, 1 ≤ q → q < 2 ^ Dance.mCount (ds n) - 1 →
        FamilyGroup.yPool0 (ds n) q ≤ PodiumCor.gmax (n - 1)) ∧
      ∀ l, 2 ≤ l → l ≤ (Windows.Ids (ds n)).card →
        Rulers.phi (Podium.Y (ds n).length (Windows.Ids (ds n)) l) ≤ PodiumCor.gmax (n - 1) :=
  PodiumCor.B3 n hn
example (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    Rulers.phi n - 1 ≤ FamilyGroup.yPool0 (ds n) 0 ∧
      FamilyGroup.yPool0 (ds n) 0 ≤ max (PodiumCor.gmax (n - 1)) (Rulers.phi n - 1) :=
  PodiumCor.B4 n hn he
example (n : ℕ) (hn : 4 ≤ n) (h4 : n % 4 = 1) :
    Rulers.phi (n - 1) - 2 ≤ FamilyGroup.yPool0 (ds n) 0 ∧
      FamilyGroup.yPool0 (ds n) 0 ≤ max (PodiumCor.gmax (n - 1)) (Rulers.phi (n - 1) - 2) :=
  PodiumCor.B5 n hn h4
example (n : ℕ) (hn : 4 ≤ n) (h4 : n % 4 = 3) (hs : 1 ≤ (Windows.Ids (ds n)).card) :
    FamilyGroup.yPool0 (ds n) 0 ≤ PodiumCor.gmax (n - 1) := PodiumCor.B6 n hn h4 hs
example (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    FamilyGroup.yPool (ds (n - 2)) 1 0 = PodiumCor.gmax (n - 1) ∧
      FamilyGroup.yPool (ds (n - 2)) 1 1 = PodiumCor.gmax (n - 1) ∧
        2 ≤ 2 ^ Dance.mCount (ds (n - 2)) := PodiumCor.B7 n hn he
example (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) :
    FamilyGroup.yPool (ds (n - 4)) 2 0 = PodiumCor.gmax (n - 1) := PodiumCor.B8 n hn ho

-- (P1)–(P3), Corollary 1.6.
example (n : ℕ) (hn : 4 ≤ n) (hev : n % 2 = 0) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (PodiumCor.gmax (n - 1)) (Rulers.phi n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n + 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = PodiumCor.gmax (n - 1) :=
  PodiumCor.P1 n hn hev
example (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) (hphi : Rulers.phi (n - 1) ≤ PodiumCor.gmax (n - 1)) :
    ∀ r, 1 ≤ r → r ≤ n + 1 →
      (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = PodiumCor.gmax (n - 1) :=
  PodiumCor.P2 n hn ho hphi
example (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) (hphi : PodiumCor.gmax (n - 1) < Rulers.phi (n - 1)) :
    (∀ r, 1 ≤ r → r ≤ n - 1 →
      (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = Rulers.phi (n - 1)) ∧
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) n : ℤ) =
      max (PodiumCor.gmax (n - 1)) (Rulers.phi (n - 1) - 2) ∧
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) (n + 1) : ℤ) = PodiumCor.gmax (n - 1) :=
  PodiumCor.P3 n hn ho hphi

-- (G1)–(G3): Gao et al. Thms 4.1–4.2, Conj. 4.14, the poster's (n+1)-th factor.
example (n : ℕ) (hn : 3 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) 1 : ℤ) =
        max (PodiumCor.gmax n) ((Rulers.v2 n : ℤ) + n - 1) ∧
      ∀ r, 2 ≤ r → r ≤ n - 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) r : ℤ) = PodiumCor.gmax n :=
  PodiumCor.G1 n hn
example (n : ℕ) (hn : 3 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) n : ℤ) =
      max (PodiumCor.gmax (n - 1)) ((Rulers.v2 (n - 1) : ℤ) + n - 3) := PodiumCor.G2 n hn
example (n : ℕ) (hn : 4 ≤ n) :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K n)) (n + 1) : ℤ) =
      PodiumCor.gmax (n - 1) := PodiumCor.G3 n hn

#print axioms PodiumCor.g0
#print axioms PodiumCor.D0
#print axioms PodiumCor.D1
#print axioms PodiumCor.E1
#print axioms PodiumCor.E2
#print axioms PodiumCor.E3
#print axioms PodiumCor.L1
#print axioms PodiumCor.L2
#print axioms PodiumCor.L3
#print axioms PodiumCor.W1
#print axioms PodiumCor.W2
#print axioms PodiumCor.B0
#print axioms PodiumCor.B1
#print axioms PodiumCor.B2
#print axioms PodiumCor.B3
#print axioms PodiumCor.B4
#print axioms PodiumCor.B5
#print axioms PodiumCor.B6
#print axioms PodiumCor.B7
#print axioms PodiumCor.B8
#print axioms PodiumCor.P1
#print axioms PodiumCor.P2
#print axioms PodiumCor.P3
#print axioms PodiumCor.G1
#print axioms PodiumCor.G2
#print axioms PodiumCor.G3
