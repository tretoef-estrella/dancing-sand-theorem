import RequestProject.PodiumWalk.All

/-! Auditor's check file for Lean piece C35b, the podium walk (Grepy Escribano, 8 Oct 2026).
Restated by hand from `C35b_the_podium_walk.md`, with `λ ≥ 1` kept as in the file (the piece proves
the statements for every `λ`): the pooled clocks unfolded by `rfl` down to the raw clocks; (H1), (H2),
(T1)–(T3), (Z1), (Z2), (C1); then `#print axioms`. -/

open Families

-- The pooled clocks, unfolded (as in CheckC33).
example (d : List Bool) (i : ℕ) : FamilyGroup.yPool d i =
    AntitonicFit.ifit (2 ^ Dance.mCount d) (fun j =>
      Rulers.clock d.length (Windows.Ids d) i (TheoremF.dancer (Windows.Ids d) j)) := rfl
example (d : List Bool) : FamilyGroup.yPool0 d =
    AntitonicFit.ifit (2 ^ Dance.mCount d - 1) (fun j =>
      Rulers.clock d.length (Windows.Ids d) 0 (TheoremF.dancer (Windows.Ids d) (j + 1))) := rfl
-- Y_l and t₁ unfolded.
example (k : ℕ) (I : Finset ℕ) (l : ℕ) :
    Podium.Y k I l = 2 ^ k + Rulers.oE (I \ Podium.P I l) := rfl

-- (H1): the head of the fit is dyadic.
example (lam : ℕ) (_ : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) :
    ∃ l ≤ (Windows.Ids (ds lam)).card, ∀ p < 2 ^ l,
      2 ^ l * FamilyGroup.yPool (ds lam) i p =
        ∑ q ∈ Finset.range (2 ^ l),
          Rulers.clock (ds lam).length (Windows.Ids (ds lam)) i
            (TheoremF.dancer (Windows.Ids (ds lam)) q) :=
  PodiumWalk.H1 lam i hi

-- (H2).
example (lam : ℕ) (_ : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) (p : ℕ)
    (hp : p < 2 ^ (Windows.Ids (ds lam)).card) :
    FamilyGroup.yPool (ds lam) i p ≤ FamilyGroup.yPool (ds lam) i 0 :=
  PodiumWalk.H2 lam i hi p (by rwa [Windows.card_Ids] at hp)

-- (T1): yPool d 1 0 = max_{0 ≤ l ≤ s} φ(Y_l).
example (lam : ℕ) (_ : 1 ≤ lam) :
    (∃ l₀, l₀ ≤ (Windows.Ids (ds lam)).card ∧ FamilyGroup.yPool (ds lam) 1 0 =
        Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l₀)) ∧
      ∀ l, l ≤ (Windows.Ids (ds lam)).card →
        Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l) ≤
          FamilyGroup.yPool (ds lam) 1 0 := by
  obtain ⟨⟨l₀, hl₀, he⟩, hall⟩ := PodiumWalk.T1 lam
  exact ⟨⟨l₀, hl₀, he⟩, fun l hl => hall l hl⟩

-- (T2) with `1 ≤ s` as in the file.
example (lam : ℕ) (_ : 1 ≤ lam) (_ : 1 ≤ (Windows.Ids (ds lam)).card) (p : ℕ) (hp1 : 1 ≤ p)
    (hp : p < 2 ^ Dance.mCount (ds lam)) :
    ∃ l, 1 ≤ l ∧ l ≤ (Windows.Ids (ds lam)).card ∧
      FamilyGroup.yPool (ds lam) 1 p ≤
        Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l) :=
  PodiumWalk.T2 lam p hp1 hp

-- (T3) if 0 ∈ I: yPool d 1 1 = max_{1 ≤ l ≤ s} φ(Y_l).
example (lam : ℕ) (_ : 1 ≤ lam) (h0 : 0 ∈ Windows.Ids (ds lam)) :
    (∃ l₁, 1 ≤ l₁ ∧ l₁ ≤ (Windows.Ids (ds lam)).card ∧ FamilyGroup.yPool (ds lam) 1 1 =
        Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l₁)) ∧
      ∀ l, 1 ≤ l → l ≤ (Windows.Ids (ds lam)).card →
        Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l) ≤
          FamilyGroup.yPool (ds lam) 1 1 :=
  PodiumWalk.T3 lam h0

-- (Z1): yPool0 d 0 = max(φ(Y_1) − 2^{t₁}, max_{2 ≤ l ≤ s} φ(Y_l)).
example (lam : ℕ) (_ : 1 ≤ lam) (hs : 1 ≤ (Windows.Ids (ds lam)).card) :
    let v := FamilyGroup.yPool0 (ds lam) 0
    let k := (ds lam).length
    let I := Windows.Ids (ds lam)
    Rulers.phi (Podium.Y k I 1) - 2 ^ Podium.tAt k I 0 ≤ v ∧
      (∀ l, 2 ≤ l → l ≤ I.card → Rulers.phi (Podium.Y k I l) ≤ v) ∧
      (v = Rulers.phi (Podium.Y k I 1) - 2 ^ Podium.tAt k I 0 ∨
        ∃ l, 2 ≤ l ∧ l ≤ I.card ∧ v = Rulers.phi (Podium.Y k I l)) :=
  PodiumWalk.Z1 lam hs

-- (Z2) with `2 ≤ s` as in the file.
example (lam : ℕ) (_ : 1 ≤ lam) (_ : 2 ≤ (Windows.Ids (ds lam)).card) (q : ℕ) (hq1 : 1 ≤ q)
    (hq : q < 2 ^ Dance.mCount (ds lam) - 1) :
    ∃ l, 2 ≤ l ∧ l ≤ (Windows.Ids (ds lam)).card ∧
      FamilyGroup.yPool0 (ds lam) q ≤
        Rulers.phi (Podium.Y (ds lam).length (Windows.Ids (ds lam)) l) :=
  PodiumWalk.Z2 lam q hq1 hq

-- (C1) Proposition 9.6: every big clock at shift i ≥ 1 is at most φ(y) for some y ≤ λ + i.
example (lam : ℕ) (_ : 1 ≤ lam) (i : ℕ) (hi : 1 ≤ i) (p : ℕ)
    (hp : p < 2 ^ Dance.mCount (ds lam)) :
    ∃ y, 1 ≤ y ∧ y ≤ lam + i ∧ FamilyGroup.yPool (ds lam) i p ≤ Rulers.phi y :=
  PodiumWalk.C1 lam i hi p hp

#print axioms PodiumWalk.H1
#print axioms PodiumWalk.H2
#print axioms PodiumWalk.T1
#print axioms PodiumWalk.T2
#print axioms PodiumWalk.T3
#print axioms PodiumWalk.Z1
#print axioms PodiumWalk.Z2
#print axioms PodiumWalk.C1
#print axioms PodiumWalk.H1_ds
#print axioms PodiumWalk.C1_ds
#print axioms PodiumWalk.Z1_ds
#print axioms PodiumWalk.T1_ds
