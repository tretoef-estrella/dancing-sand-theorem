import RequestProject.ContZero.All

/-! Auditor's check file for Lean piece C49b: congruence along the dance, and the data of Ξ at
c = 0 (Grepy Escribano, 10 Oct 2026). Restated by hand from
`C49b_congruence_and_the_data_at_zero.md`; then `#print axioms`. -/

open FormalOps FormalDance ContZero

-- the two new definitions, by `rfl`
example (M : ℕ) (x y : Bf ℤ_[2]) :
    Cong M x y = ∃ z : Bf ℤ_[2], Agree (x - y) ((2 : ℤ_[2]) ^ M • z) := rfl
example {n : Type} (M : ℕ) (G H : Matrix n n (Bf ℤ_[2])) :
    MCong M G H = ∃ Z : Matrix n n (Bf ℤ_[2]), MAgree (G - H) ((2 : ℤ_[2]) ^ M • Z) := rfl

-- (K4) inverses
example {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (P Q P' Q' : Matrix n n (Bf ℤ_[2]))
    (h1 : MAgree (P * Q) 1) (h2 : MAgree (Q * P) 1) (h3 : MAgree (P' * Q') 1)
    (h4 : MAgree (Q' * P') 1) (hP : MCong M P P') : MCong M Q Q' :=
  K4 h1 h2 h3 h4 hP

-- (K6) one clean move
example {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (G G' H H' : Matrix n n (Bf ℤ_[2]))
    (hG : CleanStep G G') (hH : CleanStep H H') (hGH : MCong (M + 1) G H) : MCong M G' H' :=
  K6 hG hH hGH

-- (T1) transport along the dance
example (ds : List Bool) (r M : ℕ) (G H : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (Gk Hk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2]))
    (hG : DanceRel ds r G Gk) (hH : DanceRel ds r H Hk) (hGH : MCong (M + ds.length) G H) :
    MCong M Gk Hk :=
  T1 ds r M G H Gk Hk hG hH hGH

-- (T3) uniqueness of finalM
example (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (Gk Hk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2]))
    (hG : DanceRel ds r G Gk) (hH : DanceRel ds r G Hk) : finalM Gk = finalM Hk :=
  T3 hG hH

-- (C1) XiOpZ congruent in c
example (α c c' N : ℕ) (hN : (2 : ℤ) ^ N ∣ (c' : ℤ) - c) (η : ℤ_[2]) (ζ : ℕ → ℤ → ℤ_[2]) :
    Cong (α + N) (Smith2.XiOpZ α c η ζ) (Smith2.XiOpZ α c' η ζ) :=
  C1 α c c' N hN η ζ

-- (C3) the integer final matrices congruent in c
example (α : ℕ) (hα : 1 ≤ α) (ds : List Bool) (c c' N M : ℕ)
    (hN : (2 : ℤ) ^ N ∣ (c' : ℤ) - c) (hM : M + ds.length = α + N)
    (s s' : Fin (2 ^ Dance.mCount ds)) :
    (2 : ℤ) ^ M ∣ Windows.finalMatrix ℤ ds α c s s' - Windows.finalMatrix ℤ ds α c' s s' :=
  C3 hα ds c c' N M hN hM s s'

-- (V1) norms at c = 0
example (l α : ℕ) (hl : 1 ≤ l) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ)
    (s s' : Fin (2 ^ Dance.mCount (Families.ds l))) :
    ‖finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l)) s)
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s')‖ =
      ‖((Windows.finalMatrix ℤ (Families.ds l) α 0 s s' : ℤ) : ℤ_[2])‖ :=
  V1 hl hα hη z GkZ hG s s'

-- (V3) the row of ∅ and det 0
example (l α : ℕ) (hl : 1 ≤ l) (hα : 2 ≤ α) (η : ℤ_[2]) (hη : IsUnit η) (z : ℕ → ℤ_[2])
    (GkZ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℤ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Smith2.XiOpZ α 0 η (fun m _ => z m)) GkZ) :
    (∀ s' : Fin (2 ^ Dance.mCount (Families.ds l)),
      finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l))
          (DanceSmith.sl (Families.ds l) (DanceSmith.zeroPos (Families.ds l))))
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s') = 0) ∧
    Matrix.det (fun s s' : Fin (2 ^ Dance.mCount (Families.ds l)) =>
      finalM GkZ (Fin.cast (Smith2.slots_cast (Families.ds l)) s)
        (Fin.cast (Smith2.slots_cast (Families.ds l)) s')) = 0 :=
  V3 hl hα hη z GkZ hG

#print axioms ContZero.K1
#print axioms ContZero.K2
#print axioms ContZero.K3
#print axioms ContZero.K4
#print axioms ContZero.K5
#print axioms ContZero.K6
#print axioms ContZero.T1
#print axioms ContZero.T2
#print axioms ContZero.T3
#print axioms ContZero.C1
#print axioms ContZero.C2
#print axioms ContZero.C3
#print axioms ContZero.V1
#print axioms ContZero.V2
#print axioms ContZero.V3
