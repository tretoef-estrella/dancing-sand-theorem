import RequestProject.FormalDance.All

/-! Auditor's check file for Lean piece C40b, the formal dance of payment systems
(Grepy Escribano, 9 Oct 2026). Restated by hand from
`C40b_the_formal_dance_of_payment_systems.md`: the definitions by `rfl`; Parts C and L with the
file's statements; then `#print axioms`. -/

open FormalOps FormalDance Finset Split Dance

section defs
variable {A : Type} [CommRing A]

example (x y : Bf A) : Agree x y ↔ ∀ (m : ℕ) (f : ℤ), (m : ℤ) ≤ f → x.coef m f = y.coef m f :=
  Iff.rfl
example {n : Type} (G H : Matrix n n (Bf A)) : MAgree G H ↔ ∀ s s', Agree (G s s') (H s s') :=
  Iff.rfl
example (q : ℕ → A) (f : ℤ) : ext0 q f = if 0 ≤ f then q f.toNat else 0 := rfl
example {n : Type} [LinearOrder n] (p : n → ℕ → A) (κ : n → n → ℕ → A) (s s' : n) :
    paySys p κ s s' =
      if s = s' then Bf.fd 1 + Bf.dg (ext0 (fun f => 2 * p s f))
      else if s' < s then Bf.dg (ext0 (fun f => 2 * κ s s' f)) else 0 := rfl
example {n : Type} (G : Matrix n n (Bf A)) (s s' : n) :
    twP G s s' = tw10 (G s s') ∧ twC G s s' = tw11 (G s s') ∧
    twB G s s' = tw00 (G s s') ∧ twD G s s' = tw01 (G s s') := ⟨rfl, rfl, rfl, rfl⟩
example {n : Type} (G : Matrix n n (Bf A)) (s s' : n) (v v' : Fin 2) :
    vsplit G (s, v) (s', v') =
      if v = 0 ∧ v' = 0 then G s s' else if v = 1 ∧ v' = 0 then vprime (G s s')
      else if v = 1 ∧ v' = 1 then vplus (G s s') else 0 := rfl
example {n : Type} [Fintype n] [DecidableEq n] (G G' : Matrix n n (Bf A)) :
    CleanStep G G' ↔ ∃ Q : Matrix n n (Bf A), MAgree (twP G * Q) 1 ∧ MAgree (Q * twP G) 1 ∧
      MAgree (twD G - twB G * Q * twC G) ((2 : A) • G') := Iff.rfl
example (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A)) (Gk : Matrix (Fin r) (Fin r) (Bf A)) :
    DanceRel [] r G Gk ↔ MAgree G Gk := Iff.rfl
example (rest : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (slots (false :: rest) r)) (Fin (slots (false :: rest) r)) (Bf A)) :
    DanceRel (false :: rest) r G Gk ↔ ∃ G', CleanStep G G' ∧ DanceRel rest r G' Gk := Iff.rfl
example (rest : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (slots (true :: rest) r)) (Fin (slots (true :: rest) r)) (Bf A)) :
    DanceRel (true :: rest) r G Gk ↔
      ∃ G'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf A), CleanStep (vsplit G) G'' ∧
        DanceRel rest (r * 2) (fun j j' => G'' (ofLex ((splitIso r).symm j))
          (ofLex ((splitIso r).symm j'))) Gk := Iff.rfl
example (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A)) :
    Clean ds r G ↔ ∃ Gk, DanceRel ds r G Gk := Iff.rfl
example {m : Type} (Gk : Matrix m m (Bf A)) (s s' : m) : finalM Gk s s' = (Gk s s').coef 0 0 :=
  rfl
end defs

section C
variable {A : Type} [CommRing A]
-- (C1)
example (n : Type) : Equivalence (Agree (A := A)) ∧ Equivalence (MAgree (A := A) (n := n)) :=
  C1 n
-- (C2)
example (n : Type) [Fintype n] (x x' y y' : Bf A) (hx : Agree x x') (hy : Agree y y') (a : A) :
    Agree (x + y) (x' + y') ∧ Agree (x - y) (x' - y') ∧ Agree (x * y) (x' * y') ∧
      Agree (a • x) (a • x') :=
  let h := (C2 (A := A) n).1 x x' y y' hx hy
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 a⟩
example (n : Type) [Fintype n] (G G' H H' : Matrix n n (Bf A)) (hG : MAgree G G')
    (hH : MAgree H H') (a : A) :
    MAgree (G + H) (G' + H') ∧ MAgree (G - H) (G' - H') ∧ MAgree (G * H) (G' * H') ∧
      MAgree (a • G) (a • G') :=
  let h := (C2 (A := A) n).2 G G' H H' hG hH
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2 a⟩
-- (C3)
example (n : Type) (x y : Bf A) (h : Agree x y) :
    Agree (tw00 x) (tw00 y) ∧ Agree (tw11 x) (tw11 y) ∧ Agree (tw10 x) (tw10 y) ∧
    Agree (tw01 x) (tw01 y) ∧ Agree (vplus x) (vplus y) ∧ Agree (vprime x) (vprime y) :=
  (C3 (A := A) n).1 x y h
example (n : Type) (G H : Matrix n n (Bf A)) (h : MAgree G H) :
    MAgree (twP G) (twP H) ∧ MAgree (twC G) (twC H) ∧ MAgree (twB G) (twB H) ∧
    MAgree (twD G) (twD H) ∧ MAgree (vsplit G) (vsplit H) :=
  (C3 (A := A) n).2 G H h
-- (C4)
example (N : DPLattice A) (W : ℤ) (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (x y : Bf A)
    (h : Agree x y) (B : ℕ) : act N W B x = act N W B y := C4 htop h B
end C

section L
variable {A : Type} [CommRing A]
-- (L1)
example {n : Type} [LinearOrder n] [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twP (paySys p κ) = 1 ∧
    twD (paySys p κ) - twB (paySys p κ) * twC (paySys p κ) =
      (2 : A) • paySys (Payment.pT p) (Payment.κT p κ) ∧
    CleanStep (paySys p κ) (paySys (Payment.pT p) (Payment.κT p κ)) := L1 p κ
-- (L2), the second equality exact (more general than the file's agreement)
example {n : Type} [LinearOrder n] [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twP (vsplit (paySys p κ)) = 1 ∧
    MAgree (twD (vsplit (paySys p κ)) - twB (vsplit (paySys p κ)) * twC (vsplit (paySys p κ)))
      ((2 : A) • ((fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')) :
        Matrix (n × Fin 2) (n × Fin 2) (Bf A))) ∧
    CleanStep (vsplit (paySys p κ))
      (fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')) := L2 p κ
example {n : Type} [LinearOrder n] [Fintype n] (p : n → ℕ → A) (κ : n → n → ℕ → A) :
    twD (vsplit (paySys p κ)) - twB (vsplit (paySys p κ)) * twC (vsplit (paySys p κ)) =
      (2 : A) • ((fun q q' => paySys (pSp p) (κSp p κ) (toLex q) (toLex q')) :
        Matrix (n × Fin 2) (n × Fin 2) (Bf A)) := L2_schur_eq p κ
-- (L3)
example {n n' : Type} [LinearOrder n] [LinearOrder n'] (e : n ≃o n') (p' : n' → ℕ → A)
    (κ' : n' → n' → ℕ → A) :
    paySys (relabP e p') (relabK e κ') = fun s s' => paySys p' κ' (e s) (e s') := L3 e p' κ'
-- (L4)
example (ds : List Bool) (r : ℕ) (p : Fin r → ℕ → A) (κ : Fin r → Fin r → ℕ → A) :
    DanceRel ds r (paySys p κ) (paySys (danceAux ds r p κ).1 (danceAux ds r p κ).2) :=
  L4_dance ds r p κ
example (R : ℕ) (p' : Fin R → ℕ → A) (κ' : Fin R → Fin R → ℕ → A) :
    finalM (paySys p' κ') = Mfin p' κ' := finalM_paySys p' κ'
-- (L4), the corollary for σ
example (ds : List Bool) (α i : ℕ) :
    Clean ds 1 (paySys (pσ (A := A) α i) κσ) ∧
    ∃ Gk, DanceRel ds 1 (paySys (pσ (A := A) α i) κσ) Gk ∧
      ∀ t t' : Fin (1 * 2 ^ mCount ds),
        finalM Gk (Fin.cast (slots_eq ds 1).symm t) (Fin.cast (slots_eq ds 1).symm t') =
          Mfin (dance ds 1 (pσ (A := A) α i) κσ).1 (dance ds 1 (pσ α i) κσ).2 t t' :=
  L4_sigma_clean ds α i
-- (L5)
example (h2 : ∀ a : A, 2 * a = 0 → a = 0) (ds : List Bool) (r : ℕ)
    (G : Matrix (Fin r) (Fin r) (Bf A)) (Gk Gk' : Matrix (Fin (slots ds r)) (Fin (slots ds r)) (Bf A))
    (hk : DanceRel ds r G Gk) (hk' : DanceRel ds r G Gk') :
    MAgree Gk Gk' ∧ finalM Gk = finalM Gk' := L5 h2 hk hk'
-- (L6)
example (u : A) (hu : IsUnit u) (ds : List Bool) (r : ℕ) (G : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (slots ds r)) (Fin (slots ds r)) (Bf A)) (h : DanceRel ds r G Gk) :
    DanceRel ds r (u • G) (u • Gk) ∧ finalM (u • Gk) = u • finalM Gk := L6 hu h
end L

#print axioms FormalDance.C1
#print axioms FormalDance.C2
#print axioms FormalDance.C3
#print axioms FormalDance.C4
#print axioms FormalDance.L1
#print axioms FormalDance.L2
#print axioms FormalDance.L2_schur_eq
#print axioms FormalDance.L3
#print axioms FormalDance.L4
#print axioms FormalDance.L4_sigma
#print axioms FormalDance.L4_sigma_clean
#print axioms FormalDance.L5
#print axioms FormalDance.L6
