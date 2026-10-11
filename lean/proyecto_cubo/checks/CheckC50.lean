import RequestProject.GlueDance.All

/-! Auditor's check file for Lean piece C50: the glue commutes with the dance (Lemma 10.19)
(Grepy Escribano, 10 Oct 2026). Restated by hand from `C50_the_glue_commutes_with_the_dance.md`;
then `#print axioms`. -/

open FormalOps FormalDance ContZero GlueDance

-- the new definitions, by `rfl`
example {n : Type*} (X Y Z : Matrix n n (Bf ℤ_[2])) :
    glueM X Y Z = fun p p' => if p.1 = 0 ∧ p'.1 = 0 then X p.2 p'.2
      else if p.1 = 1 ∧ p'.1 = 0 then Z p.2 p'.2
      else if p.1 = 1 ∧ p'.1 = 1 then Y p.2 p'.2 else 0 := rfl
example {r r₂ : ℕ} (h : r₂ = 2 * r) :
    gE h = finProdFinEquiv.trans (finCongr h.symm) := rfl
example {r r₂ : ℕ} (h : r₂ = 2 * r) (X Y Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) :
    glueC h X Y Z = fun j j' => glueM X Y Z ((gE h).symm j) ((gE h).symm j') := rfl
example {r : ℕ} (M : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])) :
    relab M = fun j j' => M (ofLex ((Dance.splitIso r).symm j))
      (ofLex ((Dance.splitIso r).symm j')) := rfl
-- the top digit: (g, s) ↦ s + r g
example {r r₂ : ℕ} (h : r₂ = 2 * r) (g : Fin 2) (s : Fin r) :
    ((gE h (g, s) : Fin r₂) : ℕ) = s + r * g := by
  simp [gE, finProdFinEquiv]
-- PairRel at [] and its two steps
example {r : ℕ} (X Y Xk Yk : Matrix (Fin r) (Fin r) (Bf ℤ_[2])) :
    PairRel [] r X Y Xk Yk = (MCong 1 Y X ∧ MAgree X Xk ∧ MAgree Y Yk) := rfl
example (rest : List Bool) {r : ℕ} (X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (Xk Yk : Matrix (Fin (Dance.slots (false :: rest) r)) (Fin (Dance.slots (false :: rest) r))
      (Bf ℤ_[2])) :
    PairRel (false :: rest) r X Y Xk Yk = (MCong 1 Y X ∧ ∃ X' Y', CleanStep X X' ∧
      CleanStep Y Y' ∧ PairRel rest r X' Y' Xk Yk) := rfl

-- (B1)
example {n : Type*} [Fintype n] [DecidableEq n] (X Y Z X' Y' Z' : Matrix n n (Bf ℤ_[2])) :
    glueM X Y Z * glueM X' Y' Z' = glueM (X * X') (Y * Y') (Z * X' + Y * Z') ∧
    glueM (1 : Matrix n n (Bf ℤ_[2])) 1 0 = 1 :=
  ⟨(B1 X Y Z X' Y' Z').1, (B1 X Y Z X' Y' Z').2.1⟩
-- (B4)
example {n : Type*} {G H : Matrix n n (Bf ℤ_[2])}
    (h : MAgree ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H)) : MAgree G H := B4 h
-- (G2)
example {n : Type*} [Fintype n] [DecidableEq n] {X Y Z X' Y' W : Matrix n n (Bf ℤ_[2])}
    (hX : CleanStep X X') (hY : CleanStep Y Y') (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z))
    (hW : MAgree (Y' - X') ((2 : ℤ_[2]) • W)) :
    CleanStep (glueM X Y Z) (glueM X' Y' W) := G2 hX hY hZ hW
-- (S3)
example {r r₂ : ℕ} (h : r₂ = 2 * r) (h2 : r₂ * 2 = 2 * (r * 2))
    (X'' Y'' W'' : Matrix (Fin r × Fin 2) (Fin r × Fin 2) (Bf ℤ_[2])) :
    relab (fun q q' => glueM X'' Y'' W'' (τ h q) (τ h q')) =
      glueC h2 (relab X'') (relab Y'') (relab W'') := S3 h h2 X'' Y'' W''
-- (D1)
example (ds : List Bool) {r : ℕ} {X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    {Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])}
    (h : PairRel ds r X Y Xk Yk) :
    DanceRel ds r X Xk ∧ DanceRel ds r Y Yk ∧ MCong 1 Yk Xk := D1 ds h
-- (D2) Lemma 10.19
example (ds : List Bool) {r r₂ : ℕ} (h : r₂ = 2 * r) {X Y : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    {Xk Yk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf ℤ_[2])}
    (hP : PairRel ds r X Y Xk Yk) (Z : Matrix (Fin r) (Fin r) (Bf ℤ_[2]))
    (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z)) :
    ∃ Zk, MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk) ∧
      DanceRel ds r₂ (glueC h X Y Z) (glueC (S4 ds h) Xk Yk Zk) := D2 ds h hP Z hZ
-- (D3)
example {r r₂ : ℕ} (h : r₂ = 2 * r) {Xk Yk Zk : Matrix (Fin r) (Fin r) (Bf ℤ_[2])}
    (hZ : MAgree (Yk - Xk) ((2 : ℤ_[2]) • Zk)) (g g' : Fin 2) (s s' : Fin r) :
    finalM (glueC h Xk Yk Zk) (gE h (g, s)) (gE h (g', s')) =
      (if g = 0 ∧ g' = 0 then finalM Xk s s' else if g = 1 ∧ g' = 0 then finalM Zk s s'
        else if g = 1 ∧ g' = 1 then finalM Yk s s' else 0) ∧
    2 * finalM Zk s s' = finalM Yk s s' - finalM Xk s s' := D3 h hZ g g' s s'

#print axioms GlueDance.B1
#print axioms GlueDance.B2
#print axioms GlueDance.B3
#print axioms GlueDance.B4
#print axioms GlueDance.G2
#print axioms GlueDance.S1
#print axioms GlueDance.S2
#print axioms GlueDance.S3
#print axioms GlueDance.S4
#print axioms GlueDance.D1
#print axioms GlueDance.D2
#print axioms GlueDance.D3
