module

public import RequestProject.Conjugation.Defs
public import RequestProject.PathSum.Aux

/-!
# `C45_conjugation_and_general_eta.md`: Part D — agreement and the dance; invertibility

* (D0) `D0`: the dance only depends on the starting system up to agreement.
* (I) `I`: over a field, an operator whose coefficient `0` is non-zero at every floor `f ≥ 0`
  has a two-sided inverse up to agreement. The right inverse is `rinv` (the recursion of C43
  (P0)), the left inverse is `linv` (the mirror recursion); they agree.
-/

@[expose] public section

noncomputable section

namespace Conjugation

open FormalOps FormalDance Finset

variable {A : Type*} [CommRing A]

lemma cleanStep_of_magree {n : Type*} [Fintype n] [DecidableEq n]
    {G G' G1 : Matrix n n (Bf A)} (h : CleanStep G G1) (hGG : MAgree G G') : CleanStep G' G1 := by
  obtain ⟨Q, hPQ, hQP, hS⟩ := h
  have h' := hGG.symm
  exact ⟨Q, (h'.twP.mul (MAgree.refl Q)).trans hPQ, ((MAgree.refl Q).mul h'.twP).trans hQP,
    (h'.twD.sub ((h'.twB.mul (MAgree.refl Q)).mul h'.twC)).trans hS⟩

/-- **(D0)** of `C45_conjugation_and_general_eta.md`:
`DanceRel ds r G Gk → MAgree G G' → DanceRel ds r G' Gk`. -/
theorem D0 (ds : List Bool) : ∀ (r : ℕ) (G G' : Matrix (Fin r) (Fin r) (Bf A))
    (Gk : Matrix (Fin (Dance.slots ds r)) (Fin (Dance.slots ds r)) (Bf A)),
    DanceRel ds r G Gk → MAgree G G' → DanceRel ds r G' Gk := by
  induction ds with
  | nil => intro r G G' Gk h hGG; exact hGG.symm.trans h
  | cons d rest ih =>
    cases d
    · rintro r G G' Gk ⟨G1, hc, hd⟩ hGG
      exact ⟨G1, cleanStep_of_magree hc hGG, hd⟩
    · rintro r G G' Gk ⟨G1, hc, hd⟩ hGG
      exact ⟨G1, cleanStep_of_magree hc hGG.vsplit, hd⟩

/-! ### (I) -/

section Inv

variable {K : Type*} [Field K]

/-- (I) of `C45_conjugation_and_general_eta.md`: the right inverse, by the recursion
`Y_L(f) = ([L = 0] − Σ_{a ≥ 1} C(L, a) x_a(f) Y_{L−a}(f − a)) / x_0(f)`. -/
def rinv (x : Bf K) : ℕ → ℤ → K
  | L, f => ((if L = 0 then 1 else 0) - ∑ a : Fin L, (L.choose (a + 1) : K) * x.coef (a + 1) f *
      rinv x (L - (a + 1)) (f - ((a + 1 : ℕ) : ℤ))) / x.coef 0 f
termination_by L => L
decreasing_by have := a.2; omega

/-- (I) of `C45_conjugation_and_general_eta.md`: the left inverse, by the mirror recursion
`Z_L(f) = ([L = 0] − Σ_{a < L} C(L, a) Z_a(f) x_{L−a}(f − a)) / x_0(f − L)`. -/
def linv (x : Bf K) : ℕ → ℤ → K
  | L, f => ((if L = 0 then 1 else 0) - ∑ a : Fin L, (L.choose a : K) * linv x a f *
      x.coef (L - a) (f - (a : ℕ))) / x.coef 0 (f - L)
termination_by L => L
decreasing_by exact a.2

lemma agree_rinv (x : Bf K) (hx : ∀ f : ℤ, 0 ≤ f → x.coef 0 f ≠ 0) :
    Agree (x * ⟨rinv x⟩) 1 := by
  intro L f hf
  rw [PathSum.coef_mul_split, Bf.coef_one]
  have h0 := hx f (by omega)
  show x.coef 0 f * rinv x L f + _ = _
  rw [rinv, Finset.sum_range (fun a => (L.choose (a + 1) : K) * x.coef (a + 1) f *
    rinv x (L - (a + 1)) (f - ((a + 1 : ℕ) : ℤ)))]
  field_simp
  ring

lemma agree_linv (x : Bf K) (hx : ∀ f : ℤ, 0 ≤ f → x.coef 0 f ≠ 0) :
    Agree (⟨linv x⟩ * x) 1 := by
  intro L f hf
  rw [Bf.coef_mul, Finset.sum_range_succ, Bf.coef_one]
  have h0 := hx (f - L) (by omega)
  show _ + (L.choose L : K) * linv x L f * x.coef (L - L) (f - L) = _
  have e : linv x L f = ((if L = 0 then 1 else 0) - ∑ a : Fin L, (L.choose a : K) * linv x a f *
      x.coef (L - a) (f - (a : ℕ))) / x.coef 0 (f - L) := by rw [linv]
  rw [e, Finset.sum_range (fun a => (L.choose a : K) * linv x a f *
    x.coef (L - a) (f - (a : ℕ)))]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
  field_simp
  ring

/-- **(I)** of `C45_conjugation_and_general_eta.md` (invertibility): over a field `K`, if
`x.coef 0 f ≠ 0` for every `f ≥ 0`, there is `Y : Bf K` with `Agree (x * Y) 1` and
`Agree (Y * x) 1`. -/
theorem I (x : Bf K) (hx : ∀ f : ℤ, 0 ≤ f → x.coef 0 f ≠ 0) :
    ∃ Y : Bf K, Agree (x * Y) 1 ∧ Agree (Y * x) 1 := by
  set Y : Bf K := ⟨rinv x⟩
  set Z : Bf K := ⟨linv x⟩
  have hR := agree_rinv x hx
  have hL := agree_linv x hx
  have hZY : Agree Z Y := by
    have e1 : Agree Z (Z * (x * Y)) := by
      have := (Agree.refl Z).mul hR.symm
      rwa [mul_one] at this
    have e2 : Agree (Z * x * Y) Y := by
      have := hL.mul (Agree.refl Y)
      rwa [one_mul] at this
    rw [← mul_assoc] at e1
    exact e1.trans e2
  exact ⟨Y, hR, (hZY.symm.mul (Agree.refl x)).trans hL⟩

end Inv

end Conjugation
