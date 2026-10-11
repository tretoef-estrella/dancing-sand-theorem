module

public import RequestProject.FormalAct.All
public import RequestProject.FormalDance.All
public import RequestProject.Dance.D2
public import RequestProject.Families.Digits
public import RequestProject.BaiCounts.Counts

/-!
# `C40d_proposition_10_7.md`: auxiliary linear equivalences

General linear-algebra helpers for the proof of Proposition 10.7 (no new mathematical object is
defined; C13's `Dance.PQ`, `Dance.pqCast`, `Dance.funFinEquiv`, `Dance.quotSmulTopCongr` are
reused):

* `curryEquiv`: `(n × X → A) ≃ₗ (n → X → A)`;
* `sysQuotPQ`: `(n → X → A) ⧸ c·⊤ ≃ₗ (Fin a → A) ⧸ c·⊤` when `|n × X| = a`;
* `cokerReindex`: cokernels of `c • M` and of `c • M'` agree if `M'` is `M` read along `e`;
* `cokerUnitMul`: cokernels of `c • M` and `c • (P * M * Q)` agree for `P`, `Q` of unit
  determinant;
* `pqZeroProd`: the factor `M ⧸ 2^0·⊤ = 0` can be dropped from a product.
-/

@[expose] public section

noncomputable section

namespace FormalProp

open Pointwise

variable {A : Type*} [CommRing A]

/-- Auxiliary (`C40d_proposition_10_7.md`, flattening of the clocks): currying,
`(n × X → A) ≃ₗ[A] (n → X → A)`. -/
def curryEquiv (n X : Type*) : (n × X → A) ≃ₗ[A] (n → X → A) where
  toFun f s i := f (s, i)
  invFun g p := g p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Auxiliary (`C40d_proposition_10_7.md`, flattening of the clocks): a clock
`(n → X → A) ⧸ c·⊤` with `|n × X| = a` is `(Fin a → A) ⧸ c·⊤`. -/
def sysQuotPQ {n X : Type*} [Fintype n] [Fintype X] {a : ℕ} (ha : Fintype.card (n × X) = a)
    (c : A) :
    ((n → X → A) ⧸ c • (⊤ : Submodule A (n → X → A))) ≃ₗ[A]
      ((Fin a → A) ⧸ c • (⊤ : Submodule A (Fin a → A))) :=
  Dance.quotSmulTopCongr ((curryEquiv n X).symm.trans (Dance.funFinEquiv _ ha)) c

/-- Auxiliary (`C40d_proposition_10_7.md`, (Q4)): if `M' t t' = M (e t) (e t')`, the cokernels of
`c • M` and `c • M'` are isomorphic. -/
def cokerReindex {m m' : Type*} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m']
    (e : m' ≃ m) (M : Matrix m m A) (M' : Matrix m' m' A)
    (hM : ∀ t t', M (e t) (e t') = M' t t') (c : A) :
    ((m → A) ⧸ LinearMap.range (c • Matrix.mulVecLin M)) ≃ₗ[A]
      ((m' → A) ⧸ LinearMap.range (c • Matrix.mulVecLin M')) :=
  FormalAct.quotEquivConj (LinearEquiv.funCongrLeft A A e) (LinearEquiv.funCongrLeft A A e) _ _ (by
    refine LinearMap.ext fun v => funext fun t => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.smul_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    congr 1
    rw [← Fintype.sum_equiv e (fun t' => M (e t) (e t') * v (e t')) (fun x => M (e t) x * v x)
      (fun _ => rfl)]
    simp only [hM])

/-- Auxiliary (`C40d_proposition_10_7.md`, (Q3)): for `P`, `Q` with unit determinant, the
cokernels of `c • M` and of `c • (P * M * Q)` are isomorphic. -/
def cokerUnitMul {m : Type*} [Fintype m] [DecidableEq m] (M P Q : Matrix m m A)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (c : A) :
    ((m → A) ⧸ LinearMap.range (c • Matrix.mulVecLin M)) ≃ₗ[A]
      ((m → A) ⧸ LinearMap.range (c • Matrix.mulVecLin (P * M * Q))) :=
  FormalAct.quotEquivConj (Matrix.toLinearEquiv' Q (Matrix.invertibleOfIsUnitDet Q hQ)).symm
    (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP)) _ _ (by
    refine LinearMap.ext fun v => ?_
    have hv : Matrix.toLin' Q
        ((Matrix.toLinearEquiv' Q (Matrix.invertibleOfIsUnitDet Q hQ)).symm v) = v := by
      rw [← Matrix.toLinearEquiv'_apply Q (Matrix.invertibleOfIsUnitDet Q hQ)]
      exact LinearEquiv.apply_symm_apply _ v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_smul] at hv ⊢
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_mulVec])

/-- Auxiliary (`C40d_proposition_10_7.md`, (Q2)): `X ⧸ 2^0·⊤` is the zero module, so it can be
dropped from a product. -/
def pqZeroProd (X Y : Type*) [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y] :
    ((X ⧸ (2 : A) ^ 0 • (⊤ : Submodule A X)) × Y) ≃ₗ[A] Y :=
  haveI : Subsingleton (X ⧸ (2 : A) ^ 0 • (⊤ : Submodule A X)) := by
    rw [pow_zero, one_smul]
    exact Submodule.Quotient.subsingleton_iff.2 rfl
  LinearEquiv.ofLinear (LinearMap.snd A _ _) (LinearMap.inr A _ _) rfl
    (LinearMap.ext fun x => Prod.ext (Subsingleton.elim _ _) rfl)

end FormalProp
