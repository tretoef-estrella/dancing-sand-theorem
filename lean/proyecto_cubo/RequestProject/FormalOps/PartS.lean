module

public import Mathlib

/-!
# `C40_the_formal_operators.md`: block operators (Definitions (new)) and Part S — the Schur step

Encodings (namespace `FormalOps`), for `A`-modules `L₁ L₂ K₁ K₂`, `P : L₁ ≃ₗ[A] K₁`,
`C : L₂ →ₗ[A] K₁`, `Bb : L₁ →ₗ[A] K₂`, `Dd : L₂ →ₗ[A] K₂`:

* `blockOp P C Bb Dd : L₁ × L₂ →ₗ[A] K₁ × K₂`, `(u, v) ↦ (P u + C v, Bb u + Dd v)` (`blockOp_apply`);
* `schur P C Bb Dd := Dd − Bb ∘ₗ P.symm ∘ₗ C`, exactly as in the file;
* the submodule `c • ⊤ : Submodule A K₁` is Mathlib's pointwise scalar multiple of the submodule
  `⊤` (the same submodule as `LinearMap.range (c • LinearMap.id)`, i.e. `c K₁`); we use the
  `c • ⊤` form;
* each "`≃ₗ[A]`" statement is given as an explicit linear equivalence (`S1equiv`, `S2equiv`,
  `S3equiv`) and as a `Nonempty` theorem (`S1`, `S2`, `S3`).
-/

@[expose] public section

noncomputable section

namespace FormalOps

open Pointwise

variable {A : Type*} [CommRing A] {L₁ L₂ K₁ K₂ : Type*} [AddCommGroup L₁] [Module A L₁]
  [AddCommGroup L₂] [Module A L₂] [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₂] [Module A K₂]

/-- Definitions (new) of `C40_the_formal_operators.md`, block operators:
`blockOp P C Bb Dd (u, v) = (P u + C v, Bb u + Dd v)`. -/
def blockOp (P : L₁ ≃ₗ[A] K₁) (C : L₂ →ₗ[A] K₁) (Bb : L₁ →ₗ[A] K₂) (Dd : L₂ →ₗ[A] K₂) :
    L₁ × L₂ →ₗ[A] K₁ × K₂ :=
  LinearMap.prod ((P : L₁ →ₗ[A] K₁) ∘ₗ LinearMap.fst A L₁ L₂ + C ∘ₗ LinearMap.snd A L₁ L₂)
    (Bb ∘ₗ LinearMap.fst A L₁ L₂ + Dd ∘ₗ LinearMap.snd A L₁ L₂)

/-- Definitions (new): `blockOp P C Bb Dd (u, v) = (P u + C v, Bb u + Dd v)`. -/
@[simp] lemma blockOp_apply (P : L₁ ≃ₗ[A] K₁) (C : L₂ →ₗ[A] K₁) (Bb : L₁ →ₗ[A] K₂)
    (Dd : L₂ →ₗ[A] K₂) (w : L₁ × L₂) :
    blockOp P C Bb Dd w = (P w.1 + C w.2, Bb w.1 + Dd w.2) := rfl

/-- Definitions (new) of `C40_the_formal_operators.md`, the Schur complement:
`schur P C Bb Dd := Dd − Bb ∘ₗ P.symm ∘ₗ C`. -/
def schur (P : L₁ ≃ₗ[A] K₁) (C : L₂ →ₗ[A] K₁) (Bb : L₁ →ₗ[A] K₂) (Dd : L₂ →ₗ[A] K₂) :
    L₂ →ₗ[A] K₂ :=
  Dd - Bb ∘ₗ (P.symm : K₁ →ₗ[A] L₁) ∘ₗ C

section S

variable (P : L₁ ≃ₗ[A] K₁) (C : L₂ →ₗ[A] K₁) (Bb : L₁ →ₗ[A] K₂) (Dd : L₂ →ₗ[A] K₂)

/-- Part S (auxiliary): the target operation `(k₁, k₂) ↦ (k₁, k₂ − Bb P⁻¹ k₁)`. -/
def tauS : K₁ × K₂ →ₗ[A] K₁ × K₂ :=
  LinearMap.prod (LinearMap.fst A K₁ K₂)
    (LinearMap.snd A K₁ K₂ - Bb ∘ₗ (P.symm : K₁ →ₗ[A] L₁) ∘ₗ LinearMap.fst A K₁ K₂)

lemma tauS_apply (k : K₁ × K₂) : tauS P Bb k = (k.1, k.2 - Bb (P.symm k.1)) := rfl

lemma tauS_injective : Function.Injective (tauS P Bb) := by
  intro k k' h
  simp only [tauS_apply, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact Prod.ext h1 (sub_left_injective h2)

/-- Part S (auxiliary): `τ (blockOp (u − P⁻¹ C v, v)) = (P u, schur v)`. -/
lemma tauS_blockOp (u : L₁) (v : L₂) :
    tauS P Bb (blockOp P C Bb Dd (u - P.symm (C v), v)) = (P u, schur P C Bb Dd v) := by
  simp only [tauS_apply, blockOp_apply, map_sub, LinearEquiv.apply_symm_apply,
    sub_add_cancel, LinearEquiv.symm_apply_apply, schur, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Prod.mk.injEq, true_and]
  abel

/-- Part S (auxiliary): the surjection `K₁ × K₂ → (K₁ ⧸ c K₁) × coker (c • schur)`. -/
def piS (c : A) : K₁ × K₂ →ₗ[A] (K₁ ⧸ (c • ⊤ : Submodule A K₁)) ×
    (K₂ ⧸ LinearMap.range (c • schur P C Bb Dd)) :=
  ((c • ⊤ : Submodule A K₁).mkQ.prodMap (LinearMap.range (c • schur P C Bb Dd)).mkQ) ∘ₗ
    tauS P Bb

lemma piS_surjective (c : A) : Function.Surjective (piS P C Bb Dd c) := by
  rintro ⟨q₁, q₂⟩
  obtain ⟨k₁, rfl⟩ := Submodule.mkQ_surjective _ q₁
  obtain ⟨k₂, rfl⟩ := Submodule.mkQ_surjective _ q₂
  refine ⟨(k₁, k₂ + Bb (P.symm k₁)), ?_⟩
  simp [piS, tauS_apply]

lemma ker_piS (c : A) :
    LinearMap.ker (piS P C Bb Dd c) = LinearMap.range (c • blockOp P C Bb Dd) := by
  ext k
  simp only [LinearMap.mem_ker, piS, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.prodMap_apply, Prod.mk_eq_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, LinearMap.smul_apply]
  constructor
  · rintro ⟨h1, ⟨v, hv⟩⟩
    obtain ⟨k₁', -, hk₁'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    refine ⟨(P.symm k₁' - P.symm (C v), v), tauS_injective P Bb ?_⟩
    rw [map_smul, tauS_blockOp, LinearEquiv.apply_symm_apply]
    exact Prod.ext hk₁' hv
  · rintro ⟨w, rfl⟩
    have hw : w = ((w.1 + P.symm (C w.2)) - P.symm (C w.2), w.2) := by simp
    rw [hw, map_smul, tauS_blockOp]
    refine ⟨(Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨_, Submodule.mem_top, rfl⟩,
      ⟨w.2, rfl⟩⟩

/-- **(S1)** of `C40_the_formal_operators.md`, the explicit equivalence:
`(K₁ × K₂) ⧸ range (c • blockOp P C Bb Dd) ≃ₗ[A]
(K₁ ⧸ (c • ⊤)) × (K₂ ⧸ range (c • schur P C Bb Dd))`; the class of `(k₁, k₂)` goes to
`([k₁], [k₂ − Bb P⁻¹ k₁])`. -/
def S1equiv (c : A) : ((K₁ × K₂) ⧸ LinearMap.range (c • blockOp P C Bb Dd)) ≃ₗ[A]
    (K₁ ⧸ (c • ⊤ : Submodule A K₁)) × (K₂ ⧸ LinearMap.range (c • schur P C Bb Dd)) :=
  (Submodule.quotEquivOfEq _ _ (ker_piS P C Bb Dd c).symm).trans
    ((piS P C Bb Dd c).quotKerEquivOfSurjective (piS_surjective P C Bb Dd c))

/-- **(S1)** of `C40_the_formal_operators.md`: for every `c : A`,
`(K₁ × K₂) ⧸ range (c • blockOp P C Bb Dd) ≃ₗ[A]
(K₁ ⧸ (c • ⊤ : Submodule A K₁)) × (K₂ ⧸ range (c • schur P C Bb Dd))`. -/
theorem S1 (c : A) : Nonempty (((K₁ × K₂) ⧸ LinearMap.range (c • blockOp P C Bb Dd)) ≃ₗ[A]
    (K₁ ⧸ (c • ⊤ : Submodule A K₁)) × (K₂ ⧸ LinearMap.range (c • schur P C Bb Dd))) :=
  ⟨S1equiv P C Bb Dd c⟩

/-- **(S2)** of `C40_the_formal_operators.md`, the explicit equivalence (the case `c = 1` of (S1)):
`(K₁ × K₂) ⧸ range (blockOp P C Bb Dd) ≃ₗ[A] K₂ ⧸ range (schur P C Bb Dd)`. -/
def S2equiv : ((K₁ × K₂) ⧸ LinearMap.range (blockOp P C Bb Dd)) ≃ₗ[A]
    (K₂ ⧸ LinearMap.range (schur P C Bb Dd)) :=
  haveI : Subsingleton (K₁ ⧸ ((1 : A) • ⊤ : Submodule A K₁)) := by
    rw [one_smul]; exact Submodule.Quotient.subsingleton_iff.2 rfl
  (Submodule.quotEquivOfEq _ _ (by rw [one_smul])).trans
    ((S1equiv P C Bb Dd 1).trans
      ((LinearEquiv.ofBijective (LinearMap.snd A _ _)
        ⟨fun a b h => Prod.ext (Subsingleton.elim _ _) h,
          fun b => ⟨(0, b), rfl⟩⟩).trans
        (Submodule.quotEquivOfEq _ _ (by rw [one_smul]))))

/-- **(S2)** of `C40_the_formal_operators.md`:
`(K₁ × K₂) ⧸ range (blockOp P C Bb Dd) ≃ₗ[A] K₂ ⧸ range (schur P C Bb Dd)`. -/
theorem S2 : Nonempty (((K₁ × K₂) ⧸ LinearMap.range (blockOp P C Bb Dd)) ≃ₗ[A]
    (K₂ ⧸ LinearMap.range (schur P C Bb Dd))) :=
  ⟨S2equiv P C Bb Dd⟩

/-- **(S3)** of `C40_the_formal_operators.md`, the explicit equivalence: if
`schur P C Bb Dd = (2 : A) • G'`, then for every `h : ℕ`,
`(K₁ × K₂) ⧸ range ((2 : A) ^ h • blockOp P C Bb Dd) ≃ₗ[A]
(K₁ ⧸ ((2 : A) ^ h • ⊤)) × (K₂ ⧸ range ((2 : A) ^ (h + 1) • G'))`. -/
def S3equiv (G' : L₂ →ₗ[A] K₂) (hG : schur P C Bb Dd = (2 : A) • G') (h : ℕ) :
    ((K₁ × K₂) ⧸ LinearMap.range ((2 : A) ^ h • blockOp P C Bb Dd)) ≃ₗ[A]
      (K₁ ⧸ ((2 : A) ^ h • ⊤ : Submodule A K₁)) ×
        (K₂ ⧸ LinearMap.range ((2 : A) ^ (h + 1) • G')) :=
  (S1equiv P C Bb Dd ((2 : A) ^ h)).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl A _)
      (Submodule.quotEquivOfEq _ _ (by rw [hG, smul_smul, ← pow_succ])))

/-- **(S3)** of `C40_the_formal_operators.md`: if `schur P C Bb Dd = (2 : A) • G'` for some
`G' : L₂ →ₗ[A] K₂`, then for every `h : ℕ`,
`(K₁ × K₂) ⧸ range ((2 : A) ^ h • blockOp P C Bb Dd) ≃ₗ[A]
(K₁ ⧸ ((2 : A) ^ h • ⊤ : Submodule A K₁)) × (K₂ ⧸ range ((2 : A) ^ (h + 1) • G'))`. -/
theorem S3 (G' : L₂ →ₗ[A] K₂) (hG : schur P C Bb Dd = (2 : A) • G') (h : ℕ) :
    Nonempty (((K₁ × K₂) ⧸ LinearMap.range ((2 : A) ^ h • blockOp P C Bb Dd)) ≃ₗ[A]
      (K₁ ⧸ ((2 : A) ^ h • ⊤ : Submodule A K₁)) ×
        (K₂ ⧸ LinearMap.range ((2 : A) ^ (h + 1) • G'))) :=
  ⟨S3equiv P C Bb Dd G' hG h⟩

end S

end FormalOps
