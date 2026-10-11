module

public import RequestProject.FormalProp.All

/-!
# `C41_inverse_block.md`: Definitions (new) — `inH` and `outH`

Encodings (namespace `InvBlock`), reusing C13 `Dance.slots`, `Dance.splitIso`; C18 `DPLattice`,
`DPLattice.one`; C29 `Filt.T` (`T_zero`, and its defining equation); C32 `Families.ds`
(`ds_zero`, and its defining equation); C40c `FormalAct.sysAct`, `pack`, `vpack`, `unitEquiv`;
C40d `FormalProp.splitEquiv` (the relabelling `j ↦ ofLex ((Dance.splitIso r).symm j)`).

* A vector of `N^{⊕n}` is a function `n → N.ι → A` (as in C40c); a vector of `A^{ns}` is a
  function `Fin ns → A`.
* `inj₀ x = pack (x, 0)` is `inj0`, `out₁ w = (pack.symm w).2` is `out1`.
* `inH l r` and `outH l r` are defined by well-founded recursion on `l`, following the defining
  equations of `Filt.T` and `Families.ds` (`l = 0`; `l = n + 1` with `n` even, i.e. `l = 2l' + 1`,
  a twist step; `l = n + 1` with `n` odd, i.e. `l = 2l' + 2`, a split step; `l' = n / 2`):
  - `l = 0`: the identity through `unitEquiv`;
  - twist step: `inH = inj₀ ∘ inH'`, `outH = outH' ∘ out₁`;
  - split step: `inH = vpack ∘ inj₀ ∘ (relabel)⁻¹ ∘ inH'`, `outH = outH' ∘ relabel ∘ out₁ ∘ vpack⁻¹`,
    with `relabel = LinearEquiv.funCongrLeft` along `FormalProp.splitEquiv r` (C40c (A3)).
  The equalities of types `T A (n+1) = phi (T A (n/2))` etc. are transported by `castLat`
  (a linear equivalence along an equality of lattices), and `Dance.slots (Families.ds (n+1)) r =
  Dance.slots (Families.ds (n/2)) r` etc. by `ri` (reindexing along `Fin.cast`).
  **They depend only on `l` and `r`, never on a system.**
-/

@[expose] public section

noncomputable section

namespace InvBlock

open DPLattice Doubling Filt FormalOps FormalDance FormalAct

variable {A : Type*} [CommRing A]

/-! ### Auxiliary transports -/

/-- Auxiliary (`C41_inverse_block.md`, Definitions): reindexing `Fin a → A` along `a = b`. -/
def ri {a b : ℕ} (h : a = b) : (Fin a → A) →ₗ[A] (Fin b → A) :=
  LinearMap.funLeft A A (Fin.cast h.symm)

/-- Auxiliary (`C41_inverse_block.md`, Definitions): the formula of `ri`. -/
@[simp] lemma ri_apply {a b : ℕ} (h : a = b) (x : Fin a → A) (i : Fin b) :
    ri h x i = x (Fin.cast h.symm i) := rfl

/-- Auxiliary (`C41_inverse_block.md`, Definitions): two reindexings compose to one. -/
lemma ri_ri {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : Fin a → A) :
    ri h₂ (ri h₁ x) = ri (h₁.trans h₂) x := rfl

/-- Auxiliary (`C41_inverse_block.md`, Definitions): a reindexing along `a = a` is the identity. -/
@[simp] lemma ri_self {a : ℕ} (h : a = a) (x : Fin a → A) : ri h x = x := rfl

/-- Auxiliary (`C41_inverse_block.md`, Definitions): transport of `n → N.ι → A` along an equality
of lattices `N = N'`. -/
def castLat {N N' : DPLattice A} (h : N = N') (n : Type*) :
    (n → N.ι → A) ≃ₗ[A] (n → N'.ι → A) :=
  Eq.rec (motive := fun N' _ => (n → N.ι → A) ≃ₗ[A] (n → N'.ι → A)) (LinearEquiv.refl A _) h

/-- Auxiliary (`C41_inverse_block.md`, Definitions): `castLat⁻¹ ∘ castLat = id`. -/
@[simp] lemma castLat_symm_apply {N N' : DPLattice A} (h : N = N') {n : Type*}
    (x : n → N.ι → A) : (castLat h n).symm (castLat h n x) = x := by
  subst h; rfl

/-- Auxiliary (`C41_inverse_block.md`, Definitions): `castLat ∘ castLat⁻¹ = id`. -/
@[simp] lemma castLat_apply_symm {N N' : DPLattice A} (h : N = N') {n : Type*}
    (x : n → N'.ι → A) : castLat h n ((castLat h n).symm x) = x := by
  subst h; rfl

/-- Auxiliary (`C41_inverse_block.md`, (V3)): the action of a system commutes with `castLat`. -/
lemma sysAct_castLat {N N' : DPLattice A} (h : N = N') {n : Type*} [Fintype n] (W : ℤ) (B : ℕ)
    (G : Matrix n n (Bf A)) (x : n → N.ι → A) :
    sysAct N' W B G (castLat h n x) = castLat h n (sysAct N W B G x) := by
  subst h; rfl

/-- Definitions (new) of `C41_inverse_block.md`: `inj₀ x = pack (x, 0)`. -/
def inj0 {n ι : Type*} : (n → ι → A) →ₗ[A] (n → Fin 2 × ι → A) :=
  (pack : _ ≃ₗ[A] (n → Fin 2 × ι → A)).toLinearMap ∘ₗ LinearMap.inl A _ _

/-- Definitions (new) of `C41_inverse_block.md`: the formula of `inj₀`. -/
@[simp] lemma inj0_apply {n ι : Type*} (x : n → ι → A) : inj0 x = pack (x, 0) := rfl

/-- Auxiliary (`C41_inverse_block.md`, (V3)): `pack (c • x, 0) = c • pack (x, 0)`. -/
lemma pack_smul_zero {n ι : Type*} (c : A) (x : n → ι → A) :
    (pack (c • x, 0) : n → Fin 2 × ι → A) = c • pack (x, 0) := by
  rw [← map_smul, Prod.smul_mk, smul_zero]

/-- Definitions (new) of `C41_inverse_block.md`: `out₁ w = (pack.symm w).2`. -/
def out1 {n ι : Type*} : (n → Fin 2 × ι → A) →ₗ[A] (n → ι → A) :=
  LinearMap.snd A _ _ ∘ₗ (pack : _ ≃ₗ[A] (n → Fin 2 × ι → A)).symm.toLinearMap

/-- Definitions (new) of `C41_inverse_block.md`: the formula of `out₁`. -/
@[simp] lemma out1_apply {n ι : Type*} (w : n → Fin 2 × ι → A) :
    out1 w = (pack.symm w).2 := rfl

/-! ### The defining equations of `T` and `ds` at `n + 1` -/

section eqns

variable [IsDomain A] [CharZero A] [OddUnits A]

variable (A) in
/-- Auxiliary (`C41_inverse_block.md`, Definitions): `T A (n + 1) = phi (T A (n / 2))` for `n` even (C29). -/
lemma T_succ_pos {n : ℕ} (h : n % 2 = 0) : T A (n + 1) = phi (T A (n / 2)) := by
  rw [T, if_pos h]

variable (A) in
/-- Auxiliary (`C41_inverse_block.md`, Definitions): `T A (n + 1) = tensorV (phi (T A (n / 2)))` for `n` odd (C29). -/
lemma T_succ_neg {n : ℕ} (h : ¬ n % 2 = 0) : T A (n + 1) = tensorV (phi (T A (n / 2))) := by
  rw [T, if_neg h]

end eqns

/-- Auxiliary (`C41_inverse_block.md`, Definitions): `ds (n + 1) = false :: ds (n / 2)` for `n` even (C32). -/
lemma ds_succ_pos {n : ℕ} (h : n % 2 = 0) : Families.ds (n + 1) = false :: Families.ds (n / 2) := by
  rw [Families.ds, if_pos h]

/-- Auxiliary (`C41_inverse_block.md`, Definitions): `ds (n + 1) = true :: ds (n / 2)` for `n` odd (C32). -/
lemma ds_succ_neg {n : ℕ} (h : ¬ n % 2 = 0) : Families.ds (n + 1) = true :: Families.ds (n / 2) := by
  rw [Families.ds, if_neg h]

/-- Auxiliary (`C41_inverse_block.md`, Definitions): the slot count at `l = 0`. -/
lemma slots_zero (r : ℕ) : Dance.slots (Families.ds 0) r = r := by
  rw [Families.ds_zero]; rfl

/-- Auxiliary (`C41_inverse_block.md`, Definitions): the slot count at a twist step. -/
lemma slots_succ_pos {n : ℕ} (h : n % 2 = 0) (r : ℕ) :
    Dance.slots (Families.ds (n + 1)) r = Dance.slots (Families.ds (n / 2)) r := by
  rw [ds_succ_pos h]; rfl

/-- Auxiliary (`C41_inverse_block.md`, Definitions): the slot count at a split step. -/
lemma slots_succ_neg {n : ℕ} (h : ¬ n % 2 = 0) (r : ℕ) :
    Dance.slots (Families.ds (n + 1)) r = Dance.slots (Families.ds (n / 2)) (r * 2) := by
  rw [ds_succ_neg h]; rfl

/-! ### `inH` and `outH` -/

/-- Auxiliary (`C41_inverse_block.md`, Definitions): the relabelling of C40c (A3) along `FormalProp.splitEquiv r`,
`(Fin r × Fin 2 → X) ≃ₗ (Fin (r * 2) → X)`, `v ↦ v ∘ splitEquiv r`. -/
abbrev relab (r : ℕ) (X : Type*) [AddCommGroup X] [Module A X] :
    (Fin r × Fin 2 → X) ≃ₗ[A] (Fin (r * 2) → X) :=
  LinearEquiv.funCongrLeft A X (FormalProp.splitEquiv r)

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- **Definitions (new)** of `C41_inverse_block.md`: the coordinate map
`inH l r : (Fin (Dance.slots (Families.ds l) r) → A) →ₗ[A] (Fin r → (T A l).ι → A)`, by recursion
along `l`: at `l = 0` the identity through `unitEquiv`; at a twist step `inH = inj₀ ∘ inH'`; at a
split step `inH = vpack ∘ inj₀ ∘ (relabel)⁻¹ ∘ inH'`. It depends only on `l` and `r`. -/
def inH : (l r : ℕ) →
    (Fin (Dance.slots (Families.ds l) r) → A) →ₗ[A] (Fin r → (T A l).ι → A)
  | 0, r =>
      (castLat (T_zero (A := A)).symm (Fin r)).toLinearMap ∘ₗ
        (unitEquiv : (Fin r → Unit → A) ≃ₗ[A] (Fin r → A)).symm.toLinearMap ∘ₗ ri (slots_zero r)
  | n + 1, r =>
      if h : n % 2 = 0 then
        (castLat (T_succ_pos A h).symm (Fin r)).toLinearMap ∘ₗ inj0 ∘ₗ inH (n / 2) r ∘ₗ
          ri (slots_succ_pos h r)
      else
        (castLat (T_succ_neg A h).symm (Fin r)).toLinearMap ∘ₗ
          (vpack : (Fin r × Fin 2 → (phi (T A (n / 2))).ι → A) ≃ₗ[A] _).toLinearMap ∘ₗ inj0 ∘ₗ
          (relab r ((T A (n / 2)).ι → A)).symm.toLinearMap ∘ₗ inH (n / 2) (r * 2) ∘ₗ
          ri (slots_succ_neg h r)
decreasing_by all_goals omega

/-- **Definitions (new)** of `C41_inverse_block.md`: the source map
`outH l r : (Fin r → (T A l).ι → A) →ₗ[A] (Fin (Dance.slots (Families.ds l) r) → A)`, by recursion
along `l`: at `l = 0` the identity through `unitEquiv`; at a twist step `outH = outH' ∘ out₁`; at a
split step `outH = outH' ∘ relabel ∘ out₁ ∘ vpack⁻¹`. It depends only on `l` and `r`. -/
def outH : (l r : ℕ) →
    (Fin r → (T A l).ι → A) →ₗ[A] (Fin (Dance.slots (Families.ds l) r) → A)
  | 0, r =>
      ri (slots_zero r).symm ∘ₗ (unitEquiv : (Fin r → Unit → A) ≃ₗ[A] (Fin r → A)).toLinearMap ∘ₗ
        (castLat (T_zero (A := A)).symm (Fin r)).symm.toLinearMap
  | n + 1, r =>
      if h : n % 2 = 0 then
        ri (slots_succ_pos h r).symm ∘ₗ outH (n / 2) r ∘ₗ out1 ∘ₗ
          (castLat (T_succ_pos A h).symm (Fin r)).symm.toLinearMap
      else
        ri (slots_succ_neg h r).symm ∘ₗ outH (n / 2) (r * 2) ∘ₗ
          (relab r ((T A (n / 2)).ι → A)).toLinearMap ∘ₗ out1 ∘ₗ
          (vpack : (Fin r × Fin 2 → (phi (T A (n / 2))).ι → A) ≃ₗ[A] _).symm.toLinearMap ∘ₗ
          (castLat (T_succ_neg A h).symm (Fin r)).symm.toLinearMap
decreasing_by all_goals omega

end InvBlock
