module

public import RequestProject.Mirror.Exps

/-!
# `C37_the_mirror_that_doubles.md`: Part Y — Corollary 1.7 (group form)

Namespace `Mirror`.  C17's `CubeLaplacian.K`, `Syl2`; C16's `FamilyGroup.SC`, `Q`, `yPool`,
`yPool0`; C33's `MainTheorem.XFam`, `M2equiv`, `S4equiv`, `castQ` are used directly.

## Encodings

* `S n` of the file is written out as `CubeLaplacian.Syl2 (CubeLaplacian.K n)` (an additive
  subgroup, viewed as an additive commutative group); `≅` is `≃+`, and an isomorphism statement is
  `Nonempty (… ≃+ …)`.
* The family-level isomorphisms are `ℤ_[2]`-linear equivalences (`≃ₗ[ℤ_[2]]`), turned into additive
  equivalences at the end.

## Proof outline (as suggested in the file)

By C33 (M2) both `ℤ_2 × S (2^e)` and `ℤ_2 × S (2^e − 1)` are products over the families.  By (A1)
the families of `2^e` are the `λ + 1`, `λ ∈ L (2^e − 1)`.  For odd `λ < 2^e − 1` (shift `i ≥ 1`),
`XFam (λ + 1) i ≃ XFam λ i × XFam λ i` (`famDouble`: C33 (S4) with (A2) for the small clocks, (X1)
for the big clocks).  The top family gives `XFam (2^e) 0 × ℤ_2 ≃ (XFam (2^e − 1) 0)^2 × Q (2^e + e − 1)`
(`famTop`).  This yields `(ℤ_2 × ℤ_2) × S (2^e) ≃ (ℤ_2 × ℤ_2) × ((S N × S N) × Q (2^e + e − 1))`;
the factor `ℤ_2 × ℤ_2` is cancelled through the `2`-power torsion (`cancel_torsion`), and
`Q a ≃ ZMod (2^a)` through `PadicInt.toZModPow` (`QequivZMod`).
-/

@[expose] public section

namespace Mirror

open Families MainTheorem

/-! ### Generic equivalences -/

/-- `Π_i (B i × C i) ≃ (Π_i B i) × (Π_i C i)` (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
def piProdEquiv {R ι : Type*} [Semiring R] (B C : ι → Type*) [∀ i, AddCommMonoid (B i)]
    [∀ i, AddCommMonoid (C i)] [∀ i, Module R (B i)] [∀ i, Module R (C i)] :
    ((i : ι) → B i × C i) ≃ₗ[R] ((i : ι) → B i) × ((i : ι) → C i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun g i := (g.1 i, g.2 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Equiv.piSplitAt` as a linear equivalence (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
def piSplitAtL {R ι : Type*} [Semiring R] [DecidableEq ι] (i : ι) (B : ι → Type*)
    [∀ i, AddCommMonoid (B i)] [∀ i, Module R (B i)] :
    ((j : ι) → B j) ≃ₗ[R] B i × ((j : {j // j ≠ i}) → B j) :=
  { Equiv.piSplitAt i B with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- `(A × B) × C ≃ (A × C) × B` (auxiliary for Part Y of `C37_the_mirror_that_doubles.md`). -/
def swapRight (A B C : Type*) [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] :
    (A × B) × C ≃+ (A × C) × B where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `((A × S) × (A' × S')) × Q ≃ (A × A') × ((S × S') × Q)` (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
def regroup (A S A' S' Q : Type*) [AddCommGroup A] [AddCommGroup S] [AddCommGroup A']
    [AddCommGroup S'] [AddCommGroup Q] :
    ((A × S) × (A' × S')) × Q ≃+ (A × A') × ((S × S') × Q) where
  toFun x := ((x.1.1.1, x.1.2.1), ((x.1.1.2, x.1.2.2), x.2))
  invFun x := (((x.1.1, x.2.1.1), (x.1.2, x.2.1.2)), x.2.2)
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `((S₁ × S₂) × (Z × V)) × Z' ≃ ((S₁ × Z) × (S₂ × Z')) × V` (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
def regroupTop {R : Type*} [Semiring R] (S₁ S₂ Z Z' V : Type*) [AddCommMonoid S₁]
    [AddCommMonoid S₂] [AddCommMonoid Z] [AddCommMonoid Z'] [AddCommMonoid V] [Module R S₁]
    [Module R S₂] [Module R Z] [Module R Z'] [Module R V] :
    (((S₁ × S₂) × (Z × V)) × Z') ≃ₗ[R] (((S₁ × Z) × (S₂ × Z')) × V) where
  toFun x := (((x.1.1.1, x.1.2.1), (x.1.1.2, x.2)), x.1.2.2)
  invFun x := (((x.1.1.1, x.1.2.1), (x.1.1.2, x.2)), x.1.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `AddEquiv.prodCongr` for additive commutative groups (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
def addProdCongr {A B C D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] (e₁ : A ≃+ B) (e₂ : C ≃+ D) : A × C ≃+ B × D :=
  e₁.prodCongr e₂

/-- The bookkeeping of Part Y of `C37_the_mirror_that_doubles.md`: from
`A × T ≃ F₀ × R`, `(A × T') × (A × T') ≃ G₀ × R` and `F₀ × A ≃ G₀ × V`, deduce
`(A × A) × T ≃ (A × A) × ((T' × T') × V)`. -/
theorem assemble {A T T' F₀ G₀ R V : Type*} [AddCommGroup A] [AddCommGroup T] [AddCommGroup T']
    [AddCommGroup F₀] [AddCommGroup G₀] [AddCommGroup R] [AddCommGroup V]
    (eL : A × T ≃+ F₀ × R) (eR : (A × T') × (A × T') ≃+ G₀ × R) (eT : F₀ × A ≃+ G₀ × V) :
    Nonempty ((A × A) × T ≃+ (A × A) × ((T' × T') × V)) :=
  ⟨(swapRight _ _ _).trans <| (addProdCongr eL (AddEquiv.refl _)).trans <|
    (swapRight _ _ _).trans <| (addProdCongr eT (AddEquiv.refl _)).trans <|
    (swapRight _ _ _).trans <| (addProdCongr eR.symm (AddEquiv.refl _)).trans
      (regroup _ _ _ _ _)⟩

/-- The interleaving `Fin M ⊕ Fin M ≃ Fin (2M)`, `inl q ↦ 2q`, `inr q ↦ 2q + 1` (auxiliary for
Part Y of `C37_the_mirror_that_doubles.md`). -/
def interleave (M : ℕ) : Fin M ⊕ Fin M ≃ Fin (2 * M) where
  toFun := Sum.elim (fun q => ⟨2 * q, by omega⟩) (fun q => ⟨2 * q + 1, by omega⟩)
  invFun p := if p.val % 2 = 0 then Sum.inl ⟨p / 2, by omega⟩ else Sum.inr ⟨p / 2, by omega⟩
  left_inv := by
    rintro (q | q)
    · simp
    · simp only [Sum.elim_inr]
      rw [if_neg (by omega)]
      congr 1; ext; simp; omega
  right_inv := by
    intro p
    by_cases h : p.val % 2 = 0
    · simp only [h, if_true, Sum.elim_inl]; ext; simp; omega
    · simp only [h, if_false, Sum.elim_inr]; ext; simp; omega

/-- Transport of `XFam` along equalities of the family and the shift (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
def castXFam {a b c d : ℕ} (h1 : a = b) (h2 : c = d) : XFam a c ≃ₗ[ℤ_[2]] XFam b d := by
  subst h1 h2; exact LinearEquiv.refl _ _

/-! ### Torsion -/

/-- The first coordinate of the image of a `2`-power torsion element `(0, x)` under an additive
equivalence `A × T ≃+ A' × T'` vanishes when `A'` has no `2`-power torsion (auxiliary for Part Y
of `C37_the_mirror_that_doubles.md`). -/
lemma fst_map_zero_mk {A A' T T' : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup T]
    [AddCommGroup T'] (hA' : ∀ (a : A') (n : ℕ), (2 ^ n : ℕ) • a = 0 → a = 0)
    (e : A × T ≃+ A' × T') {x : T} {n : ℕ} (hn : (2 ^ n : ℕ) • x = 0) : (e (0, x)).1 = 0 := by
  apply hA' _ n
  have : (2 ^ n : ℕ) • e (0, x) = 0 := by
    rw [← map_nsmul, Prod.smul_mk, smul_zero, hn, Prod.mk_zero_zero, map_zero]
  simpa using congrArg Prod.fst this

/-- Cancellation of a `2`-torsion-free factor (the suggestion of the file for Part Y of
`C37_the_mirror_that_doubles.md`): if `A × T ≃+ A' × T'` where `A` and `A'` have no `2`-power
torsion and every element of `T` and of `T'` is killed by a power of `2`, then `T ≃+ T'`
(`x ↦ (e (0, x)).2`). -/
theorem cancel_torsion {A A' T T' : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup T]
    [AddCommGroup T'] (hA : ∀ (a : A) (n : ℕ), (2 ^ n : ℕ) • a = 0 → a = 0)
    (hA' : ∀ (a : A') (n : ℕ), (2 ^ n : ℕ) • a = 0 → a = 0)
    (hT : ∀ x : T, ∃ n : ℕ, (2 ^ n : ℕ) • x = 0) (hT' : ∀ y : T', ∃ n : ℕ, (2 ^ n : ℕ) • y = 0)
    (e : A × T ≃+ A' × T') : Nonempty (T ≃+ T') := by
  have key : ∀ x : T, (e (0, x)).1 = 0 := fun x => by
    obtain ⟨n, hn⟩ := hT x
    exact fst_map_zero_mk hA' e hn
  have key' : ∀ y : T', (e.symm (0, y)).1 = 0 := fun y => by
    obtain ⟨n, hn⟩ := hT' y
    exact fst_map_zero_mk hA e.symm hn
  refine ⟨{ toFun := fun x => (e (0, x)).2
            invFun := fun y => (e.symm (0, y)).2
            left_inv := fun x => ?_
            right_inv := fun y => ?_
            map_add' := fun x y => ?_ }⟩
  · have : ((0 : A'), (e (0, x)).2) = e (0, x) := Prod.ext (key x).symm rfl
    simp only [this, AddEquiv.symm_apply_apply]
  · have : ((0 : A), (e.symm (0, y)).2) = e.symm (0, y) := Prod.ext (key' y).symm rfl
    simp only [this, AddEquiv.apply_symm_apply]
  · show (e (0, x + y)).2 = (e (0, x)).2 + (e (0, y)).2
    rw [show ((0 : A), x + y) = (0, x) + (0, y) by simp, map_add, Prod.snd_add]

/-- `ℤ_[2] × ℤ_[2]` has no `2`-power torsion (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
lemma padic_sq_torsionFree : ∀ (a : ℤ_[2] × ℤ_[2]) (n : ℕ), (2 ^ n : ℕ) • a = 0 → a = 0 := by
  have h1 : ∀ (a : ℤ_[2]) (n : ℕ), (2 ^ n : ℕ) • a = 0 → a = 0 := fun a n h => by
    rw [nsmul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 (by positivity))
  intro a n h
  exact Prod.ext (h1 a.1 n (by simpa using congrArg Prod.fst h))
    (h1 a.2 n (by simpa using congrArg Prod.snd h))

/-- If `2^n • x = 0` and `n ≤ m`, then `2^m • x = 0` (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
lemma two_pow_smul_of_le {G : Type*} [AddCommGroup G] {x : G} {n m : ℕ}
    (h : (2 ^ n : ℕ) • x = 0) (hnm : n ≤ m) : (2 ^ m : ℕ) • x = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, mul_nsmul, h, nsmul_zero]

/-- Every element of `Syl2 T` is killed by a power of `2` (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
lemma syl2_torsion (T : Type*) [AddCommGroup T] :
    ∀ x : CubeLaplacian.Syl2 T, ∃ n : ℕ, (2 ^ n : ℕ) • x = 0 := fun x => by
  obtain ⟨n, hn⟩ : ∃ k : ℕ, (2 ^ k : ℕ) • (x : T) = 0 := x.2
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

/-- `FamilyGroup.Q a` is killed by `2^a` (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
lemma Q_torsion (a : ℕ) : ∀ x : FamilyGroup.Q a, (2 ^ a : ℕ) • x = 0 := fun x => by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_nsmul, Ideal.Quotient.eq_zero_iff_mem, nsmul_eq_mul]
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- `FamilyGroup.Q a ≃ ZMod (2^a)`, through `PadicInt.toZModPow`, whose kernel is
`span {2^a}` (the suggestion of the file for Part Y of `C37_the_mirror_that_doubles.md`). -/
noncomputable def QequivZMod (a : ℕ) : FamilyGroup.Q a ≃+* ZMod (2 ^ a) :=
  (Ideal.quotEquivOfEq (by rw [PadicInt.ker_toZModPow]; simp)).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow a)))

/-! ### The small clocks of `λ + 1` -/

/-- The exponent count of the small clocks doubles (auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
lemma two_pow_SC_double (d : List Bool) (a : Fin (true :: d).length) :
    2 ^ ((true :: d).length + Dance.mCount (true :: d) - 1 - a) =
      2 ^ ((false :: d).length + Dance.mCount (false :: d) - 1 - a) +
        2 ^ ((false :: d).length + Dance.mCount (false :: d) - 1 - a) := by
  have ha := a.2
  simp only [List.length_cons, Dance.mCount] at ha ⊢
  rw [← two_mul, ← pow_succ']
  congr 1
  omega

/-- `SC (true :: d) ≃ SC (false :: d) × SC (false :: d)`: the small clocks of `λ + 1` are those of
`λ`, taken twice (C33 (S4); auxiliary for Part Y of `C37_the_mirror_that_doubles.md`). -/
noncomputable def scDouble (d : List Bool) :
    FamilyGroup.SC (true :: d) ≃ₗ[ℤ_[2]] FamilyGroup.SC (false :: d) × FamilyGroup.SC (false :: d) :=
  (S4equiv (true :: d)).trans
    ((LinearEquiv.piCongrRight fun (a : Fin (true :: d).length) =>
      (LinearEquiv.funCongrLeft ℤ_[2] (FamilyGroup.Q (a : ℕ))
        (finSumFinEquiv.trans (finCongr (two_pow_SC_double d a).symm))).trans
        (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ_[2] _)).trans
      ((piProdEquiv _ _).trans
        ((S4equiv (false :: d)).symm.prodCongr (S4equiv (false :: d)).symm)))

/-- For odd `λ`, `SC (ds (λ + 1)) ≃ SC (ds λ) × SC (ds λ)` (from (A2); auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
lemma scDouble_ds (lam : ℕ) (hodd : lam % 2 = 1) :
    Nonempty (FamilyGroup.SC (ds (lam + 1)) ≃ₗ[ℤ_[2]]
      FamilyGroup.SC (ds lam) × FamilyGroup.SC (ds lam)) := by
  obtain ⟨l, rfl⟩ : ∃ l, lam = 2 * l + 1 := ⟨lam / 2, by omega⟩
  rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring, ds_even, ds_odd]
  exact ⟨scDouble _⟩

/-! ### The families `λ + 1`, `λ < 2^e − 1` -/

/-- The big clocks of `(λ + 1, i)` are those of `(λ, i)`, taken twice (from (X1); auxiliary for
Part Y of `C37_the_mirror_that_doubles.md`). -/
noncomputable def bigDouble (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1)
    (hlt : lam < 2 ^ e - 1) (i' : ℕ) (hi' : (2 ^ e - 1 - lam) / 2 = i' + 1) :
    ((p : Fin (2 ^ Dance.mCount (ds (lam + 1)))) →
        FamilyGroup.Q (FamilyGroup.yPool (ds (lam + 1)) (i' + 1) p).toNat) ≃ₗ[ℤ_[2]]
      ((q : Fin (2 ^ Dance.mCount (ds lam))) →
          FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i' + 1) q).toNat) ×
        ((q : Fin (2 ^ Dance.mCount (ds lam))) →
          FamilyGroup.Q (FamilyGroup.yPool (ds lam) (i' + 1) q).toNat) :=
  have hM : 2 * 2 ^ Dance.mCount (ds lam) = 2 ^ Dance.mCount (ds (lam + 1)) := by
    rw [A2_mCount lam hodd, pow_succ, mul_comm]
  have hX : ∀ j, FamilyGroup.yPool (ds (lam + 1)) (i' + 1) j =
      FamilyGroup.yPool (ds lam) (i' + 1) (j / 2) := fun j => by
    have := X1 e he lam hodd hlt j; rwa [hi'] at this
  (LinearEquiv.piCongrLeft ℤ_[2]
      (fun p : Fin (2 ^ Dance.mCount (ds (lam + 1))) =>
        FamilyGroup.Q (FamilyGroup.yPool (ds (lam + 1)) (i' + 1) p).toNat)
      ((interleave _).trans (finCongr hM))).symm.trans
    ((LinearEquiv.sumPiEquivProdPi ℤ_[2] _ _ _).trans
      (LinearEquiv.prodCongr
        (LinearEquiv.piCongrRight fun q => castQ (by
          show (FamilyGroup.yPool (ds (lam + 1)) (i' + 1) (2 * q)).toNat = _
          rw [hX, show 2 * (q : ℕ) / 2 = q by omega]))
        (LinearEquiv.piCongrRight fun q => castQ (by
          show (FamilyGroup.yPool (ds (lam + 1)) (i' + 1) (2 * q + 1)).toNat = _
          rw [hX, show (2 * (q : ℕ) + 1) / 2 = q by omega]))))

/-- For `e ≥ 1`, odd `λ < 2^e − 1` and `i = (2^e − 1 − λ) / 2`,
`XFam (λ + 1) i ≃ XFam λ i × XFam λ i` (C33 (S4) with (A2) for the small clocks, (X1) for the big
clocks; auxiliary for Part Y of `C37_the_mirror_that_doubles.md`). -/
theorem famDouble (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) :
    Nonempty (XFam (lam + 1) ((2 ^ e - 1 - lam) / 2) ≃ₗ[ℤ_[2]]
      XFam lam ((2 ^ e - 1 - lam) / 2) × XFam lam ((2 ^ e - 1 - lam) / 2)) := by
  have he2 : 2 ^ e % 2 = 0 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; omega
  obtain ⟨i', hi'⟩ : ∃ i', (2 ^ e - 1 - lam) / 2 = i' + 1 := ⟨(2 ^ e - 1 - lam) / 2 - 1, by omega⟩
  obtain ⟨esc⟩ := scDouble_ds lam hodd
  have ebig := bigDouble e he lam hodd hlt i' hi'
  rw [hi']
  exact ⟨(esc.prodCongr ebig).trans (LinearEquiv.prodProdProdComm ℤ_[2] _ _ _ _)⟩

/-! ### The top family -/

/-- The top family: for `e ≥ 1`,
`XFam (2^e) 0 × ℤ_2 ≃ (XFam (2^e − 1) 0 × XFam (2^e − 1) 0) × Q (2^e + e − 1)` (the family
`2^e − 1` is `SC × (ℤ_2 × Π_{Fin 0} …)`, the family `2^e` is `SC × (ℤ_2 × Q (2^e + e − 1))`;
auxiliary for Part Y of `C37_the_mirror_that_doubles.md`). -/
theorem famTop (e : ℕ) (he : 1 ≤ e) :
    Nonempty ((XFam (2 ^ e) 0 × ℤ_[2]) ≃ₗ[ℤ_[2]]
      (XFam (2 ^ e - 1) 0 × XFam (2 ^ e - 1) 0) × FamilyGroup.Q (2 ^ e + e - 1)) := by
  have hv := yPool0_top e he
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ e = N + 1 := ⟨2 ^ e - 1, by have := Nat.one_le_two_pow (n := e); omega⟩
  have hNe : N = 2 ^ e - 1 := by omega
  have hodd : N % 2 = 1 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ] at hN; omega
  have hI : Windows.Ids (ds N) = ∅ := by rw [hNe]; exact Ids_ds_two_pow_sub_one e
  have hm0 : Dance.mCount (ds N) = 0 := by rw [← Windows.card_Ids, hI, Finset.card_empty]
  have hm1 : Dance.mCount (ds (N + 1)) = 1 := by rw [A2_mCount N hodd, hm0]
  rw [hN] at hv ⊢
  rw [Nat.add_sub_cancel]
  obtain ⟨esc⟩ := scDouble_ds N hodd
  have hc : 1 = 2 ^ Dance.mCount (ds (N + 1)) - 1 := by rw [hm1]; rfl
  let ebig : ((q : Fin (2 ^ Dance.mCount (ds (N + 1)) - 1)) →
      FamilyGroup.Q (FamilyGroup.yPool0 (ds (N + 1)) q).toNat) ≃ₗ[ℤ_[2]]
      FamilyGroup.Q (N + 1 + e - 1) :=
    (LinearEquiv.piCongrLeft ℤ_[2]
      (fun q : Fin (2 ^ Dance.mCount (ds (N + 1)) - 1) =>
        FamilyGroup.Q (FamilyGroup.yPool0 (ds (N + 1)) q).toNat) (finCongr hc)).symm.trans
      ((LinearEquiv.piUnique ℤ_[2] _).trans (castQ (by
        show (FamilyGroup.yPool0 (ds (N + 1)) 0).toNat = _
        rw [hv, Int.toNat_natCast])))
  haveI : IsEmpty (Fin (2 ^ Dance.mCount (ds N) - 1)) :=
    ⟨fun q => by have := q.2; simp only [hm0, pow_zero, Nat.sub_self] at this; omega⟩
  let eN : XFam N 0 ≃ₗ[ℤ_[2]] FamilyGroup.SC (ds N) × ℤ_[2] :=
    (LinearEquiv.refl ℤ_[2] (FamilyGroup.SC (ds N))).prodCongr LinearEquiv.prodUnique
  exact ⟨(((esc.prodCongr ((LinearEquiv.refl ℤ_[2] ℤ_[2]).prodCongr ebig)).prodCongr
    (LinearEquiv.refl ℤ_[2] ℤ_[2])).trans (regroupTop _ _ _ _ _)).trans
      ((eN.symm.prodCongr eN.symm).prodCongr (LinearEquiv.refl _ _))⟩

/-! ### Assembly -/

/-- The doubling with two copies of `ℤ_2`: for `e ≥ 1`,
`(ℤ_2 × ℤ_2) × S (2^e) ≃+ (ℤ_2 × ℤ_2) × ((S (2^e − 1) × S (2^e − 1)) × Q (2^e + e − 1))`
(from C33 (M2), (A1), `famDouble` and `famTop`; auxiliary for Part Y of
`C37_the_mirror_that_doubles.md`). -/
theorem doubled_equiv (e : ℕ) (he : 1 ≤ e) :
    Nonempty ((ℤ_[2] × ℤ_[2]) × CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      (ℤ_[2] × ℤ_[2]) × ((CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × FamilyGroup.Q (2 ^ e + e - 1))) := by
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hN1 : 2 ^ e - 1 + 1 = 2 ^ e := by omega
  have hodd : (2 ^ e - 1) % 2 = 1 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; have := Nat.one_le_two_pow (n := f); omega
  have hN0 : 1 ≤ 2 ^ e - 1 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; have := Nat.one_le_two_pow (n := f); omega
  set l := FamDec.L (2 ^ e - 1) with hl
  have hL : FamDec.L (2 ^ e) = l.map (· + 1) := by
    have := A1_map (2 ^ e - 1) hodd; rwa [hN1] at this
  have hlen : l.length = (FamDec.L (2 ^ e)).length := by rw [hL, List.length_map]
  have hget : ∀ j : Fin l.length, (FamDec.L (2 ^ e)).get (finCongr hlen j) = l.get j + 1 := by
    intro j
    have : ∀ l' : List ℕ, l' = l.map (· + 1) → ∀ h : l.length = l'.length,
        l'.get (finCongr h j) = l.get j + 1 := by
      rintro l' rfl h; simp
    exact this _ hL hlen
  have hcount : l.count (2 ^ e - 1) = 1 := FamDec.m_self _
  obtain ⟨j0, hj0⟩ : ∃ j0, l.get j0 = 2 ^ e - 1 :=
    List.mem_iff_get.1 (List.count_pos_iff.1 (by omega))
  have hne : ∀ j : Fin l.length, j ≠ j0 → l.get j ≠ 2 ^ e - 1 := by
    intro j hj h
    have hd : List.Duplicate (2 ^ e - 1) l := by
      rw [List.duplicate_iff_exists_distinct_get]
      rcases lt_or_gt_of_ne hj with h' | h'
      · exact ⟨j, j0, h', h.symm, hj0.symm⟩
      · exact ⟨j0, j, h', hj0.symm, h.symm⟩
    have := List.duplicate_iff_two_le_count.1 hd
    omega
  have hmem : ∀ j : Fin l.length, l.get j % 2 = 1 ∧ l.get j ≤ 2 ^ e - 1 := fun j =>
    ⟨A1_odd _ hodd _ (List.get_mem _ _), FamDec.le_of_mem_L _ _ (List.get_mem _ _)⟩
  -- the side of `2^e`
  let E2 : ((j : Fin (FamDec.L (2 ^ e)).length) →
      XFam ((FamDec.L (2 ^ e)).get j) ((2 ^ e - (FamDec.L (2 ^ e)).get j) / 2)) ≃ₗ[ℤ_[2]]
      ((j : Fin l.length) → XFam (l.get j + 1) ((2 ^ e - (l.get j + 1)) / 2)) :=
    (LinearEquiv.piCongrLeft ℤ_[2]
      (fun j => XFam ((FamDec.L (2 ^ e)).get j) ((2 ^ e - (FamDec.L (2 ^ e)).get j) / 2))
      (finCongr hlen)).symm.trans
      (LinearEquiv.piCongrRight fun j => castXFam (hget j) (by rw [hget j]))
  let E3 := piSplitAtL (R := ℤ_[2]) j0
    (fun j : Fin l.length => XFam (l.get j + 1) ((2 ^ e - (l.get j + 1)) / 2))
  let edbl : (j : {j // j ≠ j0}) → XFam (l.get j + 1) ((2 ^ e - (l.get j + 1)) / 2) ≃ₗ[ℤ_[2]]
      XFam (l.get j) ((2 ^ e - 1 - l.get j) / 2) × XFam (l.get j) ((2 ^ e - 1 - l.get j) / 2) :=
    fun j => (castXFam rfl (by omega)).trans
      (famDouble e he (l.get j) (hmem j).1
        (lt_of_le_of_ne (hmem j).2 (hne j j.2))).some
  let E4 := LinearEquiv.prodCongr
    (LinearEquiv.refl ℤ_[2] (XFam (l.get j0 + 1) ((2 ^ e - (l.get j0 + 1)) / 2)))
    (LinearEquiv.piCongrRight edbl)
  let Left := (M2equiv (2 ^ e) hpos).trans (E2.trans (E3.trans E4)).toAddEquiv
  -- the side of `2^e − 1`
  let E6 := (piProdEquiv (R := ℤ_[2])
    (fun j : Fin l.length => XFam (l.get j) ((2 ^ e - 1 - l.get j) / 2))
    (fun j : Fin l.length => XFam (l.get j) ((2 ^ e - 1 - l.get j) / 2))).symm
  let E7 := piSplitAtL (R := ℤ_[2]) j0
    (fun j : Fin l.length => XFam (l.get j) ((2 ^ e - 1 - l.get j) / 2) ×
      XFam (l.get j) ((2 ^ e - 1 - l.get j) / 2))
  let Right := (addProdCongr (M2equiv (2 ^ e - 1) hN0) (M2equiv (2 ^ e - 1) hN0)).trans
    (E6.trans E7).toAddEquiv
  -- the top family
  have h1 : l.get j0 + 1 = 2 ^ e := by omega
  have h2 : (2 ^ e - (l.get j0 + 1)) / 2 = 0 := by omega
  let E8 : (XFam (l.get j0 + 1) ((2 ^ e - (l.get j0 + 1)) / 2) × ℤ_[2]) ≃ₗ[ℤ_[2]]
      (XFam (l.get j0) ((2 ^ e - 1 - l.get j0) / 2) ×
        XFam (l.get j0) ((2 ^ e - 1 - l.get j0) / 2)) × FamilyGroup.Q (2 ^ e + e - 1) :=
    ((castXFam h1 h2).prodCongr (LinearEquiv.refl _ _)).trans
      ((famTop e he).some.trans
        (((castXFam hj0.symm (by omega)).prodCongr (castXFam hj0.symm (by omega))).prodCongr
          (LinearEquiv.refl _ _)))
  exact assemble Left Right E8.toAddEquiv

/-- The `2`-part of the sandpile group of the cube `2^e` with the extra factors cancelled (the
common core of (Y1) and (Y2) of `C37_the_mirror_that_doubles.md`): for `e ≥ 1`,
`S (2^e) ≃+ (S (2^e − 1) × S (2^e − 1)) × Q (2^e + e − 1)`. -/
theorem Y_core (e : ℕ) (he : 1 ≤ e) :
    Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × FamilyGroup.Q (2 ^ e + e - 1)) := by
  obtain ⟨E⟩ := doubled_equiv e he
  refine cancel_torsion padic_sq_torsionFree padic_sq_torsionFree (syl2_torsion _) ?_ E
  rintro ⟨⟨a, b⟩, q⟩
  obtain ⟨n1, h1⟩ := syl2_torsion _ a
  obtain ⟨n2, h2⟩ := syl2_torsion _ b
  refine ⟨n1 + n2 + (2 ^ e + e - 1), ?_⟩
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · exact two_pow_smul_of_le h1 (by omega)
  · exact two_pow_smul_of_le h2 (by omega)
  · exact two_pow_smul_of_le (Q_torsion _ q) (by omega)

/-- **(Y1)** of `C37_the_mirror_that_doubles.md` (Corollary 1.7, Gao et al. Conjecture 5.4, with
`ℤ_[2]` on both sides): for every `e ≥ 1`,
`ℤ_[2] × S (2^e) ≃+ ℤ_[2] × ((S (2^e − 1) × S (2^e − 1)) × Q (2^e + e − 1))`, with
`S n = CubeLaplacian.Syl2 (CubeLaplacian.K n)`. -/
theorem Y1 (e : ℕ) (he : 1 ≤ e) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      ℤ_[2] × ((CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × FamilyGroup.Q (2 ^ e + e - 1))) := by
  obtain ⟨T⟩ := Y_core e he
  exact ⟨(AddEquiv.refl ℤ_[2]).prodCongr T⟩

/-- **(Y2)** of `C37_the_mirror_that_doubles.md` (Corollary 1.7, Gao et al. Conjecture 5.4): for
every `e ≥ 1`, `S (2^e) ≃+ (S (2^e − 1) × S (2^e − 1)) × ZMod (2^(2^e + e − 1))`, i.e.
`Syl_2 K(Q_{2^e}) ≅ Syl_2 K(Q_{2^e − 1})² ⊕ ℤ/2^{2^e + e − 1}`, with
`S n = CubeLaplacian.Syl2 (CubeLaplacian.K n)`. -/
theorem Y2 (e : ℕ) (he : 1 ≤ e) :
    Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e)) ≃+
      (CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1)) ×
        CubeLaplacian.Syl2 (CubeLaplacian.K (2 ^ e - 1))) × ZMod (2 ^ (2 ^ e + e - 1))) := by
  obtain ⟨T⟩ := Y_core e he
  exact ⟨T.trans ((AddEquiv.refl _).prodCongr (QequivZMod _).toAddEquiv)⟩

end Mirror
