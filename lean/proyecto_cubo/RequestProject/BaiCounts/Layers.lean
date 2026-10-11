module

public import Mathlib

/-!
# `C34_bais_counts.md`: the layers `ℓ_0`, `ℓ_1` of an abelian group (Setting)

Encodings (namespace `BaiCounts`):

* For an additive commutative group `G` and `j : ℕ`, `twoPow G j : AddSubgroup G` is
  `2^j G := {2^j • x | x ∈ G}` (carrier `{x | ∃ y, 2 ^ j • y = x}`, `•` the `ℕ`-action).
* `l0 G := Nat.card (G ⧸ twoPow G 1)` is `ℓ_0(G) = |G/2G|`.
* `l1 G := Nat.card (twoPow G 1 ⧸ (twoPow G 2).addSubgroupOf (twoPow G 1))` is
  `ℓ_1(G) = |2G/4G|`, with `4G` viewed as a subgroup of `2G`.
* `ℤ_[2]` is `PadicInt 2`; the big clock `Q e` of C16 is (by definition) the ring quotient
  `ℤ_[2] ⧸ Ideal.span {2 ^ e}` and is written that way in this file.

This file proves the finite-group bookkeeping used in the sketches of Part F and Part B of
`C34_bais_counts.md`: invariance of `ℓ_0`, `ℓ_1` under `≃+`, multiplicativity over products of
two and over finite (dependent) products, and the values on `ℤ/2^e = Q e` and on `ℤ_[2]`.
(`Nat.card` of an infinite type is `0`; the product formulas hold in general, by `Nat.card_prod`
and `Nat.card_pi`.)
-/

@[expose] public section

namespace BaiCounts

/-- *Setting* of `C34_bais_counts.md`: `2^j G := {2^j • x | x ∈ G}` as an `AddSubgroup G`. -/
def twoPow (G : Type*) [AddCommGroup G] (j : ℕ) : AddSubgroup G where
  carrier := {x | ∃ y : G, 2 ^ j • y = x}
  zero_mem' := ⟨0, smul_zero _⟩
  add_mem' := by
    rintro a b ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y + z, smul_add _ _ _⟩
  neg_mem' := by
    rintro a ⟨y, rfl⟩
    exact ⟨-y, smul_neg _ _⟩

/-- *Setting* of `C34_bais_counts.md`: the layer `ℓ_0(G) := Nat.card (G ⧸ 2G)`. -/
noncomputable def l0 (G : Type*) [AddCommGroup G] : ℕ := Nat.card (G ⧸ twoPow G 1)

/-- *Setting* of `C34_bais_counts.md`: the layer
`ℓ_1(G) := Nat.card (2G ⧸ (4G as a subgroup of 2G))`. -/
noncomputable def l1 (G : Type*) [AddCommGroup G] : ℕ :=
  Nat.card (twoPow G 1 ⧸ (twoPow G 2).addSubgroupOf (twoPow G 1))

/-- Membership in `2^j G` (Setting of `C34_bais_counts.md`). -/
lemma mem_twoPow {G : Type*} [AddCommGroup G] {j : ℕ} {x : G} :
    x ∈ twoPow G j ↔ ∃ y : G, 2 ^ j • y = x := Iff.rfl

/-! ### Generic counting lemmas -/

/-- If `f : A →+ B` is surjective with kernel `S`, then `|A ⧸ S| = |B|` (auxiliary for the
Setting of `C34_bais_counts.md`). -/
lemma card_quot_of_surj {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Surjective f) (S : AddSubgroup A) (hS : ∀ x, x ∈ S ↔ f x = 0) :
    Nat.card (A ⧸ S) = Nat.card B := by
  have : S = f.ker := by ext x; rw [hS, AddMonoidHom.mem_ker]
  subst this
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv

/-- `ℓ_1(G) = |G ⧸ {x | 2x ∈ 4G}|`, through the surjection `x ↦ [2x]` (auxiliary for the Setting
of `C34_bais_counts.md`). -/
lemma l1_eq (G : Type*) [AddCommGroup G] :
    l1 G = Nat.card (G ⧸ (twoPow G 2).comap (nsmulAddMonoidHom (α := G) 2)) := by
  let g : G →+ twoPow G 1 :=
    { toFun := fun x => ⟨2 • x, ⟨x, by simp⟩⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  let f : G →+ twoPow G 1 ⧸ (twoPow G 2).addSubgroupOf (twoPow G 1) :=
    (QuotientAddGroup.mk' _).comp g
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨⟨w, ⟨y, rfl⟩⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    exact ⟨y, by simp [f, g]⟩
  rw [l1, card_quot_of_surj f hf]
  intro x
  simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap]
  rfl

/-- Transport of a quotient count along `e : G ≃+ H` (auxiliary for the invariance of the layers
in `C34_bais_counts.md`). -/
lemma card_quot_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (S : AddSubgroup G) (T : AddSubgroup H) (h : ∀ x, x ∈ T ↔ e.symm x ∈ S) :
    Nat.card (H ⧸ T) = Nat.card (G ⧸ S) := by
  refine card_quot_of_surj ((QuotientAddGroup.mk' S).comp e.symm.toAddMonoidHom) ?_ T ?_
  · intro z
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective S z
    exact ⟨e y, by simp⟩
  · intro x
    simp [h]

/-- A product count (auxiliary for the multiplicativity of the layers in `C34_bais_counts.md`). -/
lemma card_quot_prod {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (S : AddSubgroup G) (T : AddSubgroup H) (U : AddSubgroup (G × H))
    (hU : ∀ x, x ∈ U ↔ x.1 ∈ S ∧ x.2 ∈ T) :
    Nat.card ((G × H) ⧸ U) = Nat.card (G ⧸ S) * Nat.card (H ⧸ T) := by
  rw [← Nat.card_prod]
  refine card_quot_of_surj (AddMonoidHom.prodMap (QuotientAddGroup.mk' S)
    (QuotientAddGroup.mk' T)) ?_ U ?_
  · rintro ⟨a, b⟩
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective S a
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective T b
    exact ⟨(y, z), rfl⟩
  · intro x
    rw [hU]
    simp [Prod.ext_iff]

/-- A finite product count (auxiliary for the multiplicativity of the layers in
`C34_bais_counts.md`). -/
lemma card_quot_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    (S : ∀ i, AddSubgroup (G i)) (U : AddSubgroup (∀ i, G i))
    (hU : ∀ x, x ∈ U ↔ ∀ i, x i ∈ S i) :
    Nat.card ((∀ i, G i) ⧸ U) = ∏ i, Nat.card (G i ⧸ S i) := by
  rw [← Nat.card_pi]
  refine card_quot_of_surj (Pi.addMonoidHom fun i =>
    (QuotientAddGroup.mk' (S i)).comp (Pi.evalAddMonoidHom G i)) ?_ U ?_
  · intro z
    choose y hy using fun i => QuotientAddGroup.mk'_surjective (S i) (z i)
    exact ⟨y, funext fun i => hy i⟩
  · intro x
    rw [hU]
    simp [funext_iff]

/-! ### Membership in `2^j G` for products and transports -/

/-- `2^j (G × H) = 2^j G × 2^j H` (auxiliary for the multiplicativity of the layers in `C34_bais_counts.md`). -/
lemma mem_twoPow_prod {G H : Type*} [AddCommGroup G] [AddCommGroup H] (j : ℕ) (x : G × H) :
    x ∈ twoPow (G × H) j ↔ x.1 ∈ twoPow G j ∧ x.2 ∈ twoPow H j := by
  simp only [mem_twoPow]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, rfl⟩, ⟨y.2, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- `2^j (Π_i G_i) = Π_i 2^j G_i` (auxiliary for the multiplicativity of the layers in `C34_bais_counts.md`). -/
lemma mem_twoPow_pi {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)] (j : ℕ)
    (x : ∀ i, G i) : x ∈ twoPow (∀ i, G i) j ↔ ∀ i, x i ∈ twoPow (G i) j := by
  simp only [mem_twoPow]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

/-- `2^j` commutes with `≃+` (auxiliary for the invariance of the layers in `C34_bais_counts.md`). -/
lemma mem_twoPow_equiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (j : ℕ)
    (x : H) : x ∈ twoPow H j ↔ e.symm x ∈ twoPow G j := by
  simp only [mem_twoPow]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by simp [map_nsmul]⟩
  · rintro ⟨y, hy⟩
    exact ⟨e y, by rw [← map_nsmul, hy]; simp⟩

/-! ### Invariance and multiplicativity -/

/-- `ℓ_0` is invariant under `≃+` (Part B sketch of `C34_bais_counts.md`). -/
theorem l0_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) :
    l0 G = l0 H :=
  (card_quot_congr e _ _ (mem_twoPow_equiv e 1)).symm

/-- `ℓ_1` is invariant under `≃+` (Part B sketch of `C34_bais_counts.md`). -/
theorem l1_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) :
    l1 G = l1 H := by
  rw [l1_eq, l1_eq]
  refine (card_quot_congr e _ _ fun x => ?_).symm
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply]
  rw [mem_twoPow_equiv e, map_nsmul]

/-- `ℓ_0(G × H) = ℓ_0(G) ℓ_0(H)` (Part F sketch of `C34_bais_counts.md`). -/
theorem l0_prod (G H : Type*) [AddCommGroup G] [AddCommGroup H] :
    l0 (G × H) = l0 G * l0 H :=
  card_quot_prod _ _ _ (mem_twoPow_prod 1)

/-- `ℓ_1(G × H) = ℓ_1(G) ℓ_1(H)` (Part F sketch of `C34_bais_counts.md`). -/
theorem l1_prod (G H : Type*) [AddCommGroup G] [AddCommGroup H] :
    l1 (G × H) = l1 G * l1 H := by
  rw [l1_eq, l1_eq, l1_eq]
  refine card_quot_prod _ _ _ fun x => ?_
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply]
  exact mem_twoPow_prod 2 _

/-- `ℓ_0(Π_i G_i) = Π_i ℓ_0(G_i)` over a finite index type (Part F sketch of
`C34_bais_counts.md`). -/
theorem l0_pi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, AddCommGroup (G i)] :
    l0 (∀ i, G i) = ∏ i, l0 (G i) :=
  card_quot_pi _ _ (mem_twoPow_pi 1)

/-- `ℓ_1(Π_i G_i) = Π_i ℓ_1(G_i)` over a finite index type (Part F sketch of
`C34_bais_counts.md`). -/
theorem l1_pi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, AddCommGroup (G i)] :
    l1 (∀ i, G i) = ∏ i, l1 (G i) := by
  rw [l1_eq]
  simp_rw [l1_eq]
  refine card_quot_pi _ _ fun x => ?_
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply]
  exact mem_twoPow_pi 2 _

/-! ### Trivial groups -/

/-- A quotient of a trivial group is trivial (auxiliary for the layers in `C34_bais_counts.md`). -/
lemma subsingleton_quot (G : Type*) [AddCommGroup G] [Subsingleton G] (S : AddSubgroup G) :
    Subsingleton (G ⧸ S) :=
  ⟨fun a b => by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective S a
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective S b
    rw [Subsingleton.elim a b]⟩

/-- `ℓ_0` of a trivial group is `1` (Part F sketch of `C34_bais_counts.md`). -/
lemma l0_of_subsingleton (G : Type*) [AddCommGroup G] [Subsingleton G] : l0 G = 1 := by
  rw [l0, Nat.card_eq_one_iff_unique]
  exact ⟨subsingleton_quot G _, inferInstance⟩

/-- `ℓ_1` of a trivial group is `1` (Part F sketch of `C34_bais_counts.md`). -/
lemma l1_of_subsingleton (G : Type*) [AddCommGroup G] [Subsingleton G] : l1 G = 1 := by
  rw [l1_eq, Nat.card_eq_one_iff_unique]
  exact ⟨subsingleton_quot G _, inferInstance⟩

/-- If `2G = 0` then `ℓ_1(G) = 1` (Part F sketch of `C34_bais_counts.md`). -/
lemma l1_of_two_smul (G : Type*) [AddCommGroup G] (h : ∀ x : G, 2 • x = 0) : l1 G = 1 := by
  rw [l1_eq, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  rename_i a b
  rw [QuotientAddGroup.eq]
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, h]
  exact (twoPow G 2).zero_mem

/-! ### Quotients of `ℤ_[2]` -/

/-- A surjection from `ℤ_[2]` with kernel `2ℤ_[2]` has a target of cardinality `2` (auxiliary for
the Part F and Part B sketches of `C34_bais_counts.md`). -/
lemma card_eq_two {H : Type*} [AddCommGroup H] (f : ℤ_[2] →+ H) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 0 ↔ (2 : ℤ_[2]) ∣ x) : Nat.card H = 2 := by
  rw [← card_quot_of_surj f hf f.ker (fun x => AddMonoidHom.mem_ker),
    card_quot_of_surj (PadicInt.toZModPow (p := 2) 1).toAddMonoidHom
      (ZMod.ringHom_surjective _) f.ker]
  · simp
  · intro x
    rw [AddMonoidHom.mem_ker, hker]
    change _ ↔ x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    simp

/-- If `π : ℤ_[2] →+ G` is surjective with kernel inside `2ℤ_[2]`, then `ℓ_0(G) = 2` (auxiliary for
the Part F and Part B sketches of `C34_bais_counts.md`). -/
lemma l0_of_surj {G : Type*} [AddCommGroup G] (π : ℤ_[2] →+ G) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 0 → (2 : ℤ_[2]) ∣ x) : l0 G = 2 := by
  refine card_eq_two ((QuotientAddGroup.mk' _).comp π)
    ((QuotientAddGroup.mk'_surjective _).comp hπ) fun x => ?_
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    mem_twoPow, pow_one]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hπ y
    have h0 : π (x - 2 * z) = 0 := by
      rw [map_sub, ← hy, show (2 : ℤ_[2]) * z = 2 • z by rw [nsmul_eq_mul]; norm_num, map_nsmul,
        sub_self]
    obtain ⟨c, hc⟩ := hker _ h0
    exact ⟨c + z, by linear_combination hc⟩
  · rintro ⟨w, rfl⟩
    exact ⟨π w, by rw [← map_nsmul, nsmul_eq_mul]; norm_num⟩

/-- If `π : ℤ_[2] →+ G` is surjective with kernel inside `4ℤ_[2]`, then `ℓ_1(G) = 2` (auxiliary for
the Part F and Part B sketches of `C34_bais_counts.md`). -/
lemma l1_of_surj {G : Type*} [AddCommGroup G] (π : ℤ_[2] →+ G) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 0 → (4 : ℤ_[2]) ∣ x) : l1 G = 2 := by
  rw [l1_eq]
  refine card_eq_two ((QuotientAddGroup.mk' _).comp π)
    ((QuotientAddGroup.mk'_surjective _).comp hπ) fun x => ?_
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, mem_twoPow]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hπ y
    have h0 : π (2 * x - 4 * z) = 0 := by
      rw [map_sub, show (2 : ℤ_[2]) * x = 2 • x by rw [nsmul_eq_mul]; norm_num,
        show (4 : ℤ_[2]) * z = 2 ^ 2 • z by rw [nsmul_eq_mul]; norm_num, map_nsmul, map_nsmul,
        hy, sub_self]
    obtain ⟨c, hc⟩ := hker _ h0
    have h2 : (2 : ℤ_[2]) * (x - 2 * (c + z)) = 0 := by linear_combination hc
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h two_ne_zero
    · exact ⟨c + z, by linear_combination h⟩
  · rintro ⟨w, rfl⟩
    exact ⟨π w, by rw [← map_nsmul, ← map_nsmul, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring_nf⟩

/-- `ℓ_0(ℤ_[2]) = 2` (Part B sketch of `C34_bais_counts.md`). -/
theorem l0_padic : l0 ℤ_[2] = 2 :=
  l0_of_surj (AddMonoidHom.id _) Function.surjective_id (fun x hx => by simp [show x = 0 from hx])

/-- `ℓ_1(ℤ_[2]) = 2` (Part B sketch of `C34_bais_counts.md`). -/
theorem l1_padic : l1 ℤ_[2] = 2 :=
  l1_of_surj (AddMonoidHom.id _) Function.surjective_id (fun x hx => by simp [show x = 0 from hx])

/-- The kernel of the quotient map `ℤ_[2] → ℤ_[2] ⧸ (2^e)` (auxiliary for the Part F sketch of
`C34_bais_counts.md`). -/
lemma mkQ_eq_zero (e : ℕ) (x : ℤ_[2]) :
    (Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ e})).toAddMonoidHom x = 0 ↔
      (2 : ℤ_[2]) ^ e ∣ x := by
  simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- `ℓ_0(ℤ/2^e) = 2` for `e ≥ 1` (Part F sketch of `C34_bais_counts.md`). -/
theorem l0_Q {e : ℕ} (he : 1 ≤ e) : l0 (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ e}) = 2 :=
  l0_of_surj (Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ e})).toAddMonoidHom
    Ideal.Quotient.mk_surjective fun x hx => by
      have h1 := (mkQ_eq_zero e x).1 hx
      exact (pow_one (2 : ℤ_[2])) ▸ (pow_dvd_pow 2 he).trans h1

/-- `ℓ_0(ℤ/2^0) = 1` (Part F sketch of `C34_bais_counts.md`). -/
theorem l0_Q_zero : l0 (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ 0}) = 1 := by
  haveI : Subsingleton (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ 0}) := by
    rw [pow_zero, Ideal.span_singleton_one]; infer_instance
  exact l0_of_subsingleton _

/-- `ℓ_1(ℤ/2^e) = 2` for `e ≥ 2` (Part F sketch of `C34_bais_counts.md`). -/
theorem l1_Q {e : ℕ} (he : 2 ≤ e) : l1 (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ e}) = 2 :=
  l1_of_surj (Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ e})).toAddMonoidHom
    Ideal.Quotient.mk_surjective fun x hx => by
    have h1 := (mkQ_eq_zero e x).1 hx
    exact (show (4 : ℤ_[2]) = 2 ^ 2 by norm_num) ▸ (pow_dvd_pow 2 he).trans h1

/-- `ℓ_1(ℤ/2^e) = 1` for `e ≤ 1` (Part F sketch of `C34_bais_counts.md`). -/
theorem l1_Q_le_one {e : ℕ} (he : e ≤ 1) : l1 (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ e}) = 1 := by
  refine l1_of_two_smul _ fun x => ?_
  induction x using Submodule.Quotient.induction_on
  rename_i y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton,
    nsmul_eq_mul]
  exact (pow_dvd_pow 2 he).trans ⟨y, by push_cast; ring⟩

end BaiCounts
