module

public import RequestProject.PodiumCor.Defs

/-!
# `C36_the_podium_corollary.md`: Part D — the layers

Encodings as in `PodiumCor/Defs.lean`: `layer G j = |2^j G / 2^{j+1} G|` (with C34's `twoPow`),
`ℤ_[2]` is `PadicInt 2`, `FamilyGroup.Q e = ℤ_[2] ⧸ Ideal.span {2 ^ e}` (C16).
-/

@[expose] public section

namespace PodiumCor

open Finset BaiCounts

/-- `layer G j = |G ⧸ {x | 2^j x ∈ 2^{j+1} G}|`, through the surjection `x ↦ [2^j x]` (auxiliary
for Part D of `C36_the_podium_corollary.md`). -/
lemma layer_eq (G : Type*) [AddCommGroup G] (j : ℕ) :
    layer G j = Nat.card (G ⧸ (twoPow G (j + 1)).comap (nsmulAddMonoidHom (α := G) (2 ^ j))) := by
  let g : G →+ twoPow G j :=
    { toFun := fun x => ⟨2 ^ j • x, ⟨x, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [smul_add] }
  let f : G →+ twoPow G j ⧸ (twoPow G (j + 1)).addSubgroupOf (twoPow G j) :=
    (QuotientAddGroup.mk' _).comp g
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨⟨w, ⟨y, rfl⟩⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    exact ⟨y, by simp [f, g]⟩
  rw [layer, card_quot_of_surj f hf]
  intro x
  simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap]
  rfl

/-- **(D0)** of `C36_the_podium_corollary.md`, first part: `layer G 0 = ℓ_0(G)` (C34 `l0`). -/
theorem D0_zero (G : Type*) [AddCommGroup G] : layer G 0 = l0 G := by
  rw [layer_eq, l0]
  congr 2
  ext x
  simp

/-- **(D0)** of `C36_the_podium_corollary.md`, second part: `layer G 1 = ℓ_1(G)` (C34 `l1`). -/
theorem D0_one (G : Type*) [AddCommGroup G] : layer G 1 = l1 G := rfl

/-- **(D0)** of `C36_the_podium_corollary.md`: `layer G 0 = l0 G` and `layer G 1 = l1 G`. -/
theorem D0 (G : Type*) [AddCommGroup G] : layer G 0 = l0 G ∧ layer G 1 = l1 G :=
  ⟨D0_zero G, D0_one G⟩

/-- **(D1)** of `C36_the_podium_corollary.md`: `layer` is invariant under `≃+`. -/
theorem layer_congr {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (j : ℕ) :
    layer G j = layer H j := by
  rw [layer_eq, layer_eq]
  refine (card_quot_congr e _ _ fun x => ?_).symm
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply]
  rw [mem_twoPow_equiv e, map_nsmul]

/-- **(D1)** of `C36_the_podium_corollary.md`: `layer (G × H) j = layer G j * layer H j`. -/
theorem layer_prod (G H : Type*) [AddCommGroup G] [AddCommGroup H] (j : ℕ) :
    layer (G × H) j = layer G j * layer H j := by
  rw [layer_eq, layer_eq, layer_eq]
  refine card_quot_prod _ _ _ fun x => ?_
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply]
  exact mem_twoPow_prod _ _

/-- **(D1)** of `C36_the_podium_corollary.md`: for a `Fintype` index,
`layer (Π i, G i) j = Π_i layer (G i) j`. -/
theorem layer_pi {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, AddCommGroup (G i)] (j : ℕ) :
    layer (∀ i, G i) j = ∏ i, layer (G i) j := by
  rw [layer_eq]
  simp_rw [layer_eq]
  refine card_quot_pi _ _ fun x => ?_
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply]
  exact mem_twoPow_pi _ _

/-- If `π : ℤ_[2] →+ G` is surjective with kernel inside `2^{j+1} ℤ_[2]`, then `layer G j = 2`
(auxiliary for (D1) of `C36_the_podium_corollary.md`). -/
lemma layer_of_surj {G : Type*} [AddCommGroup G] (j : ℕ) (π : ℤ_[2] →+ G)
    (hπ : Function.Surjective π) (hker : ∀ x, π x = 0 → (2 : ℤ_[2]) ^ (j + 1) ∣ x) :
    layer G j = 2 := by
  rw [layer_eq]
  refine card_eq_two ((QuotientAddGroup.mk' _).comp π)
    ((QuotientAddGroup.mk'_surjective _).comp hπ) fun x => ?_
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, mem_twoPow]
  have h2j : (2 : ℤ_[2]) ^ j ≠ 0 := pow_ne_zero _ two_ne_zero
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hπ y
    have h0 : π (2 ^ j * x - 2 ^ (j + 1) * z) = 0 := by
      rw [map_sub, show (2 : ℤ_[2]) ^ j * x = (2 ^ j : ℕ) • x by rw [nsmul_eq_mul]; norm_num,
        show (2 : ℤ_[2]) ^ (j + 1) * z = (2 ^ (j + 1) : ℕ) • z by rw [nsmul_eq_mul]; norm_num,
        map_nsmul, map_nsmul, hy, sub_self]
    obtain ⟨c, hc⟩ := hker _ h0
    have h2 : (2 : ℤ_[2]) ^ j * (x - 2 * (c + z)) = 0 := by
      rw [pow_succ] at hc; linear_combination hc
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h h2j
    · exact ⟨c + z, by linear_combination h⟩
  · rintro ⟨w, rfl⟩
    exact ⟨π w, by rw [← map_nsmul, ← map_nsmul, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring_nf⟩

/-- If `2^j G = 0` then `layer G j = 1` (auxiliary for (D1) of `C36_the_podium_corollary.md`). -/
lemma layer_of_smul_eq_zero (G : Type*) [AddCommGroup G] (j : ℕ) (h : ∀ x : G, 2 ^ j • x = 0) :
    layer G j = 1 := by
  rw [layer_eq, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
  induction a using QuotientAddGroup.induction_on
  induction b using QuotientAddGroup.induction_on
  rename_i a b
  rw [QuotientAddGroup.eq]
  simp only [AddSubgroup.mem_comap, nsmulAddMonoidHom_apply, h]
  exact (twoPow G (j + 1)).zero_mem

/-- **(D1)** of `C36_the_podium_corollary.md`: `layer ℤ_[2] j = 2`. -/
theorem layer_padic (j : ℕ) : layer ℤ_[2] j = 2 :=
  layer_of_surj j (AddMonoidHom.id _) Function.surjective_id
    (fun x hx => by simp [show x = 0 from hx])

/-- **(D1)** of `C36_the_podium_corollary.md`:
`layer (Q e) j = if j < e then 2 else 1`, with `Q e = ℤ_[2] ⧸ Ideal.span {2 ^ e}` (C16). -/
theorem layer_Q (e j : ℕ) : layer (FamilyGroup.Q e) j = if j < e then 2 else 1 := by
  split_ifs with h
  · exact layer_of_surj j (Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2]) ^ e})).toAddMonoidHom
      Ideal.Quotient.mk_surjective fun x hx =>
        (pow_dvd_pow 2 (by omega)).trans ((mkQ_eq_zero e x).1 hx)
  · refine layer_of_smul_eq_zero _ _ fun x => ?_
    induction x using Submodule.Quotient.induction_on
    rename_i y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton,
      nsmul_eq_mul]
    exact (pow_dvd_pow 2 (show e ≤ j by omega)).trans ⟨y, by push_cast; ring⟩

/-- **(D1)** of `C36_the_podium_corollary.md`, all items together: invariance under `≃+`,
products, finite products, `layer ℤ_[2] j = 2` and `layer (Q e) j = if j < e then 2 else 1`. -/
theorem D1 :
    (∀ {G H : Type} [AddCommGroup G] [AddCommGroup H] (_ : G ≃+ H) (j : ℕ),
      layer G j = layer H j) ∧
    (∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (j : ℕ),
      layer (G × H) j = layer G j * layer H j) ∧
    (∀ {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] (j : ℕ),
      layer (∀ i, G i) j = ∏ i, layer (G i) j) ∧
    (∀ j, layer ℤ_[2] j = 2) ∧
    (∀ e j, layer (FamilyGroup.Q e) j = if j < e then 2 else 1) :=
  ⟨fun e j => layer_congr e j, fun G H _ _ j => layer_prod G H j,
    fun G _ j => layer_pi G j, layer_padic, layer_Q⟩

end PodiumCor
