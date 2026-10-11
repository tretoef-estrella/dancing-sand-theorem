module

public import RequestProject.OddParts.PartQ

/-!
# `C52_odd_parts.md`: auxiliary transport facts for Parts B and C

* `diagMap d`: the diagonal map `v ↦ (i ↦ d i * v i)` on `ι → ℤ`.
* `sylpDiagQuot`: the `p`-part of the cokernel of a diagonal map, the factors with `d i = 0` removed.
* `sylpTwoMul`: for `p` an odd prime, `Sylp p (Π i, ZMod (2 * k i)) ≃+ Sylp p (Π i, ZMod (k i))`.
* `piZModReindex`: reindexing a product of cyclic groups along an equivalence of index types.
* `idxB`, `idxC`: the groupings of the nonempty subsets by size (for (B1)) and of the nonempty
  even subsets by size (for (C5)).
-/

@[expose] public section

noncomputable section

namespace OddParts

open Finset

/-- The diagonal map `v ↦ (i ↦ d i * v i)`. -/
def diagMap {ι : Type*} (d : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun v i := (d i : ℤ) * v i
  map_add' v w := by funext i; simp [mul_add]
  map_smul' c v := by funext i; simp; ring

lemma diagMap_apply {ι : Type*} (d : ι → ℕ) (v : ι → ℤ) (i : ι) :
    diagMap d v i = (d i : ℤ) * v i := rfl

/-- The `p`-part of the cokernel of a diagonal map, with the factors where `d i = 0` removed. -/
theorem sylpDiagQuot {ι : Type*} (d : ι → ℕ) (D : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))
    (hD : ∀ v i, D v i = (d i : ℤ) * v i) (P : ι → Prop) [DecidablePred P]
    (hP : ∀ i, ¬ P i → d i = 0) {p : ℕ} (hp : p ≠ 0) :
    Nonempty (Sylp p ((ι → ℤ) ⧸ LinearMap.range D) ≃+
      Sylp p ((i : {i // P i}) → ZMod (d i))) :=
  ⟨(sylpCongr p ((diagQuotEquiv d D hD).toAddEquiv.trans (piSplit P (fun i => ZMod (d i))))).trans
    (sylpProdBotRight p _ _ (sylp_pi_zmod_zero (fun i : {i // ¬ P i} => d i)
      (fun i => hP i.1 i.2) hp))⟩

lemma not_dvd_two_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

lemma not_dvd_two_pow_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) : ¬ p ∣ 2 ^ k :=
  fun h => not_dvd_two_of_ne hp hp2 (hp.dvd_of_dvd_pow h)

/-- For `p` an odd prime, `Sylp p (Π i, ZMod (2 * k i)) ≃+ Sylp p (Π i, ZMod (k i))`. -/
theorem sylpTwoMul {ι : Type*} (k : ι → ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nonempty (Sylp p ((i : ι) → ZMod (2 * k i)) ≃+ Sylp p ((i : ι) → ZMod (k i))) := by
  have e2 := diagQuotEquiv (fun i => 2 * k i) (diagMap (fun i => 2 * k i)) (fun _ _ => rfl)
  have e1 := diagQuotEquiv k (diagMap k) (fun _ _ => rfl)
  obtain ⟨t⟩ := sylpQuotTransfer (LinearMap.range (diagMap (fun i => 2 * k i)))
    (LinearMap.range (diagMap k)) LinearMap.id ((2 : ℕ) • LinearMap.id)
    (by
      rintro _ ⟨v, rfl⟩
      refine ⟨(2 : ℕ) • v, ?_⟩
      funext i
      simp only [diagMap_apply, Pi.smul_apply, LinearMap.id_coe, id_eq]
      push_cast; ring)
    (by
      rintro _ ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      funext i
      simp only [diagMap_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, Pi.smul_apply]
      push_cast; ring)
    2 (fun _ => rfl) (fun _ => rfl) p hp (not_dvd_two_of_ne hp hp2)
  exact ⟨(sylpCongr p e2.symm.toAddEquiv).trans (t.trans (sylpCongr p e1.toAddEquiv))⟩

/-- Reindexing a product of cyclic groups along an equivalence of index types. -/
def piZModReindex {ι κ : Type*} (τ : κ ≃ ι) (d : ι → ℕ) (d' : κ → ℕ)
    (h : ∀ x, d (τ x) = d' x) : ((i : ι) → ZMod (d i)) ≃+ ((x : κ) → ZMod (d' x)) :=
  (LinearEquiv.piCongrLeft ℤ (fun i => ZMod (d i)) τ).symm.toAddEquiv.trans
    (AddEquiv.piCongrRight fun x => (ZMod.ringEquivCongr (h x)).toAddEquiv)

/-- Grouping the nonempty subsets of `Fin n` by their size `j + 1`. -/
def idxB1 (n : ℕ) :
    {S : Finset (Fin n) // S.Nonempty} ≃ (Σ j : Fin n, {S : Finset (Fin n) // S.card = j + 1}) where
  toFun S := ⟨⟨S.1.card - 1, by
      have h1 := S.1.card_le_univ; have h2 := S.2.card_pos; simp at h1; omega⟩,
    ⟨S.1, by have h2 := S.2.card_pos; simp; omega⟩⟩
  invFun x := ⟨x.2.1, Finset.card_pos.mp (by rw [x.2.2]; omega)⟩
  left_inv S := rfl
  right_inv x := by
    obtain ⟨j, S, hS⟩ := x
    refine Sigma.subtype_ext (Fin.ext ?_) rfl
    simp [hS]

/-- The index equivalence for (B1). -/
def idxB (n : ℕ) :
    (Σ j : Fin n, Fin (n.choose (j + 1))) ≃ {S : Finset (Fin n) // S.Nonempty} :=
  ((idxB1 n).trans (Equiv.sigmaCongrRight fun j =>
    Fintype.equivFinOfCardEq (by rw [Fintype.card_finset_len, Fintype.card_fin]))).symm

lemma idxB_card (n : ℕ) (x : Σ j : Fin n, Fin (n.choose (j + 1))) :
    (idxB n x).1.card = x.1 + 1 :=
  ((Fintype.equivFinOfCardEq (by rw [Fintype.card_finset_len, Fintype.card_fin] :
    Fintype.card {S : Finset (Fin n) // S.card = x.1 + 1} = n.choose (x.1 + 1))).symm x.2).2

/-- Grouping the nonempty even subsets of `Fin n` by their size `2 (t + 1)`. -/
def idxC1 (n : ℕ) :
    {S : EvenS n // S.1.Nonempty} ≃
      (Σ t : Fin (n / 2), {S : Finset (Fin n) // S.card = 2 * (t + 1)}) where
  toFun S := ⟨⟨S.1.1.card / 2 - 1, by
      have h1 := S.1.1.card_le_univ; have h2 := S.2.card_pos; obtain ⟨r, hr⟩ := S.1.2
      simp at h1; omega⟩,
    ⟨S.1.1, by have h2 := S.2.card_pos; obtain ⟨r, hr⟩ := S.1.2; simp; omega⟩⟩
  invFun x := ⟨⟨x.2.1, ⟨x.1 + 1, by rw [x.2.2]; ring⟩⟩,
    Finset.card_pos.mp (by rw [x.2.2]; omega)⟩
  left_inv S := rfl
  right_inv x := by
    obtain ⟨t, S, hS⟩ := x
    refine Sigma.subtype_ext (Fin.ext ?_) rfl
    simp [hS]

/-- The index equivalence for (C5). -/
def idxC (n : ℕ) :
    (Σ t : Fin (n / 2), Fin (n.choose (2 * (t + 1)))) ≃ {S : EvenS n // S.1.Nonempty} :=
  ((idxC1 n).trans (Equiv.sigmaCongrRight fun t =>
    Fintype.equivFinOfCardEq (by rw [Fintype.card_finset_len, Fintype.card_fin]))).symm

lemma idxC_card (n : ℕ) (x : Σ t : Fin (n / 2), Fin (n.choose (2 * (t + 1)))) :
    (idxC n x).1.1.card = 2 * (x.1 + 1) :=
  ((Fintype.equivFinOfCardEq (by rw [Fintype.card_finset_len, Fintype.card_fin] :
    Fintype.card {S : Finset (Fin n) // S.card = 2 * (x.1 + 1)} =
      n.choose (2 * (x.1 + 1)))).symm x.2).2

end OddParts
