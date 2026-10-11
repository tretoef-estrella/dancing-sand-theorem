module

public import RequestProject.CubeLaplacian.Cokernel
public import RequestProject.FoldGroup.PartK

/-!
# `C52_odd_parts.md`: Definitions (new)

Folder `RequestProject/OddParts/`, namespace `OddParts`. Reused without redefinition (Setting of the
file): C17 `CubeLaplacian.G`, `e`, `lap`, `L`, `coker`, `K`, `cokerEquivK`, `Syl2`; C38 `Fold.aElt`,
`Fold.Gbar`, `Fold.mk`, `Fold.lapBar`, `Fold.cokerBar`, `Fold.KBar`; C38b `FoldGroup.KBar_finite`,
`FoldGroup.cokerBarEquivKBar`.

Encodings:
* `Sylp p T` is the additive subgroup `{y | ∃ k, p ^ k • y = 0}` (the `p`-primary part).
* `chi n S g = (-1) ^ (Σ_{i ∈ S} (g i).val)` for `S : Finset (Fin n)`.
* `fourier n f S = Σ_g chi n S g * f g`, `ifourier n v g = Σ_S chi n S g * v S`,
  `diagD n v S = 2 * |S| * v S`.
* `EvenS n` is the subtype of subsets of even size.
* `chiBar n S` is `chi n S.1` passed to the quotient `Gbar n = G n ⧸ ⟨aElt n⟩` with
  `Quotient.lift` (well defined since `|S|` is even), so that `chiBar n S (mk n g) = chi n S.1 g`.
* `fourierBar`, `ifourierBar`, `diagDBar` are the same formulas on `Gbar n` and `EvenS n`.
-/

@[expose] public section

noncomputable section

namespace OddParts

open CubeLaplacian Finset

/-- Definitions (C52): the `p`-primary part of an abelian group: elements killed by a power of
`p`. -/
def Sylp (p : ℕ) (T : Type*) [AddCommGroup T] : AddSubgroup T where
  carrier := {y | ∃ k : ℕ, (p ^ k : ℕ) • y = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    show (p ^ (k + l) : ℕ) • (a + b) = 0
    have h1 : (p ^ (k + l) : ℕ) • a = 0 := by
      rw [pow_add, mul_nsmul, hk, nsmul_zero]
    have h2 : (p ^ (k + l) : ℕ) • b = 0 := by
      rw [pow_add, mul_comm, mul_nsmul, hl, nsmul_zero]
    rw [smul_add, h1, h2, add_zero]
  neg_mem' := by
    rintro a ⟨k, hk⟩
    exact ⟨k, by rw [smul_neg, hk, neg_zero]⟩

/-- Definitions (C52): the character `χ_S` of `G n = Fin n → ZMod 2`. -/
def chi (n : ℕ) (S : Finset (Fin n)) (g : CubeLaplacian.G n) : ℤ :=
  (-1) ^ (∑ i ∈ S, (g i).val)

/-- Definitions (C52): the Fourier map, `(fourier n f) S = Σ_g chi n S g * f g`. -/
def fourier (n : ℕ) : (CubeLaplacian.G n → ℤ) →ₗ[ℤ] (Finset (Fin n) → ℤ) where
  toFun f S := ∑ g, chi n S g * f g
  map_add' f f' := by funext S; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Definitions (C52): the inverse Fourier map (without division),
`(ifourier n v) g = Σ_S chi n S g * v S`. -/
def ifourier (n : ℕ) : (Finset (Fin n) → ℤ) →ₗ[ℤ] (CubeLaplacian.G n → ℤ) where
  toFun v g := ∑ S, chi n S g * v S
  map_add' f f' := by funext S; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Definitions (C52): the diagonal map `v ↦ (S ↦ 2|S| · v S)`. -/
def diagD (n : ℕ) : (Finset (Fin n) → ℤ) →ₗ[ℤ] (Finset (Fin n) → ℤ) where
  toFun v S := 2 * S.card * v S
  map_add' f f' := by funext S; simp [mul_add]
  map_smul' c f := by funext S; simp; ring

/-- Definitions (C52): the subsets of even size. -/
abbrev EvenS (n : ℕ) := {S : Finset (Fin n) // Even S.card}

lemma chi_const (n : ℕ) (S : Finset (Fin n)) (hS : Even S.card) (c : ZMod 2) :
    chi n S (fun _ => c) = 1 := by
  unfold chi
  rw [Finset.sum_const, smul_eq_mul, pow_mul, hS.neg_one_pow, one_pow]

lemma chi_add (n : ℕ) (S : Finset (Fin n)) (g h : CubeLaplacian.G n) :
    chi n S (g + h) = chi n S g * chi n S h := by
  simp only [chi, Pi.add_apply, ← pow_add,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  generalize g i = a
  generalize h i = b
  fin_cases a <;> fin_cases b <;> decide

/-- Definitions (C52): the character `χ_S` on `Gbar n`, for `|S|` even (it is constant on cosets of
`aElt n`); defined through the quotient, so that `chiBar n S (Fold.mk n g) = chi n S.1 g`. -/
def chiBar (n : ℕ) (S : EvenS n) : Fold.Gbar n → ℤ :=
  Quotient.lift (chi n S.1) (by
    intro a b hab
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.leftRel_apply.mp hab)
    have hb : b = a + k • Fold.aElt n := by rw [hk]; abel
    have hc : k • Fold.aElt n = fun _ => (k : ZMod 2) := by
      funext i; simp [Fold.aElt]
    rw [hb, chi_add, hc, chi_const n S.1 S.2, mul_one])

/-- Definitions (C52): `(fourierBar n u) S = Σ_x chiBar n S x * u x`. -/
def fourierBar (n : ℕ) : (Fold.Gbar n → ℤ) →ₗ[ℤ] (EvenS n → ℤ) where
  toFun u S := ∑ x, chiBar n S x * u x
  map_add' f f' := by funext S; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Definitions (C52): `(ifourierBar n v) x = Σ_S chiBar n S x * v S`. -/
def ifourierBar (n : ℕ) : (EvenS n → ℤ) →ₗ[ℤ] (Fold.Gbar n → ℤ) where
  toFun v x := ∑ S, chiBar n S x * v S
  map_add' f f' := by funext S; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    funext S
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Definitions (C52): `(diagDBar n v) S = 2 * S.1.card * v S`. -/
def diagDBar (n : ℕ) : (EvenS n → ℤ) →ₗ[ℤ] (EvenS n → ℤ) where
  toFun v S := 2 * S.1.card * v S
  map_add' f f' := by funext S; simp [mul_add]
  map_smul' c f := by funext S; simp; ring

end OddParts
