module

public import RequestProject.Stability.Basic
public import Mathlib

/-!
# `C44_stability_and_rigidity.md`, Part S — the stability lemma, abstract (Lemma 10.11)

Namespace `Stability`. Here `n` is a `Fintype` with `DecidableEq`, `S : n → n → Prop` is
reflexive (`hrefl`) and transitive (`htrans`), and `ν : n → n → ℕ` satisfies `ν i i = 0`
(`hνd`) and `ν i j ≤ ν i u + ν u j` whenever `S i u` and `S u j` (`htri`). The decidability of
`S` assumed in the file is not needed (the proofs are classical), so it is left out.

* (S0) `S0` (collecting `one_mem_Wt`, `add_mem_Wt`, `neg_mem_Wt`, `smul_mem_Wt`, `mul_mem_Wt`,
  `Wt_succ_subset`).
* (S1) `S1`, for every `s ≥ 1`.
* (S2) `S2`, for every `s ≥ 1`.
-/

@[expose] public section

noncomputable section

namespace Stability

open Matrix Finset

variable {n : Type*} {S : n → n → Prop} {ν : n → n → ℕ}

/-! ### Elementary bounds -/

lemma two_zpow_neg_nat_pos (a : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (-(a : ℤ)) := by positivity

lemma two_zpow_neg_nat_le_one (a : ℕ) : (2 : ℝ) ^ (-(a : ℤ)) ≤ 1 :=
  zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

lemma two_zpow_neg_nat_anti {a b : ℕ} (h : a ≤ b) :
    (2 : ℝ) ^ (-(b : ℤ)) ≤ (2 : ℝ) ^ (-(a : ℤ)) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)

lemma two_zpow_neg_nat_add (a b : ℕ) :
    (2 : ℝ) ^ (-(a : ℤ)) * (2 : ℝ) ^ (-(b : ℤ)) = (2 : ℝ) ^ (-((a + b : ℕ) : ℤ)) := by
  rw [← zpow_add₀ two_ne_zero]; push_cast; ring_nf

/-! ### (S0) The weighted ring -/

/-- (S0) of `C44_stability_and_rigidity.md`: `1 ∈ Wt S ν 0`. -/
lemma one_mem_Wt [DecidableEq n] (hrefl : ∀ i, S i i) (hνd : ∀ i, ν i i = 0) :
    (1 : Matrix n n ℚ_[2]) ∈ Wt S ν 0 := by
  intro i j
  by_cases h : i = j
  · subst h
    refine ⟨fun h' => absurd (hrefl i) h', ?_⟩
    simp [hνd]
  · refine ⟨fun _ => one_apply_ne h, ?_⟩
    rw [one_apply_ne h, norm_zero]; positivity

/-- (S0) of `C44_stability_and_rigidity.md`: `Wt S ν s` is closed under `+`. -/
lemma add_mem_Wt {s : ℕ} {X Y : Matrix n n ℚ_[2]} (hX : X ∈ Wt S ν s) (hY : Y ∈ Wt S ν s) :
    X + Y ∈ Wt S ν s := by
  intro i j
  refine ⟨fun h => by rw [add_apply, (hX i j).1 h, (hY i j).1 h, add_zero], ?_⟩
  rw [add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j).2 (hY i j).2)

/-- (S0) of `C44_stability_and_rigidity.md`: `Wt S ν s` is closed under negation. -/
lemma neg_mem_Wt {s : ℕ} {X : Matrix n n ℚ_[2]} (hX : X ∈ Wt S ν s) : -X ∈ Wt S ν s := by
  intro i j
  refine ⟨fun h => by rw [neg_apply, (hX i j).1 h, neg_zero], ?_⟩
  rw [neg_apply, norm_neg]; exact (hX i j).2

/-- (S0) of `C44_stability_and_rigidity.md`: `Wt S ν s` is closed under multiplication by
scalars `a` with `‖a‖ ≤ 1`. -/
lemma smul_mem_Wt {s : ℕ} {a : ℚ_[2]} (ha : ‖a‖ ≤ 1) {X : Matrix n n ℚ_[2]}
    (hX : X ∈ Wt S ν s) : a • X ∈ Wt S ν s := by
  intro i j
  refine ⟨fun h => by rw [smul_apply, (hX i j).1 h, smul_zero], ?_⟩
  rw [smul_apply, smul_eq_mul, norm_mul]
  calc ‖a‖ * ‖X i j‖ ≤ 1 * ‖X i j‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact (hX i j).2

/-- (S0) of `C44_stability_and_rigidity.md`: `X ∈ Wt S ν s`, `Y ∈ Wt S ν t` imply
`X * Y ∈ Wt S ν (s + t)`. -/
lemma mul_mem_Wt [Fintype n] (htrans : ∀ i u j, S i u → S u j → S i j)
    (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j) {s t : ℕ}
    {X Y : Matrix n n ℚ_[2]} (hX : X ∈ Wt S ν s) (hY : Y ∈ Wt S ν t) :
    X * Y ∈ Wt S ν (s + t) := by
  intro i j
  constructor
  · intro hij
    rw [mul_apply]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : S i u
    · by_cases h2 : S u j
      · exact absurd (htrans i u j h1 h2) hij
      · rw [(hY u j).1 h2, mul_zero]
    · rw [(hX i u).1 h1, zero_mul]
  · rw [mul_apply]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro u _
    by_cases h : S i u ∧ S u j
    · rw [norm_mul]
      calc ‖X i u‖ * ‖Y u j‖ ≤ (2 : ℝ) ^ (-((ν i u + s : ℕ) : ℤ)) *
            (2 : ℝ) ^ (-((ν u j + t : ℕ) : ℤ)) :=
            mul_le_mul (hX i u).2 (hY u j).2 (norm_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ (-((ν i u + s + (ν u j + t) : ℕ) : ℤ)) := two_zpow_neg_nat_add _ _
        _ ≤ _ := two_zpow_neg_nat_anti (by have := htri i u j h.1 h.2; omega)
    · have : X i u * Y u j = 0 := by
        by_cases h1 : S i u
        · rw [(hY u j).1 (fun h2 => h ⟨h1, h2⟩), mul_zero]
        · rw [(hX i u).1 h1, zero_mul]
      rw [this, norm_zero]; positivity

/-- (S0) of `C44_stability_and_rigidity.md`: `Wt S ν (s + 1) ⊆ Wt S ν s`. -/
lemma Wt_succ_subset (s : ℕ) : Wt S ν (s + 1) ⊆ Wt S ν s := by
  intro X hX i j
  exact ⟨(hX i j).1, (hX i j).2.trans (two_zpow_neg_nat_anti (by omega))⟩

/-- Iterated (S0): `Wt S ν t ⊆ Wt S ν s` for `s ≤ t`. -/
lemma Wt_mono {s t : ℕ} (h : s ≤ t) : Wt S ν t ⊆ Wt S ν s := by
  intro X hX i j
  exact ⟨(hX i j).1, (hX i j).2.trans (two_zpow_neg_nat_anti (by omega))⟩

/-- **(S0) The weighted ring** of `C44_stability_and_rigidity.md`, Part S: `1 ∈ Wt S ν 0`;
`Wt S ν s` is closed under `+`, negation and multiplication by scalars of norm `≤ 1`;
`Wt S ν s * Wt S ν t ⊆ Wt S ν (s + t)`; `Wt S ν (s + 1) ⊆ Wt S ν s`. -/
theorem S0 [Fintype n] [DecidableEq n] (hrefl : ∀ i, S i i) (htrans : ∀ i u j, S i u → S u j → S i j)
    (hνd : ∀ i, ν i i = 0) (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j) :
    (1 : Matrix n n ℚ_[2]) ∈ Wt S ν 0 ∧
    (∀ s, ∀ X ∈ Wt S ν s, ∀ Y ∈ Wt S ν s, X + Y ∈ Wt S ν s) ∧
    (∀ s, ∀ X ∈ Wt S ν s, -X ∈ Wt S ν s) ∧
    (∀ s, ∀ a : ℚ_[2], ‖a‖ ≤ 1 → ∀ X ∈ Wt S ν s, a • X ∈ Wt S ν s) ∧
    (∀ s t, ∀ X ∈ Wt S ν s, ∀ Y ∈ Wt S ν t, X * Y ∈ Wt S ν (s + t)) ∧
    (∀ s, Wt S ν (s + 1) ⊆ Wt S ν s) :=
  ⟨one_mem_Wt hrefl hνd, fun _ _ hX _ hY => add_mem_Wt hX hY, fun _ _ hX => neg_mem_Wt hX,
    fun _ _ ha _ hX => smul_mem_Wt ha hX, fun _ _ _ hX _ hY => mul_mem_Wt htrans htri hX hY,
    Wt_succ_subset⟩

lemma zero_mem_Wt (s : ℕ) : (0 : Matrix n n ℚ_[2]) ∈ Wt S ν s := by
  intro i j; refine ⟨fun _ => rfl, ?_⟩; rw [zero_apply, norm_zero]; positivity

lemma sub_mem_Wt {s : ℕ} {X Y : Matrix n n ℚ_[2]} (hX : X ∈ Wt S ν s) (hY : Y ∈ Wt S ν s) :
    X - Y ∈ Wt S ν s := by
  rw [sub_eq_add_neg]; exact add_mem_Wt hX (neg_mem_Wt hY)

lemma sum_mem_Wt {s : ℕ} {ι : Type*} (t : Finset ι) (f : ι → Matrix n n ℚ_[2])
    (hf : ∀ i ∈ t, f i ∈ Wt S ν s) : ∑ i ∈ t, f i ∈ Wt S ν s :=
  Finset.sum_induction _ (· ∈ Wt S ν s) (fun _ _ => add_mem_Wt) (zero_mem_Wt s) hf

lemma pow_mem_Wt [Fintype n] [DecidableEq n] (hrefl : ∀ i, S i i) (htrans : ∀ i u j, S i u → S u j → S i j)
    (hνd : ∀ i, ν i i = 0) (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j)
    {X : Matrix n n ℚ_[2]} (hX : X ∈ Wt S ν 0) (k : ℕ) : X ^ k ∈ Wt S ν 0 := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_Wt hrefl hνd
  | succ k ih => rw [pow_succ]; simpa using mul_mem_Wt htrans htri ih hX

/-! ### Inverses in a weighted subalgebra (Cayley–Hamilton) -/

/-- The integral lift of a matrix with entries of norm `≤ 1`. -/
def liftZ (X : Matrix n n ℚ_[2]) (h : ∀ i j, ‖X i j‖ ≤ 1) : Matrix n n ℤ_[2] :=
  Matrix.of fun i j => ⟨X i j, h i j⟩

lemma liftZ_map (X : Matrix n n ℚ_[2]) (h : ∀ i j, ‖X i j‖ ≤ 1) :
    (liftZ X h).map (PadicInt.Coe.ringHom) = X := by
  ext i j; rfl

/-- If `X` lies in a set `P` of matrices closed under `1`, `+`, `*` and scalars of norm `≤ 1`,
has entries of norm `≤ 1` and `‖det X‖ = 1`, then `X⁻¹ ∈ P` (by Cayley–Hamilton). -/
lemma inv_mem_of_closed [Fintype n] [DecidableEq n] (P : Set (Matrix n n ℚ_[2])) (h1 : (1 : Matrix n n ℚ_[2]) ∈ P)
    (hadd : ∀ X ∈ P, ∀ Y ∈ P, X + Y ∈ P) (hmul : ∀ X ∈ P, ∀ Y ∈ P, X * Y ∈ P)
    (hsmul : ∀ a : ℚ_[2], ‖a‖ ≤ 1 → ∀ X ∈ P, a • X ∈ P)
    (X : Matrix n n ℚ_[2]) (hX : X ∈ P) (hent : ∀ i j, ‖X i j‖ ≤ 1) (hdet : ‖X.det‖ = 1) :
    X⁻¹ ∈ P := by
  set p := X.charpoly with hp_def
  have hp : p = (liftZ X hent).charpoly.map PadicInt.Coe.ringHom := by
    rw [hp_def, ← charpoly_map, liftZ_map]
  have hcoef : ∀ k, ‖p.coeff k‖ ≤ 1 := by
    intro k; rw [hp, Polynomial.coeff_map]; exact PadicInt.norm_le_one _
  have hc0 : ‖p.coeff 0‖ = 1 := by
    rw [det_eq_sign_charpoly_coeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at hdet
    exact hdet
  have hzero : (0 : Matrix n n ℚ_[2]) ∈ P := by simpa using hsmul 0 (by simp) 1 h1
  have hpow : ∀ k : ℕ, X ^ k ∈ P := by
    intro k; induction k with
    | zero => rw [pow_zero]; exact h1
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hX
  set d := p.natDegree
  set Q : Matrix n n ℚ_[2] := ∑ k ∈ range d, p.coeff (k + 1) • X ^ k with hQ
  have hQP : Q ∈ P :=
    Finset.sum_induction _ (· ∈ P) (fun a b ha hb => hadd a ha b hb) hzero
      (fun k _ => hsmul _ (hcoef _) _ (hpow k))
  have hXQ : X * Q = -(p.coeff 0) • (1 : Matrix n n ℚ_[2]) := by
    have h0 := aeval_self_charpoly X
    rw [← hp_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ'] at h0
    rw [hQ, Finset.mul_sum]
    have : ∀ k ∈ range d, X * (p.coeff (k + 1) • X ^ k) = p.coeff (k + 1) • X ^ (k + 1) := by
      intro k _; rw [mul_smul_comm, pow_succ']
    rw [Finset.sum_congr rfl this, neg_smul, eq_neg_iff_add_eq_zero]
    simpa using h0
  have hc0ne : p.coeff 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hc0; exact zero_ne_one hc0
  have hinv : X⁻¹ = (-(p.coeff 0)⁻¹) • Q := by
    apply inv_eq_right_inv
    rw [mul_smul_comm, hXQ, smul_smul]
    rw [show -(p.coeff 0)⁻¹ * -p.coeff 0 = 1 by field_simp, one_smul]
  rw [hinv]
  refine hsmul _ ?_ _ hQP
  rw [norm_neg, norm_inv, hc0, inv_one]

/-- `‖det (1 + N)‖ = 1` when every entry of `N` has norm `< 1` (reduction modulo `2`). -/
lemma norm_det_one_add [Fintype n] [DecidableEq n] (N : Matrix n n ℚ_[2]) (hN : ∀ i j, ‖N i j‖ < 1) :
    ‖(1 + N).det‖ = 1 := by
  set N' := liftZ N (fun i j => (hN i j).le)
  have hmap : (1 + N').map (PadicInt.Coe.ringHom) = 1 + N := by
    have : (1 + N').map PadicInt.Coe.ringHom = (PadicInt.Coe.ringHom).mapMatrix (1 + N') := rfl
    rw [this, map_add, map_one, RingHom.mapMatrix_apply, liftZ_map]
  have hdet : (1 + N).det = ((1 + N').det : ℚ_[2]) := by
    rw [← hmap]
    exact (RingHom.map_det PadicInt.Coe.ringHom (1 + N')).symm
  have hN0 : (PadicInt.toZMod (p := 2)).mapMatrix N' = 0 := by
    ext i j
    rw [RingHom.mapMatrix_apply, map_apply, zero_apply, ← RingHom.mem_ker, PadicInt.ker_toZMod,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
    exact hN i j
  have hmod : PadicInt.toZMod (1 + N').det = 1 := by
    rw [RingHom.map_det, map_add, map_one, hN0, add_zero, det_one]
  have hunit : IsUnit (1 + N').det := by
    by_contra h
    have hm : (1 + N').det ∈ RingHom.ker (PadicInt.toZMod (p := 2)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h
    rw [RingHom.mem_ker, hmod] at hm
    exact one_ne_zero hm
  rw [hdet]
  exact PadicInt.isUnit_iff.1 hunit

/-! ### (S1) Stability -/

/-- `B ⊙ E`, the entrywise product. -/
def hprod (B E : Matrix n n ℚ_[2]) : Matrix n n ℚ_[2] := Matrix.of fun i j => B i j * E i j

lemma hadOne_eq (B E : Matrix n n ℚ_[2]) : hadOne B E = B + hprod B E := by
  ext i j; simp [hadOne, hprod, mul_add]

lemma hprod_mem_Wt {s : ℕ} {B E : Matrix n n ℚ_[2]} (hB : B ∈ Wt S ν 0)
    (hE : ∀ i j, ‖E i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ))) : hprod B E ∈ Wt S ν s := by
  intro i j
  refine ⟨fun h => by simp [hprod, (hB i j).1 h], ?_⟩
  simp only [hprod, of_apply, norm_mul]
  calc ‖B i j‖ * ‖E i j‖ ≤ (2 : ℝ) ^ (-((ν i j + 0 : ℕ) : ℤ)) * (2 : ℝ) ^ (-(s : ℤ)) :=
        mul_le_mul (hB i j).2 (hE i j) (norm_nonneg _) (by positivity)
    _ = _ := by rw [two_zpow_neg_nat_add]; simp

/-- **(S1) Stability** of `C44_stability_and_rigidity.md`, Part S (Lemma 10.11, abstract, for
every `s ≥ 1`): if `A ∈ Wt S ν 0` with `‖A i j‖ = 2^{−ν i j}` whenever `S i j`, `B ∈ Wt S ν 0`
with `A * B = 1`, and `‖E i j‖ ≤ 2^{−s}` for all `i, j`, then `hadOne B E` (that is,
`B ∘ (1 + E)`) has unit determinant and `(hadOne B E)⁻¹ = hadOne A E'` for some `E'` with
`‖E' i j‖ ≤ 2^{−s}` for all `i, j`. -/
theorem S1 [Fintype n] [DecidableEq n] (hrefl : ∀ i, S i i)
    (htrans : ∀ i u j, S i u → S u j → S i j)
    (hνd : ∀ i, ν i i = 0) (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j)
    {s : ℕ} (hs : 1 ≤ s) {A B E : Matrix n n ℚ_[2]} (hA : A ∈ Wt S ν 0)
    (hAn : ∀ i j, S i j → ‖A i j‖ = (2 : ℝ) ^ (-(ν i j : ℤ))) (hB : B ∈ Wt S ν 0)
    (hAB : A * B = 1) (hE : ∀ i j, ‖E i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ))) :
    IsUnit (hadOne B E).det ∧ ∃ E' : Matrix n n ℚ_[2], (hadOne B E)⁻¹ = hadOne A E' ∧
      ∀ i j, ‖E' i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ)) := by
  classical
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  set C := hprod B E
  have hC : C ∈ Wt S ν s := hprod_mem_Wt hB hE
  set N := A * C
  have hN : N ∈ Wt S ν s := by simpa using mul_mem_Wt htrans htri hA hC
  have hH : hadOne B E = B * (1 + N) := by
    rw [hadOne_eq, mul_add, mul_one, ← mul_assoc, hBA, one_mul]
  have hX : (1 + N) ∈ Wt S ν 0 := add_mem_Wt (one_mem_Wt hrefl hνd) (Wt_mono (Nat.zero_le _) hN)
  have hNlt : ∀ i j, ‖N i j‖ < 1 := by
    intro i j
    calc ‖N i j‖ ≤ (2 : ℝ) ^ (-((ν i j + s : ℕ) : ℤ)) := (hN i j).2
      _ ≤ (2 : ℝ) ^ (-((1 : ℕ) : ℤ)) := two_zpow_neg_nat_anti (by omega)
      _ < 1 := by norm_num
  have hdetX : ‖(1 + N).det‖ = 1 := norm_det_one_add N hNlt
  have hent : ∀ i j, ‖(1 + N) i j‖ ≤ 1 :=
    fun i j => (hX i j).2.trans (two_zpow_neg_nat_le_one _)
  have hdetB : IsUnit B.det := by
    have := congrArg Matrix.det hAB
    rw [det_mul, det_one] at this
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul_eq_one this)
  have hdetX' : IsUnit (1 + N).det := by
    rw [isUnit_iff_ne_zero]; intro h; rw [h, norm_zero] at hdetX; exact zero_ne_one hdetX
  have hunit : IsUnit (hadOne B E).det := by rw [hH, det_mul]; exact hdetB.mul hdetX'
  refine ⟨hunit, ?_⟩
  set Y := (1 + N)⁻¹
  have hY : Y ∈ Wt S ν 0 :=
    inv_mem_of_closed (Wt S ν 0) (one_mem_Wt hrefl hνd) (fun _ hX _ hY => add_mem_Wt hX hY)
      (fun _ hX _ hY => by simpa using mul_mem_Wt htrans htri hX hY)
      (fun _ ha _ hX => smul_mem_Wt ha hX) _ hX hent hdetX
  have hXY : (1 + N) * Y = 1 := mul_nonsing_inv _ hdetX'
  have hBinv : B⁻¹ = A := inv_eq_right_inv hBA
  set R := N * Y * A
  have hR : R ∈ Wt S ν s := by
    simpa using mul_mem_Wt htrans htri (mul_mem_Wt htrans htri hN hY) hA
  have hinv : (hadOne B E)⁻¹ = A - R := by
    rw [hH, Matrix.mul_inv_rev, hBinv]
    have : Y = 1 - N * Y := by
      rw [eq_sub_iff_add_eq]; nth_rw 1 [← Matrix.one_mul Y]; rw [← Matrix.add_mul, hXY]
    change Y * A = A - N * Y * A
    conv_lhs => rw [this]
    rw [sub_mul, one_mul]
  refine ⟨Matrix.of fun i j => if S i j then -R i j / A i j else 0, ?_, ?_⟩
  · rw [hinv]
    ext i j
    simp only [hadOne, of_apply, sub_apply]
    by_cases h : S i j
    · rw [if_pos h]
      have hA0 : A i j ≠ 0 := by
        intro h0; have := hAn i j h; rw [h0, norm_zero] at this
        exact (two_zpow_neg_nat_pos _).ne this
      field_simp
      ring
    · rw [if_neg h, (hA i j).1 h, (hR i j).1 h]; ring
  · intro i j
    simp only [of_apply]
    split_ifs with h
    · rw [norm_div, norm_neg, hAn i j h,
        div_le_iff₀ (two_zpow_neg_nat_pos _), two_zpow_neg_nat_add, add_comm]
      exact (hR i j).2
    · rw [norm_zero]; positivity

/-! ### (S2) With diagonal scalings -/

lemma diagonal_hadOne_diagonal [Fintype n] [DecidableEq n] (x y : n → ℚ_[2])
    (Y E : Matrix n n ℚ_[2]) :
    diagonal x * hadOne Y E * diagonal y = hadOne (diagonal x * Y * diagonal y) E := by
  ext i j
  simp [hadOne, diagonal_mul, mul_diagonal]
  ring

/-- **(S2) With diagonal scalings** of `C44_stability_and_rigidity.md`, Part S (the paper's
Lemma 10.11 is the case `s = 1`): in the setting of (S1), for `d₁ d₂ : n → ℚ_[2]` with all values
non-zero and `M := diagonal d₁ * A * diagonal d₂`: `IsUnit M.det`, `IsUnit (hadOne M⁻¹ E).det`,
and `(hadOne M⁻¹ E)⁻¹ = hadOne M E'` for some `E'` with `‖E' i j‖ ≤ 2^{−s}` for all `i, j`. -/
theorem S2 [Fintype n] [DecidableEq n] (hrefl : ∀ i, S i i)
    (htrans : ∀ i u j, S i u → S u j → S i j)
    (hνd : ∀ i, ν i i = 0) (htri : ∀ i u j, S i u → S u j → ν i j ≤ ν i u + ν u j)
    {s : ℕ} (hs : 1 ≤ s) {A B E : Matrix n n ℚ_[2]} (hA : A ∈ Wt S ν 0)
    (hAn : ∀ i j, S i j → ‖A i j‖ = (2 : ℝ) ^ (-(ν i j : ℤ))) (hB : B ∈ Wt S ν 0)
    (hAB : A * B = 1) (hE : ∀ i j, ‖E i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ)))
    (d₁ d₂ : n → ℚ_[2]) (hd₁ : ∀ i, d₁ i ≠ 0) (hd₂ : ∀ i, d₂ i ≠ 0) :
    IsUnit (diagonal d₁ * A * diagonal d₂).det ∧
      IsUnit (hadOne (diagonal d₁ * A * diagonal d₂)⁻¹ E).det ∧
      ∃ E' : Matrix n n ℚ_[2],
        (hadOne (diagonal d₁ * A * diagonal d₂)⁻¹ E)⁻¹ = hadOne (diagonal d₁ * A * diagonal d₂) E' ∧
        ∀ i j, ‖E' i j‖ ≤ (2 : ℝ) ^ (-(s : ℤ)) := by
  obtain ⟨hu, E', hE', hb⟩ := S1 hrefl htrans hνd htri hs hA hAn hB hAB hE
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have hd1 : diagonal d₁ * diagonal d₁⁻¹ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd₁ i)
  have hd2 : diagonal d₂ * diagonal d₂⁻¹ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd₂ i)
  have hd1' : diagonal d₁⁻¹ * diagonal d₁ = 1 := mul_eq_one_comm.1 hd1
  have hd2' : diagonal d₂⁻¹ * diagonal d₂ = 1 := mul_eq_one_comm.1 hd2
  set M := diagonal d₁ * A * diagonal d₂
  have hMinv' : M * (diagonal d₂⁻¹ * B * diagonal d₁⁻¹) = 1 := by
    simp only [M, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal d₂), hd2, Matrix.one_mul, ← Matrix.mul_assoc A,  hAB,
      Matrix.one_mul, hd1]
  have hMinv : M⁻¹ = diagonal d₂⁻¹ * B * diagonal d₁⁻¹ := inv_eq_right_inv hMinv'
  have hMdet : IsUnit M.det := by
    have := congrArg Matrix.det hMinv'
    rw [det_mul, det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have hH : hadOne M⁻¹ E = diagonal d₂⁻¹ * hadOne B E * diagonal d₁⁻¹ := by
    rw [hMinv, diagonal_hadOne_diagonal]
  have hHdet : IsUnit (hadOne M⁻¹ E).det := by
    rw [hH, det_mul, det_mul]
    refine (IsUnit.mul ?_ hu).mul ?_
    · have := congrArg Matrix.det hd2'
      rw [det_mul, det_one] at this
      exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
    · have := congrArg Matrix.det hd1'
      rw [det_mul, det_one] at this
      exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  refine ⟨hMdet, hHdet, E', ?_, hb⟩
  apply inv_eq_right_inv
  rw [hH, show hadOne M E' = diagonal d₁ * (hadOne B E)⁻¹ * diagonal d₂ by
    rw [hE', diagonal_hadOne_diagonal]]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonal d₁⁻¹) (diagonal d₁), hd1', Matrix.one_mul,
    ← Matrix.mul_assoc (hadOne B E), mul_nonsing_inv _ hu, Matrix.one_mul, hd2']

end Stability
