module

public import RequestProject.Bend.PartN
public import RequestProject.Bend.Aux

/-!
# `C50d_the_bend.md`: Part B — the bend (Lemma 10.20)

* `Nmat_eq_inv` (auxiliary): for a two-sided inverse `Y` of `Ξ` and `B ≥ l + 1`, `Nmat l B Y` is
  the inverse of the final matrix of `Ξ` (C42 `C109` and (N2)); used at `l = 0`.
* `B1_zero`, `B1_pos`: the cases `l = 0` and `l ≥ 1` of (B1), following the four steps of the
  file (C42 `C109` and C43 `P1` for `Σ₁`; C44 `F2`, `A3`; C45 `T_eta` and C44 `F1`; the window
  computation `core_real` with (W) and (Y1); the ultrametric inequality).
* (B1) `B1`, (B2) `B2`.
-/

@[expose] public section

noncomputable section

namespace Bend

open FormalOps FormalDance Finset Matrix

/-- Auxiliary for (B1) of `C50d_the_bend.md`: for `B ≥ l + 1`, `Ξ Y` with `Agree (Ξ * Y) 1`,
`Agree (Y * Ξ) 1` and `Gk` with `DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Gk`,
`Nmat l B Y = (finalM Gk)⁻¹` (C42 `C109` and (N2)). -/
lemma Nmat_eq_inv (l B : ℕ) (hB : l + 1 ≤ B) (Ξ Y : Bf ℚ_[2]) (hΞY : Agree (Ξ * Y) 1)
    (hYΞ : Agree (Y * Ξ) 1)
    (Gk : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hG : DanceRel (Families.ds l) 1 (fun _ _ => Ξ) Gk) :
    Nmat l B Y = (finalM Gk)⁻¹ := by
  obtain ⟨-, hC⟩ := InvFloors.C109 l B hB Ξ Y hΞY hYΞ Gk hG
  ext Y' X
  rw [N2 l B hB Y X Y']
  split_ifs with h
  · rw [(hC X Y').1 h]
  · rw [(hC X Y').2 (by omega)]

/-- Auxiliary for (B1) of `C50d_the_bend.md` (`l = 0`): for the empty word, `DanceRel` is
`MAgree`, so the final matrix reads the coefficient `0` at the floor `0`. -/
lemma finalM_nil {ds : List Bool} (hds : ds = []) (G : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2]))
    (Gk : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]))
    (h : DanceRel ds 1 G Gk) (s s' : Fin (Dance.slots ds 1)) :
    finalM Gk s s' = (G 0 0).coef 0 0 := by
  subst hds
  show (Gk s s').coef 0 0 = _
  rw [← h s s' 0 0 le_rfl]
  congr 2 <;> exact Subsingleton.elim _ _

/-- Auxiliary for (B1) of `C50d_the_bend.md` (`l = 0`): for the empty word a final matrix
exists (the system itself). -/
lemma danceRel_nil_exists {ds : List Bool} (hds : ds = []) (G : Matrix (Fin 1) (Fin 1) (Bf ℚ_[2])) :
    ∃ Gk : Matrix (Fin (Dance.slots ds 1)) (Fin (Dance.slots ds 1)) (Bf ℚ_[2]),
      DanceRel ds 1 G Gk := by
  subst hds
  exact ⟨G, fun _ _ _ _ _ => rfl⟩

/-- Auxiliary for (B1) of `C50d_the_bend.md` (`l = 0`): the inverse of a `1 × 1` matrix. -/
lemma inv_apply_of_subsingleton {n : Type*} [Fintype n] [DecidableEq n] [Subsingleton n]
    (A : Matrix n n ℚ_[2]) (a : ℚ_[2]) (ha : a ≠ 0) (hA : ∀ i j, A i j = a) (i j : n) :
    A⁻¹ i j = a⁻¹ := by
  have hinv : A⁻¹ = Matrix.of fun _ _ => a⁻¹ := by
    apply Matrix.inv_eq_right_inv
    ext x y
    obtain rfl : x = y := Subsingleton.elim _ _
    rw [Matrix.mul_apply, Fintype.sum_subsingleton _ x, Matrix.one_apply_eq, hA, Matrix.of_apply,
      mul_inv_cancel₀ ha]
  rw [hinv, Matrix.of_apply]

/-- The case `l = 0` of (B1) of `C50d_the_bend.md`: every matrix has size `1`, and the product
is `π(0) / (π(0) + t)`, of norm `2‖π(0)‖ ≤ 1/2`. -/
theorem B1_zero {B α c : ℕ} (hB : 0 + 1 ≤ B) (hα : 2 ≤ α) {η : ℚ_[2]} {ζ : ℕ → ℤ → ℚ_[2]}
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y : Bf ℚ_[2])
    (hY1 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Y) 1)
    (hY2 : Agree (Y * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds 0) 1)) (Fin (Dance.slots (Families.ds 0) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds 0) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ)
    (s s' : Fin (Dance.slots (Families.ds 0) 1)) :
    ‖(finalM GΞ * Nmat 0 B Y) s s'‖ ≤ 1 / 2 := by
  haveI : Subsingleton (Fin (Dance.slots (Families.ds 0) 1)) := by
    rw [InvBlock.slots_zero]; infer_instance
  obtain ⟨Gt, hGt⟩ := danceRel_nil_exists Families.ds_zero
    (fun _ _ => PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))
  have hN := Nmat_eq_inv 0 B hB _ Y hY1 hY2 Gt hGt
  have hp := norm_piF_add (c := c) hα ht 0
  have hne : PathSum.piF α c 0 + t ≠ 0 := by
    intro h; rw [h, norm_zero] at hp; norm_num at hp
  have hGt' : ∀ i j, finalM Gt i j = PathSum.piF α c 0 + t := by
    intro i j
    rw [finalM_nil Families.ds_zero _ Gt hGt i j, coef_XiOp_add]
    simp
  have hGΞ' : ∀ i j, finalM GΞ i j = PathSum.piF α c 0 := by
    intro i j
    rw [finalM_nil Families.ds_zero _ GΞ hGΞ i j]
    simp
  rw [Matrix.mul_apply, Fintype.sum_subsingleton _ s, hN,
    inv_apply_of_subsingleton _ _ hne hGt', hGΞ', norm_mul, norm_inv, hp]
  have h1 : ‖PathSum.piF α c 0‖ ≤ (1 / 2 : ℝ) ^ α := PathSum.norm_piF_le α c 0
  have h2 : (1 / 2 : ℝ) ^ α ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hα
  norm_num at h1 h2 ⊢
  linarith

/-- The case `l ≥ 1` of (B1) of `C50d_the_bend.md`, by the four steps of the file. -/
theorem B1_pos {l B α c : ℕ} (hl : 1 ≤ l) (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y : Bf ℚ_[2])
    (hY1 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Y) 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ)
    (s s' : Fin (Dance.slots (Families.ds l) 1)) :
    ‖(finalM GΞ * Nmat l B Y) s s'‖ ≤ 1 / 2 := by
  have hk : 1 ≤ (Families.ds l).length := Stability.length_ds_pos hl
  have hα1 : 1 ≤ α := by omega
  -- step 2: `Σ` with `η = 1`
  obtain ⟨G₁, hG₁⟩ := Conjugation.sig_one_dance (Families.ds l) hα1 c
  obtain ⟨Y₁, hY₁a, hY₁b⟩ := Conjugation.I (PathSum.SigOp α c 1) (fun f hf => by
    simpa [PathSum.SigOp] using PathSum.piF_ne_zero (α := α) hc hf)
  obtain ⟨-, hC⟩ := InvFloors.C109 l B hB _ Y₁ hY₁a hY₁b G₁ hG₁
  obtain ⟨hF2, hd1, hd2⟩ := Stability.F2 (l := l) hα1 hc G₁ hG₁
  obtain ⟨-, Bi, hBi, hAB⟩ := Stability.A3 hk
  set d1 : Fin (Dance.slots (Families.ds l) 1) → ℚ_[2] :=
    fun s => ((Stability.F2d1 (Families.ds l) α c s : ℚ) : ℚ_[2]) with hd1def
  set d2 : Fin (Dance.slots (Families.ds l) 1) → ℚ_[2] :=
    fun s => ((Stability.F2d2 (Families.ds l) α c s : ℚ) : ℚ_[2]) with hd2def
  have hd1' : ∀ s, d1 s ≠ 0 := fun s => Rat.cast_ne_zero.mpr (hd1 s)
  have hd2' : ∀ s, d2 s ≠ 0 := fun s => Rat.cast_ne_zero.mpr (hd2 s)
  have hdiag : ∀ d : Fin (Dance.slots (Families.ds l) 1) → ℚ_[2], (∀ s, d s ≠ 0) →
      diagonal d * diagonal (fun s => (d s)⁻¹) = 1 := by
    intro d hd
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext s
    exact mul_inv_cancel₀ (hd s)
  have hinv : (finalM G₁)⁻¹ = diagonal (fun s => (d2 s)⁻¹) * Bi * diagonal (fun s => (d1 s)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [hF2]
    calc diagonal d1 * Stability.Amat (Families.ds l) * diagonal d2 *
          (diagonal (fun s => (d2 s)⁻¹) * Bi * diagonal (fun s => (d1 s)⁻¹))
        = diagonal d1 * (Stability.Amat (Families.ds l) *
          ((diagonal d2 * diagonal (fun s => (d2 s)⁻¹)) * Bi)) *
            diagonal (fun s => (d1 s)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdiag d2 hd2', Matrix.one_mul, hAB, Matrix.mul_one, hdiag d1 hd1']
  -- step 3: the final matrix of `Ψ`
  obtain ⟨GSig, -, -, hT2, hF1η⟩ := Conjugation.T_eta hl hα hc hη hζ GΞ hGΞ
  have hM : ∀ D Y', ‖finalM GΞ D Y'‖ =
      ‖d1 D‖ * ‖Stability.Amat (Families.ds l) D Y'‖ * ‖d2 Y'‖ := by
    intro D Y'
    have e1 : finalM G₁ D Y' = d1 D * Stability.Amat (Families.ds l) D Y' * d2 Y' := by
      rw [hF2, mul_diagonal, diagonal_mul]
    have e2 : ‖finalM GΞ D Y'‖ = ‖finalM G₁ D Y'‖ := by
      rw [(hT2 D Y').2, hF1η D Y', Stability.F1 hα1 G₁ hG₁ D Y']
      split_ifs
      · rw [norm_mul, norm_zpow, hη, _root_.one_zpow, one_mul]
      · rfl
    rw [e2, e1, norm_mul, norm_mul]
  -- the norms `p d = ‖π(d)‖`
  set p : ℕ → ℝ := fun d => ‖PathSum.piF α c (d : ℤ)‖ with hpdef
  have hp0 : ∀ d, 0 < p d := fun d =>
    norm_pos_iff.mpr (PathSum.piF_ne_zero hc (Int.natCast_nonneg d))
  have hp : ∀ d, p d ≤ 1 / 4 := by
    intro d
    have h1 : ‖PathSum.piF α c d‖ ≤ (1 / 2 : ℝ) ^ α := PathSum.norm_piF_le α c d
    have h2 : (1 / 2 : ℝ) ^ α ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hα
    simp only [hpdef]
    norm_num at h1 h2 ⊢
    linarith
  -- step 4: the product
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) fun Y' _ => ?_
  rw [norm_mul, hM, N2 l B hB Y s' Y']
  set oX := Rulers.oE (Windows.Dset (Families.ds l) s') with hoX
  set oY := Rulers.oE (Windows.Dset (Families.ds l) Y') with hoY
  set oD := Rulers.oE (Windows.Dset (Families.ds l) s) with hoD
  set K := 2 ^ (Families.ds l).length with hK
  have hK1 : 1 ≤ K := Nat.one_le_two_pow
  split_ifs with hcond
  swap
  · rw [norm_zero, mul_zero]; norm_num
  set L := oY + K - 1 - oX with hL
  have hLf : (L : ℤ) ≤ ((oY + K - 1 : ℕ) : ℤ) := by exact_mod_cast Nat.sub_le _ _
  have hsL : PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ) ≠ 0 :=
    PathSum.sL_ne_zero hc one_ne_zero hLf
  have hinvE : (d2 Y')⁻¹ * Bi Y' s' * (d1 s')⁻¹ =
      2 ^ (Families.ds l).length * InvFloors.gamma l s' Y' *
        PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ) := by
    have := (hC s' Y').1 hcond
    rw [hinv, mul_diagonal, diagonal_mul, PathSum.P1 hc 1 Y₁ hY₁a _ _ hLf] at this
    exact this
  have hg : (2 : ℚ_[2]) ^ (Families.ds l).length * InvFloors.gamma l s' Y' =
      (d2 Y')⁻¹ * Bi Y' s' * (d1 s')⁻¹ / PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ) := by
    rw [hinvE, mul_div_cancel_right₀ _ hsL]
  rw [hg]
  by_cases hA : Stability.nest (Families.ds l) s Y'
  swap
  · simp [Stability.Amat, hA]
  by_cases hBn : Stability.nest (Families.ds l) Y' s'
  swap
  · rw [(hBi Y' s').1 hBn]; simp
  -- the two factors of norm `≤ 1`
  have hA1 : ‖Stability.Amat (Families.ds l) s Y'‖ ≤ 1 := by
    refine ((Stability.Amat_mem_Wt hk s Y').2).trans ?_
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hB1 : ‖Bi Y' s'‖ ≤ 1 := by
    refine ((hBi Y' s').2).trans ?_
    exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  -- the window
  have hW1 := (W (Families.ds l) s Y' hA)
  have hW2 := (W (Families.ds l) Y' s' hBn)
  have e1 := hW1.1
  have e2 := hW1.2
  have e3 := hW2.1
  have hXD : oX ≤ oD := by omega
  have hDL : oD ≤ oX + L := by omega
  -- the bound of the term
  have hYb := Y1 hα hη hζ ht Y hY1 L ((oY + K - 1 : ℕ) : ℤ) hLf
  have hcore := core_real p hp0 hp hXD hDL
    (C := (1 / 2 : ℝ) ^ ((1 : ℤ) - 2 ^ (Families.ds l).length)) (by positivity)
    (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero L))) hYb
  have hprod : ∏ i ∈ range (L + 1), ‖PathSum.piF α c (((oY + K - 1 : ℕ) : ℤ) - i)‖ =
      ∏ j ∈ range (L + 1), p (oX + j) := by
    rw [← prod_range_reflect (fun j => p (oX + j)) (L + 1)]
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    simp only [hpdef]
    congr 2
    push_cast [Nat.cast_sub (show oX ≤ oY + K - 1 from hcond),
      Nat.cast_sub (show 1 ≤ oY + K by omega), Nat.cast_sub (show i ≤ L + 1 - 1 by omega),
      Nat.cast_sub (show 1 ≤ L + 1 by omega)]
    omega
  have hd2n : ‖d2 Y'‖ ≠ 0 := norm_ne_zero_iff.mpr (hd2' Y')
  have hd1n : ‖d1 s'‖ ≠ 0 := norm_ne_zero_iff.mpr (hd1' s')
  have hsLn : ‖PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ)‖ ≠ 0 := norm_ne_zero_iff.mpr hsL
  calc ‖d1 s‖ * ‖Stability.Amat (Families.ds l) s Y'‖ * ‖d2 Y'‖ *
        ‖(d2 Y')⁻¹ * Bi Y' s' * (d1 s')⁻¹ / PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ) *
          Y.coef L ((oY + K - 1 : ℕ) : ℤ)‖
      = (‖Stability.Amat (Families.ds l) s Y'‖ * ‖Bi Y' s'‖) *
        (‖d1 s‖ / ‖d1 s'‖ * (‖Y.coef L ((oY + K - 1 : ℕ) : ℤ)‖ /
          ‖PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ)‖)) := by
        rw [norm_mul, norm_div, norm_mul, norm_mul, norm_inv, norm_inv]
        field_simp
    _ ≤ 1 * (‖d1 s‖ / ‖d1 s'‖ * (‖Y.coef L ((oY + K - 1 : ℕ) : ℤ)‖ /
          ‖PathSum.sL α c 1 L ((oY + K - 1 : ℕ) : ℤ)‖)) := by
        gcongr
        exact mul_le_one₀ hA1 (norm_nonneg _) hB1
    _ ≤ 1 / 2 := by
        rw [one_mul]
        simp only [hd1def]
        rw [norm_F2d1, norm_F2d1, norm_sL_one, hprod]
        exact hcore

/-- **(B1) Lemma 10.20** of `C50d_the_bend.md`: let `l : ℕ` (any; `l = 0` included),
`B ≥ l + 1`, `α ≥ 2`, `c ≥ 1`, `η` with `‖η‖ = 1`, `ζ` with `‖ζ m f‖ ≤ 1` for `m ≥ 2`, and `t`
with `‖t‖ = 1/2`. Let `Y : Bf ℚ_[2]` satisfy `Agree ((XiOp α c η ζ + t • 1) * Y) 1` and
`Agree (Y * (XiOp α c η ζ + t • 1)) 1`, and let `GΞ` satisfy
`DanceRel (Families.ds l) 1 (fun _ _ => XiOp α c η ζ) GΞ`. Then for all `s s'`,
`‖(finalM GΞ * Nmat l B Y) s s'‖ ≤ 1 / 2`. -/
theorem B1 {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    {t : ℚ_[2]} (ht : ‖t‖ = 1 / 2) (Y : Bf ℚ_[2])
    (hY1 : Agree ((PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2])) * Y) 1)
    (hY2 : Agree (Y * (PathSum.XiOp α c η ζ + t • (1 : Bf ℚ_[2]))) 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∀ s s' : Fin (Dance.slots (Families.ds l) 1),
      ‖(finalM GΞ * Nmat l B Y) s s'‖ ≤ 1 / 2 := by
  intro s s'
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · exact B1_zero hB hα ht Y hY1 hY2 GΞ hGΞ s s'
  · exact B1_pos hl hB hα hc hη hζ ht Y hY1 GΞ hGΞ s s'

/-- **(B2)** of `C50d_the_bend.md` (the two signs): in the setting of (B1) with `t = 2` and
`t = −2`, given the two inverses `Y₊` (of `XiOp α c η ζ + 2 • 1`) and `Y₋` (of
`XiOp α c η ζ + (−2) • 1`): `‖(finalM GΞ * Nmat l B Y₊) s s'‖ ≤ 1/2` and
`‖(finalM GΞ * Nmat l B Y₋) s s'‖ ≤ 1/2` (from (B1), with `‖2‖ = ‖−2‖ = 1/2`). -/
theorem B2 {l B α c : ℕ} (hB : l + 1 ≤ B) (hα : 2 ≤ α) (hc : 1 ≤ c)
    {η : ℚ_[2]} (hη : ‖η‖ = 1) {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1)
    (Yp Ym : Bf ℚ_[2])
    (hYp1 : Agree ((PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Yp) 1)
    (hYp2 : Agree (Yp * (PathSum.XiOp α c η ζ + (2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (hYm1 : Agree ((PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2])) * Ym) 1)
    (hYm2 : Agree (Ym * (PathSum.XiOp α c η ζ + (-2 : ℚ_[2]) • (1 : Bf ℚ_[2]))) 1)
    (GΞ : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => PathSum.XiOp α c η ζ) GΞ) :
    ∀ s s' : Fin (Dance.slots (Families.ds l) 1),
      ‖(finalM GΞ * Nmat l B Yp) s s'‖ ≤ 1 / 2 ∧ ‖(finalM GΞ * Nmat l B Ym) s s'‖ ≤ 1 / 2 := by
  intro s s'
  have h2 : ‖(2 : ℚ_[2])‖ = 1 / 2 := PathSum.norm_two_padic
  have hm2 : ‖(-2 : ℚ_[2])‖ = 1 / 2 := by rw [norm_neg, PathSum.norm_two_padic]
  exact ⟨B1 hB hα hc hη hζ h2 Yp hYp1 hYp2 GΞ hGΞ s s',
    B1 hB hα hc hη hζ hm2 Ym hYm1 hYm2 GΞ hGΞ s s'⟩

end Bend
