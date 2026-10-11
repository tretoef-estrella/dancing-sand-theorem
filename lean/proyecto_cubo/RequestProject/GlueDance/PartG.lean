module

public import RequestProject.GlueDance.PartB

/-!
# `C50_the_glue_commutes_with_the_dance.md`: Part G — one twist move

(G2) of the file. The proof follows the sketch, with no division: the pivot of the glued system
has the glued inverse `glueM Q_X Q_Y (−(Q_Y * twP Z * Q_X))`; the lower-left block `L` of the glued
Schur complement satisfies `2L ≈ S_Y − S_X` (an exact identity of noncommutative ring elements up to
terms that agree with `0`); and `L ≈ 2W` by (B4).
-/

@[expose] public section

noncomputable section

namespace GlueDance

open FormalOps FormalDance ContZero

variable {n : Type*}

/-! ### Linearity of the twist blocks -/

/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twP_sub (G H : Matrix n n (Bf ℤ_[2])) : twP (G - H) = twP G - twP H := by
  funext s s'; exact tw10_sub' _ _
/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twC_sub (G H : Matrix n n (Bf ℤ_[2])) : twC (G - H) = twC G - twC H := by
  funext s s'; exact tw11_sub' _ _
/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twB_sub (G H : Matrix n n (Bf ℤ_[2])) : twB (G - H) = twB G - twB H := by
  funext s s'; exact tw00_sub' _ _
/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twD_sub (G H : Matrix n n (Bf ℤ_[2])) : twD (G - H) = twD G - twD H := by
  funext s s'; exact tw01_sub' _ _

/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twP_smul (a : ℤ_[2]) (G : Matrix n n (Bf ℤ_[2])) : twP (a • G) = a • twP G := by
  ext s s' q f; simp [twP]; ring
/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twC_smul (a : ℤ_[2]) (G : Matrix n n (Bf ℤ_[2])) : twC (a • G) = a • twC G := by
  ext s s' q f; simp [twC]; ring
/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twB_smul (a : ℤ_[2]) (G : Matrix n n (Bf ℤ_[2])) : twB (a • G) = a • twB G := by
  ext s s' q f; simp [twB]; ring
/-- Linearity of the twist blocks (used for (G2) of `C50_the_glue_commutes_with_the_dance.md`). -/
lemma twD_smul (a : ℤ_[2]) (G : Matrix n n (Bf ℤ_[2])) : twD (a • G) = a • twD G := by
  ext s s' q f
  cases q <;> simp [twD]
  ring

/-! ### Agreement with `0` -/

/-- `MAgree G H ↔ MAgree (G − H) 0` (used for (G2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma magree_iff_sub_zero {G H : Matrix n n (Bf ℤ_[2])} : MAgree G H ↔ MAgree (G - H) 0 := by
  constructor
  · intro h; simpa using h.sub (MAgree.refl H)
  · intro h; simpa using h.add (MAgree.refl H)

/-- Matrices agreeing with `0` form a two-sided ideal (used for (G2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma z0_mul [Fintype n] {G : Matrix n n (Bf ℤ_[2])} (K K' : Matrix n n (Bf ℤ_[2]))
    (h : MAgree G 0) : MAgree (K * G * K') 0 := by
  simpa using ((MAgree.refl K).mul h).mul (MAgree.refl K')

/-- Negatives of matrices agreeing with `0` (used for (G2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma z0_neg {G : Matrix n n (Bf ℤ_[2])} (hG : MAgree G 0) : MAgree (-G) 0 := by
  simpa using (MAgree.refl (0 : Matrix n n (Bf ℤ_[2]))).sub hG

/-- Sums of matrices agreeing with `0` (used for (G2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma z0_add {G H : Matrix n n (Bf ℤ_[2])} (hG : MAgree G 0) (hH : MAgree H 0) :
    MAgree (G + H) 0 := by simpa using hG.add hH

/-- Differences of matrices agreeing with `0` (used for (G2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma z0_sub {G H : Matrix n n (Bf ℤ_[2])} (hG : MAgree G 0) (hH : MAgree H 0) :
    MAgree (G - H) 0 := by simpa using hG.sub hH

/-- The halved twist blocks: from `MAgree (Y − X) (2 • Z)`, the same for `twP`, `twC`, `twB`,
`twD`, written as `MAgree ((t Y − t X) − (t Z + t Z)) 0` (used for (G2) of
`C50_the_glue_commutes_with_the_dance.md`). -/
lemma halve_tw {X Y Z : Matrix n n (Bf ℤ_[2])} (h : MAgree (Y - X) ((2 : ℤ_[2]) • Z)) :
    MAgree ((twP Y - twP X) - (twP Z + twP Z)) 0 ∧
    MAgree ((twC Y - twC X) - (twC Z + twC Z)) 0 ∧
    MAgree ((twB Y - twB X) - (twB Z + twB Z)) 0 ∧
    MAgree ((twD Y - twD X) - (twD Z + twD Z)) 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← magree_iff_sub_zero, ← two_smul ℤ_[2]]
  · have := h.twP; rwa [twP_sub, twP_smul] at this
  · have := h.twC; rwa [twC_sub, twC_smul] at this
  · have := h.twB; rwa [twB_sub, twB_smul] at this
  · have := h.twD; rwa [twD_sub, twD_smul] at this

/-- The telescoping of the sketch of (G2) of `C50_the_glue_commutes_with_the_dance.md`: the
lower-left block `L` of the glued Schur complement satisfies `2L ≈ S_Y − S_X`. -/
lemma schur_telescope [Fintype n] [DecidableEq n]
    (PX PY PZ BX BY BZ CX CY CZ DX DY DZ QX QY : Matrix n n (Bf ℤ_[2]))
    (hP : MAgree ((PY - PX) - (PZ + PZ)) 0) (hC : MAgree ((CY - CX) - (CZ + CZ)) 0)
    (hB : MAgree ((BY - BX) - (BZ + BZ)) 0) (hD : MAgree ((DY - DX) - (DZ + DZ)) 0)
    (hX : MAgree (PX * QX) 1) (hY : MAgree (QY * PY) 1) :
    MAgree ((DZ - ((BZ * QX + BY * -(QY * PZ * QX)) * CX + BY * QY * CZ)) +
        (DZ - ((BZ * QX + BY * -(QY * PZ * QX)) * CX + BY * QY * CZ)))
      ((DY - BY * QY * CY) - (DX - BX * QX * CX)) := by
  rw [magree_iff_sub_zero] at hX hY ⊢
  have key : ((DZ - ((BZ * QX + BY * -(QY * PZ * QX)) * CX + BY * QY * CZ)) +
        (DZ - ((BZ * QX + BY * -(QY * PZ * QX)) * CX + BY * QY * CZ))) -
      ((DY - BY * QY * CY) - (DX - BX * QX * CX)) =
      ((1 * ((BY - BX) - (BZ + BZ)) * (QX * CX) - 1 * ((DY - DX) - (DZ + DZ)) * 1) -
        (BY * QY) * ((PY - PX) - (PZ + PZ)) * (QX * CX)) +
      ((BY * QY) * ((CY - CX) - (CZ + CZ)) * 1 +
        (BY * (QY * PY - 1) * (QX * CX) - (BY * QY) * (PX * QX - 1) * CX)) := by
    noncomm_ring
  rw [key]
  exact z0_add (z0_sub (z0_sub (z0_mul _ _ hB) (z0_mul _ _ hD)) (z0_mul _ _ hP))
    (z0_add (z0_mul _ _ hC) (z0_sub (z0_mul _ _ hY) (z0_mul _ _ hX)))

/-- **(G2)** of `C50_the_glue_commutes_with_the_dance.md` (one twist move): for `n` a `Fintype`
with `DecidableEq` and `X Y Z X' Y' W : Matrix n n (Bf ℤ_[2])`, if `CleanStep X X'`,
`CleanStep Y Y'`, `MAgree (Y - X) ((2 : ℤ_[2]) • Z)` and `MAgree (Y' - X') ((2 : ℤ_[2]) • W)`,
then `CleanStep (glueM X Y Z) (glueM X' Y' W)`. -/
theorem G2 [Fintype n] [DecidableEq n] {X Y Z X' Y' W : Matrix n n (Bf ℤ_[2])}
    (hX : CleanStep X X') (hY : CleanStep Y Y') (hZ : MAgree (Y - X) ((2 : ℤ_[2]) • Z))
    (hW : MAgree (Y' - X') ((2 : ℤ_[2]) • W)) : CleanStep (glueM X Y Z) (glueM X' Y' W) := by
  obtain ⟨QX, hX1, hX2, hX3⟩ := hX
  obtain ⟨QY, hY1, hY2, hY3⟩ := hY
  obtain ⟨hP, hC, hB, hD⟩ := halve_tw hZ
  refine ⟨glueM QX QY (-(QY * twP Z * QX)), ?_, ?_, ?_⟩
  · rw [B2_twP, B1_mul, ← B1_one]
    refine B3_mk hX1 hY1 ?_
    rw [magree_iff_sub_zero] at hY1 ⊢
    have key : twP Z * QX + twP Y * -(QY * twP Z * QX) - 0 =
        -(1 * (twP Y * QY - 1) * (twP Z * QX)) := by noncomm_ring
    rw [key]; exact z0_neg (z0_mul 1 (twP Z * QX) hY1)
  · rw [B2_twP, B1_mul, ← B1_one]
    refine B3_mk hX2 hY2 ?_
    rw [magree_iff_sub_zero] at hX2 ⊢
    have key : -(QY * twP Z * QX) * twP X + QY * twP Z - 0 =
        -((QY * twP Z) * (QX * twP X - 1) * 1) := by noncomm_ring
    rw [key]; exact z0_neg (z0_mul (QY * twP Z) 1 hX2)
  · rw [B2_twD, B2_twB, B2_twC, B1_mul, B1_mul, B1_sub, B1_smul]
    refine B3_mk hX3 hY3 (B4 ?_)
    have h2L := schur_telescope (twP X) (twP Y) (twP Z) (twB X) (twB Y) (twB Z) (twC X) (twC Y)
      (twC Z) (twD X) (twD Y) (twD Z) QX QY hP hC hB hD hX1 hY2
    rw [← two_smul ℤ_[2]] at h2L
    refine h2L.trans ((hY3.sub hX3).trans ?_)
    rw [← smul_sub]
    exact hW.smul 2

end GlueDance
