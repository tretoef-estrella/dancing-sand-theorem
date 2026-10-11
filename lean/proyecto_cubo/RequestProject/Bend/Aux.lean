module

public import RequestProject.Bend.PartY
public import RequestProject.Bend.PartW

/-!
# `C50d_the_bend.md`: auxiliary norm computations for (B1)

* `core_real`: the window computation of step 4 of the file, in real numbers:
  `(|𝔡₁(D)| / |𝔡₁(X)|) · 2^{L+1} · ∏_{d = o_X}^{o_X + L} ‖π(d)‖ ≤ 1/2` when
  `o_X ≤ o_D ≤ o_X + L`.
* `norm_F2d1`: the norm of the left diagonal factor `𝔡₁` of C44 `F2`.
* `norm_sL_one`: the norm of `sL α c 1 L f`.
-/

@[expose] public section

noncomputable section

namespace Bend

open Finset

/-- Auxiliary for (B1) of `C50d_the_bend.md` (step 4, the window), in real numbers: with
`p d = ‖π(d)‖ ∈ (0, 1/4]`, `o_X ≤ o_D ≤ o_X + L`, `C > 0`, `lf > 0` and `y ≤ lf · 2^{L+1}`,
`(C (1/2)^{o_D} / ∏_{d < o_D} p d) / (C (1/2)^{o_X} / ∏_{d < o_X} p d) ·
(y / (lf / ∏_{j ≤ L} p (o_X + j))) ≤ 1/2`. -/
lemma core_real (p : ℕ → ℝ) (hp0 : ∀ d, 0 < p d) (hp : ∀ d, p d ≤ 1 / 4) {oX oD L : ℕ}
    (h1 : oX ≤ oD) (h2 : oD ≤ oX + L) {C y lf : ℝ} (hC : 0 < C) (hlf : 0 < lf)
    (hy : y ≤ lf * 2 ^ (L + 1)) :
    (C * (1 / 2) ^ oD / ∏ d ∈ range oD, p d) / (C * (1 / 2) ^ oX / ∏ d ∈ range oX, p d) *
      (y / (lf / ∏ j ∈ range (L + 1), p (oX + j))) ≤ 1 / 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, oD = oX + e := ⟨oD - oX, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, L + 1 = e + n := ⟨L + 1 - e, by omega⟩
  have hn1 : 1 ≤ n := by omega
  set PX := ∏ d ∈ range oX, p d
  set PD := ∏ d ∈ range (oX + e), p d
  set Pj := ∏ j ∈ range (L + 1), p (oX + j)
  set Pn := ∏ j ∈ range n, p (oX + e + j)
  have hPX : 0 < PX := prod_pos fun d _ => hp0 d
  have hPD : 0 < PD := prod_pos fun d _ => hp0 d
  have hPj : 0 < Pj := prod_pos fun d _ => hp0 _
  have hPn0 : 0 ≤ Pn := (prod_pos fun d _ => hp0 _).le
  have hsplit : PX * Pj = PD * Pn := by
    simp only [PX, Pj, PD, Pn]
    rw [← prod_range_add, hn, ← add_assoc, prod_range_add]
  have hPn : Pn ≤ (1 / 4) ^ n := by
    calc Pn ≤ ∏ _j ∈ range n, (1 / 4 : ℝ) :=
          prod_le_prod (fun j _ => (hp0 _).le) (fun j _ => hp _)
      _ = (1 / 4) ^ n := by rw [prod_const, card_range]
  have heq : (C * (1 / 2) ^ (oX + e) / PD) / (C * (1 / 2) ^ oX / PX) * (y / (lf / Pj)) =
      (1 / 2) ^ e * (y / lf) * Pn := by
    rw [pow_add]
    field_simp
    linear_combination y * hsplit
  rw [heq]
  have hyl : y / lf ≤ 2 ^ (L + 1) := by rw [div_le_iff₀ hlf]; linarith
  calc (1 / 2 : ℝ) ^ e * (y / lf) * Pn ≤ (1 / 2) ^ e * 2 ^ (L + 1) * (1 / 4) ^ n := by
        gcongr
    _ = (1 / 2) ^ n := by
        rw [hn, pow_add, show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, mul_pow]
        have h2e : (1 / 2 : ℝ) ^ e * 2 ^ e = 1 := by rw [← mul_pow]; norm_num
        have h2n : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination ((1 / 2 : ℝ) ^ n) * (2 ^ n * (1 / 2) ^ n) * h2e +
          ((1 / 2 : ℝ) ^ n) * h2n
    _ ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
          _ = 1 / 2 := by norm_num

/-- Auxiliary for (B1) of `C50d_the_bend.md`: `Deficit.pi0 α c d` (cast to `ℚ_[2]`) is
`PathSum.piF α c d`. -/
lemma pi0_cast (α c d : ℕ) : ((Deficit.pi0 (α : ℤ) c d : ℚ) : ℚ_[2]) = PathSum.piF α c d := by
  simp only [Deficit.pi0, PathSum.piF]
  push_cast
  rw [zpow_natCast]
  ring

/-- Auxiliary for (B1) of `C50d_the_bend.md` (step 2): the norm of the left diagonal factor of
C44 `F2`, `‖𝔡₁ s‖ = (1/2)^{1 − K} · (1/2)^{o_s} / ∏_{d < o_s} ‖π(d)‖`. -/
lemma norm_F2d1 (ds : List Bool) (α c : ℕ) (s : Fin (Dance.slots ds 1)) :
    ‖((Stability.F2d1 ds α c s : ℚ) : ℚ_[2])‖ =
      (1 / 2 : ℝ) ^ ((1 : ℤ) - 2 ^ ds.length) * (1 / 2) ^ Rulers.oE (Windows.Dset ds s) /
        ∏ d ∈ range (Rulers.oE (Windows.Dset ds s)), ‖PathSum.piF α c (d : ℤ)‖ := by
  simp only [Stability.F2d1]
  push_cast
  rw [norm_div, norm_mul, norm_neg, norm_zpow, norm_pow, norm_prod, PathSum.norm_two_padic]
  congr 2
  funext d
  rw [pi0_cast]

/-- Auxiliary for (B1) of `C50d_the_bend.md`: `‖sL α c 1 L f‖ = ‖L!‖ / ∏_{i ≤ L} ‖π(f − i)‖`. -/
lemma norm_sL_one (α c L : ℕ) (f : ℤ) :
    ‖PathSum.sL α c 1 L f‖ =
      ‖((L.factorial : ℕ) : ℚ_[2])‖ / ∏ i ∈ range (L + 1), ‖PathSum.piF α c (f - i)‖ := by
  simp only [PathSum.sL]
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, mul_one, norm_prod]

end Bend
