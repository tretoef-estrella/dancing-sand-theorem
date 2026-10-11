module

public import RequestProject.ArmsEven.Defs

/-!
# `C50c_the_arms_of_the_even_families.md`: Part H — the halves are good

(H1) for a good system `Γ` and `ε = ±1`, the product `Γ (Γ + 2 ε)` is twice a good system;
(H2) the covariant system of that half is the half of `Γ (Γ + 2 ε)` as a matrix.
-/

@[expose] public section

noncomputable section

namespace ArmsEven

open RingK Cleanliness FormalOps Finset

/-- Helper for (H1), (C1) of `C50c_the_arms_of_the_even_families.md`: every coefficient function
of `k • uSys` is in `Kr`. -/
lemma InK_smul_uSys (k : ℤ_[2]) : InK (k • uSys) := fun Δ m =>
  K3_smul k (K3_const (if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0))

/-- Helper for (H1), (C1) of `C50c_the_arms_of_the_even_families.md`: `InK (Γ + k • uSys)` for
`InK Γ`. -/
lemma InK_add_smul_uSys {Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]} (hK : InK Γ) (k : ℤ_[2]) :
    InK (Γ + k • uSys) := fun Δ m => K3_add (hK Δ m) (InK_smul_uSys k Δ m)

/-- Helper for (H1) of `C50c_the_arms_of_the_even_families.md`: `thetaSys ((2 ε) • uSys) = 0`
(the coefficients are the constants `2 ε` or `0`, and `red 2 = 0`). -/
lemma thetaSys_two_smul_uSys (ε : ℤ_[2]) : thetaSys ((2 * ε) • uSys) = 0 := by
  refine RS.ext fun Δ m => ?_
  have : ((2 * ε) • uSys) Δ m = fun _ => 2 * ε * (if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) := by
    funext y; rfl
  rw [thetaSys_apply, this, S1_const, map_mul, map_mul, red_two, zero_mul, zero_mul,
    TrivSqZeroExt.inl_zero, RS.zero_apply]

/-- Helper for (H1) of `C50c_the_arms_of_the_even_families.md` (as in the proof of C48 (W4)): for
`InK Γ` with even constant term at `(∅, 0)`, `thetaSys Γ * thetaSys Γ = 0` (C47 (R2), (S5)). -/
lemma thetaSys_mul_self {Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]} (hK : InK Γ) (hA : PayA Γ) :
    thetaSys Γ * thetaSys Γ = 0 := by
  refine RS.ext fun Δ q => ?_
  rw [R2, RS.zero_apply]
  split_ifs
  · rw [thetaSys_apply]
    obtain ⟨r, hr⟩ := hK ∅ 0
    rw [← hr]
    refine (S5 r).2 ?_
    obtain ⟨z, hz⟩ := hA 0
    obtain ⟨w, hw⟩ := (K6 r 0).1
    refine ⟨2 * z - 2 * w, ?_⟩
    rw [hr] at hw
    linear_combination hz - hw
  · rfl

/-- Helper for (H1) of `C50c_the_arms_of_the_even_families.md`: `red ε ≠ 0` for `ε = ±1`. -/
lemma red_ne_zero_of_pm {ε : ℤ_[2]} (hε : ε = 1 ∨ ε = -1) : red ε ≠ 0 := by
  rcases hε with rfl | rfl
  · rw [map_one]; exact one_ne_zero
  · rw [map_neg, map_one]; exact neg_ne_zero.2 one_ne_zero

/-- **(H1)** of `C50c_the_arms_of_the_even_families.md`: for every `Γ` with `Good Γ`, every `h`
and every `ε` with `ε = 1 ∨ ε = -1`, there is `Γ'` with `Good Γ'` and
`2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y` for all `Δ m y`. -/
theorem H1 (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (h : ℕ) (ε : ℤ_[2])
    (hε : ε = 1 ∨ ε = -1) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      ∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y := by
  obtain ⟨hK, hA, hB⟩ := hΓ
  have hK2 : InK (Γ + (2 * ε) • uSys) := InK_add_smul_uSys hK _
  have hKp : InK (prodFun h Γ (Γ + (2 * ε) • uSys)) := (T2 h _ _ hK hK2).1
  have hθ : thetaSys (prodFun h Γ (Γ + (2 * ε) • uSys)) = 0 := by
    rw [(T3 h _ _ hK hK2).1, (T3 h _ _ hK (InK_smul_uSys _)).2.1, thetaSys_two_smul_uSys,
      add_zero, thetaSys_mul_self hK hA]
  have h0 : ∀ Δ m, theta (prodFun h Γ (Γ + (2 * ε) • uSys) Δ m) = 0 := fun Δ m => by
    rw [← thetaSys_apply, hθ, RS.zero_apply]
  choose Γ' hΓ' using fun Δ m => (S3 (hKp Δ m)).1 (h0 Δ m)
  have h2 : ∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y := fun Δ m y =>
    (congrFun (hΓ' Δ m).2 y).symm
  have hu0 : ∀ y, (Γ + (2 * ε) • uSys) ∅ 0 y = Γ ∅ 0 y + 2 * ε := fun y => by
    simp [uSys]
  have hu1 : ∀ y, (Γ + (2 * ε) • uSys) ∅ 1 y = Γ ∅ 1 y := fun y => by
    simp [uSys]
  refine ⟨Γ', ⟨fun Δ m => (hΓ' Δ m).1, fun y => ?_, fun y => ?_⟩, h2⟩
  · obtain ⟨z, hz⟩ := hA y
    refine ⟨z * (2 * z + ε), mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) ?_⟩
    rw [h2, prodFun_empty_zero, hu0, hz]
    ring
  · obtain ⟨z, hz⟩ := hA y
    obtain ⟨z', hz'⟩ := hA (y - 2 ^ h)
    have hval : Γ' ∅ 1 y = 2 * (z * Γ ∅ 1 y + Γ ∅ 1 y * z') + ε * Γ ∅ 1 y := by
      refine mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) ?_
      rw [h2, prodFun_empty_one, hu1, hu0, hz, hz']
      ring
    rw [hval, isUnit_iff_red_ne_zero, map_add, map_mul, red_two, zero_mul, zero_add, map_mul]
    exact mul_ne_zero (red_ne_zero_of_pm hε) ((isUnit_iff_red_ne_zero _).1 (hB y))

/-- **(H2)** of `C50c_the_arms_of_the_even_families.md`: under the hypotheses of (H1), if
`2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y` for all `Δ m y`, then for every `P` and
`c`: `2 • covSys P h c Γ' = covSys P h c Γ * (covSys P h c Γ + (2 * ε) • 1)`.
(The hypotheses `Good Γ` and `ε = 1 ∨ ε = -1` of (H1) are kept, as anonymous binders, although
the proof does not use them.) -/
theorem H2 (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (_ : Good Γ) (h : ℕ) (ε : ℤ_[2])
    (_ : ε = 1 ∨ ε = -1) (Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (hΓ' : ∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y)
    (P : Finset ℕ) (c : ℤ_[2]) :
    (2 : ℤ_[2]) • covSys P h c Γ' =
      covSys P h c Γ * (covSys P h c Γ + (2 * ε) • (1 : Matrix (Dn P) (Dn P) (Bf ℤ_[2]))) := by
  rw [T1_one P h c, T1_smul P h c _ (2 * ε), T1_add, T1_mul, T1_smul]
  congr 1
  funext Δ m y
  exact hΓ' Δ m y

end ArmsEven
