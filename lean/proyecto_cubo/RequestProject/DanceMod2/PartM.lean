module

public import RequestProject.DanceMod2.PartK

/-!
# `C50b_the_dance_modulo_two.md`: Part M — one move

For good systems `Γ Γ''` congruent modulo `2` (`Cong2`): (M1) their Schur complements agree modulo
`4` at the constant terms, computed in the commutative ring `RA (ZMod (2 ^ 2))`; (M2) they agree
modulo `4` everywhere; (M3) C48 (W5) with the Schur equation kept; (M4) the next systems are
congruent modulo `2`; (M5) one twist move; (M6) one split move.
-/

@[expose] public section

noncomputable section

namespace DanceMod2

open Cleanliness FormalDance Finset
open RingK (Kr prodFun covSys Dn oS)

/-- Helper for (M1) of `C50b_the_dance_modulo_two.md`: `(2 * δ) Δ q = 2 * δ Δ q` in `RA R`. -/
lemma RA.two_mul_apply {R : Type*} [CommRing R] (δ : RA R) (Δ : Finset ℕ) (q : ℕ) :
    ((2 : RA R) * δ) Δ q = 2 * δ Δ q := by
  rw [two_mul, RA.add_apply, two_mul]

/-- Helper for (M1) of `C50b_the_dance_modulo_two.md`: `4 = 0` in `RA (ZMod (2 ^ 2))`. -/
lemma RA.four_eq_zero : (4 : RA (ZMod (2 ^ 2))) = 0 := by
  have h : (4 : RA (ZMod (2 ^ 2))) = 2 * 2 * 1 := by norm_num
  rw [h]
  refine RA.ext fun Δ q => ?_
  rw [mul_assoc, RA.two_mul_apply, RA.two_mul_apply, RA.zero_apply, ← mul_assoc, RA.one_apply]
  split_ifs
  · decide
  · simp

/-- Helper for (M1) of `C50b_the_dance_modulo_two.md`: `Cong2` reduced modulo `4`. -/
lemma red4_cong {Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]} {z : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]}
    (hz : ∀ Δ m y, Γ Δ m y - Γ'' Δ m y = 2 * z Δ m y) (Δ : Finset ℕ) (m : ℕ) (y : ℤ_[2]) :
    red4 (Γ'' Δ m y) = red4 (Γ Δ m y) - 2 * red4 (z Δ m y) := by
  rw [show Γ'' Δ m y = Γ Δ m y - 2 * z Δ m y by linear_combination -(hz Δ m y), map_sub, map_mul,
    map_ofNat]

/-- Helper for (M2) of `C50b_the_dance_modulo_two.md` (proof of C48 `W4_strong`): the Schur
complement of a system with `InK Γ` and `CoefB Γ` is in the class. -/
lemma schurG_inK (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hK : InK Γ) (hB : CoefB Γ) :
    InK (schurG h Γ) := by
  obtain ⟨-, hQ⟩ := GP_hyp h Γ hK hB
  obtain ⟨hGB, hGC, -, hGD, -, -⟩ := W2 h Γ hK
  have hX : InK (prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ))) :=
    (RingK.T2 (h + 1) _ _ hGB hQ).1
  have hT : InK (prodFun (h + 1) (prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ))) (GC h Γ)) :=
    (RingK.T2 (h + 1) _ _ hX hGC).1
  exact fun Δ m => RingK.K3_sub (hGD Δ m) (hT Δ m)

/-- **(M1)** of `C50b_the_dance_modulo_two.md`: for `Γ Γ''` with `Good Γ`, `Good Γ''`,
`Cong2 Γ Γ''`, and every `h`: `kap (schurG h Γ) = kap (schurG h Γ'')`. -/
theorem M1 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (h : ℕ) : kap (schurG h Γ) = kap (schurG h Γ'') := by
  obtain ⟨hK, hA, hB⟩ := hΓ
  obtain ⟨hK'', -, hB''⟩ := hΓ''
  choose z hz using hc
  obtain ⟨e1, hS⟩ := K4 h Γ hK hB
  obtain ⟨e2, hS''⟩ := K4 h Γ'' hK'' hB''
  rw [hS, hS'']
  -- the data of `Γ''` are those of `Γ` plus multiples of `2`
  set δ : RA (ZMod (2 ^ 2)) := fun Δ q => -(red4 (Doubling.dfi q) * red4 (z Δ (2 * q) 0))
  set π : RA (ZMod (2 ^ 2)) := fun Δ q =>
    -(red4 (Doubling.dfi (q + 1)) * red4 (z Δ (2 * q + 1) (0 + 2 ^ h)))
  have hβ : kap (GB Γ'') = kap (GB Γ) + 2 * δ := by
    refine RA.ext fun Δ q => ?_
    rw [RA.add_apply, RA.two_mul_apply]
    simp only [kap, GB, map_mul, red4_cong hz, δ]
    ring
  have hp : kap (GP h Γ'') = kap (GP h Γ) + 2 * π := by
    refine RA.ext fun Δ q => ?_
    rw [RA.add_apply, RA.two_mul_apply]
    simp only [kap, GP, map_mul, red4_cong hz, π]
    ring
  have hD : kap (GD Γ'') = kap (GD Γ) := by
    refine RA.ext fun Δ q => ?_
    cases q with
    | zero => rfl
    | succ q =>
      simp only [kap, GD, map_mul, red4_cong hz, map_natCast]
      push_cast
      linear_combination (-(((q : ZMod (2 ^ 2)) + 1) * red4 (Doubling.dfi (q + 1)) *
        red4 (z Δ (2 * q + 1) 0))) * four_zmod
  -- `β² = 2 γ`
  have hβ0 : kap (GB Γ) ∅ 0 = 0 := by
    obtain ⟨w, hw⟩ := hA 0
    simp only [kap, GB, Doubling.dfi_zero, Nat.mul_zero, one_mul, hw, red4_four_mul]
  choose γ hγ using fun Δ q => R2 (kap (GB Γ)) Δ q
  obtain ⟨γ', hγ'⟩ : ∃ γ' : RA (ZMod (2 ^ 2)), kap (GB Γ) * kap (GB Γ) = 2 * γ' := by
    refine ⟨γ, RA.ext fun Δ q => ?_⟩
    rw [hγ, RA.two_mul_apply, hβ0, mul_zero, ite_self, zero_add]
  rw [hβ, hD]
  rw [hp] at e2
  linear_combination (kap (rinv (h + 1) (GP h Γ'')) - kap (rinv (h + 1) (GP h Γ))) * hγ' -
    2 * γ' * kap (rinv (h + 1) (GP h Γ'')) * e1 +
    2 * γ' * kap (rinv (h + 1) (GP h Γ)) * e2 +
    ((kap (GB Γ) * δ + δ * δ) * kap (rinv (h + 1) (GP h Γ'')) -
      γ' * π * kap (rinv (h + 1) (GP h Γ)) *
        kap (rinv (h + 1) (GP h Γ''))) * RA.four_eq_zero

/-- **(M2)** of `C50b_the_dance_modulo_two.md`: for `Γ Γ''` with `Good Γ`, `Good Γ''`,
`Cong2 Γ Γ''`, and every `h`: `∀ Δ m y, ∃ z, schurG h Γ Δ m y - schurG h Γ'' Δ m y = 4 * z`. -/
theorem M2 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (h : ℕ) :
    ∀ Δ m y, ∃ z, schurG h Γ Δ m y - schurG h Γ'' Δ m y = 4 * z := by
  intro Δ m y
  have hM := congrFun (congrFun (M1 Γ Γ'' hΓ hΓ'' hc h) Δ) m
  simp only [kap] at hM
  rw [← red4_eq_zero_iff, map_sub, K1 (schurG_inK h Γ hΓ.1 hΓ.2.2 Δ m),
    K1 (schurG_inK h Γ'' hΓ''.1 hΓ''.2.2 Δ m), hM, sub_self]

/-- **(M3)** of `C50b_the_dance_modulo_two.md` (C48 (W5) with the Schur equation kept): for every
`Γ` with `Good Γ` and every `P h c`, there is `Γ'` with `Good Γ'`,
`∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y` and
`CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')`. The proof is that of C48 (W5). -/
theorem M3 (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hG : Good Γ) (P : Finset ℕ) (h : ℕ)
    (c : ℤ_[2]) :
    ∃ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧
      (∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y) ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') := by
  obtain ⟨hK, hA, hB⟩ := hG
  have hE : ∀ y, ∃ z, Γ ∅ 0 y = 2 * z := fun y => by
    obtain ⟨z, hz⟩ := hA y
    exact ⟨2 * z, by rw [hz]; ring⟩
  obtain ⟨Γ', hK', h2, hC⟩ := W4_strong P h c Γ hK hB hE
  have hQ0 : ∀ y, rinv (h + 1) (GP h Γ) ∅ 0 y = Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) := fun y => by
    rw [rinv_empty_zero, GP_empty_zero]
  have hform : ∀ y, 2 * Γ' ∅ 0 y =
      -(Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * Γ ∅ 0 (y + 2 ^ h)) := fun y => by
    rw [h2, schurG, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, prodFun_empty_zero,
      prodFun_empty_zero, hQ0]
    simp [GD, GB, GC]
  have h8 : ∀ y, ∃ z, Γ' ∅ 0 y = 8 * z := fun y => by
    obtain ⟨a, ha⟩ := hA y
    obtain ⟨b, hb⟩ := hA (y + 2 ^ h)
    refine ⟨-(a * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * b), ?_⟩
    have := hform y
    rw [ha, hb] at this
    exact mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) (by rw [this]; ring)
  refine ⟨Γ', ⟨hK', fun y => ?_, fun y => ?_⟩, h2, hC⟩
  · obtain ⟨z, hz⟩ := h8 y
    exact ⟨2 * z, by rw [hz]; ring⟩
  · obtain ⟨a, ha⟩ := hA y
    obtain ⟨b, hb⟩ := hA (y - 2 ^ (h + 1) + 2 ^ h)
    have hX0 : prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ)) ∅ 0 y =
        Γ ∅ 0 y * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) := by
      simp only [prodFun_empty_zero, hQ0, GB, Doubling.dfi_zero, Nat.mul_zero, one_mul]
    set w := a * Ring.inverse (Γ ∅ 1 (y + 2 ^ h)) * GC h Γ ∅ 1 y +
      prodFun (h + 1) (GB Γ) (rinv (h + 1) (GP h Γ)) ∅ 1 y * b
    have hval : 2 * Γ' ∅ 1 y = 2 * (Γ ∅ 1 y - 2 * w) := by
      rw [h2, schurG, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, prodFun_empty_one, GD_one, hX0]
      have hC0 : GC h Γ ∅ 0 (y - 2 ^ (h + 1)) = 4 * b := by
        simp only [GC, Doubling.dfi_zero, Nat.mul_zero, one_mul]; exact hb
      rw [hC0, ha]
      ring
    have hv := mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) hval
    rw [hv, RingK.isUnit_iff_red_ne_zero, map_sub, map_mul, RingK.red_two, zero_mul, sub_zero,
      ← RingK.isUnit_iff_red_ne_zero]
    exact hB y

/-- **(M4)** of `C50b_the_dance_modulo_two.md`: for `Γ Γ''` with `Good Γ`, `Good Γ''`,
`Cong2 Γ Γ''`, and every `h`: if `∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y` and
`∀ Δ m y, 2 * Γ''' Δ m y = schurG h Γ'' Δ m y`, then `Cong2 Γ' Γ'''`. -/
theorem M4 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (h : ℕ) (Γ' Γ''' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (h1 : ∀ Δ m y, 2 * Γ' Δ m y = schurG h Γ Δ m y)
    (h2 : ∀ Δ m y, 2 * Γ''' Δ m y = schurG h Γ'' Δ m y) : Cong2 Γ' Γ''' := by
  intro Δ m y
  obtain ⟨z, hz⟩ := M2 Γ Γ'' hΓ hΓ'' hc h Δ m y
  refine ⟨z, mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) ?_⟩
  rw [mul_sub, h1, h2, hz]
  ring

/-- **(M5)** of `C50b_the_dance_modulo_two.md` (one twist move): for `Γ Γ''` with `Good Γ`,
`Good Γ''`, `Cong2 Γ Γ''`, and every `P h c`, there are `Γ' Γ'''` with `Good Γ'`, `Good Γ'''`,
`Cong2 Γ' Γ'''`, `CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ')` and
`CleanStep (covSys P h c Γ'') (covSys P (h + 1) c Γ''')`. -/
theorem M5 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) :
    ∃ Γ' Γ''' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧ Good Γ''' ∧ Cong2 Γ' Γ''' ∧
      CleanStep (covSys P h c Γ) (covSys P (h + 1) c Γ') ∧
      CleanStep (covSys P h c Γ'') (covSys P (h + 1) c Γ''') := by
  obtain ⟨Γ', hG', h1, hC1⟩ := M3 Γ hΓ P h c
  obtain ⟨Γ''', hG''', h2, hC2⟩ := M3 Γ'' hΓ'' P h c
  exact ⟨Γ', Γ''', hG', hG''', M4 Γ Γ'' hΓ hΓ'' hc h Γ' Γ''' h1 h2, hC1, hC2⟩

/-- Helper for (M6) of `C50b_the_dance_modulo_two.md`: the `V`-split preserves `Cong2`. -/
lemma cong2_vsplitG {Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]} (hc : Cong2 Γ Γ'') (h : ℕ) :
    Cong2 (vsplitG h Γ) (vsplitG h Γ'') := by
  intro Δ m y
  simp only [vsplitG]
  split_ifs
  · exact hc _ _ _
  · exact hc _ _ _

/-- **(M6)** of `C50b_the_dance_modulo_two.md` (one split move): for `Γ Γ''` with `Good Γ`,
`Good Γ''`, `Cong2 Γ Γ''`, and every `P h c` with `hP : h ∉ P`, there are `Γ' Γ'''` with
`Good Γ'`, `Good Γ'''`, `Cong2 Γ' Γ'''`,
`CleanStep (vsplit (covSys P h c Γ))
(fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q'))` and
`CleanStep (vsplit (covSys P h c Γ''))
(fun q q' => covSys (insert h P) (h + 1) c Γ''' (splitDn P h hP q) (splitDn P h hP q'))`. -/
theorem M6 (Γ Γ'' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : Good Γ) (hΓ'' : Good Γ'')
    (hc : Cong2 Γ Γ'') (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (hP : h ∉ P) :
    ∃ Γ' Γ''' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], Good Γ' ∧ Good Γ''' ∧ Cong2 Γ' Γ''' ∧
      CleanStep (vsplit (covSys P h c Γ))
        (fun q q' => covSys (insert h P) (h + 1) c Γ' (splitDn P h hP q) (splitDn P h hP q')) ∧
      CleanStep (vsplit (covSys P h c Γ''))
        (fun q q' => covSys (insert h P) (h + 1) c Γ''' (splitDn P h hP q)
          (splitDn P h hP q')) := by
  obtain ⟨Γ', Γ''', hG', hG''', hc', hC1, hC2⟩ :=
    M5 (vsplitG h Γ) (vsplitG h Γ'') ((V2 h Γ).1 hΓ) ((V2 h Γ'').1 hΓ'') (cong2_vsplitG hc h)
      (insert h P) h c
  have hV : ∀ G : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2], vsplit (covSys P h c G) = fun q q' =>
      covSys (insert h P) h c (vsplitG h G) (splitDn P h hP q) (splitDn P h hP q') :=
    fun G => funext fun q => funext fun q' => V1 P h c G hP q q'
  refine ⟨Γ', Γ''', hG', hG''', hc', ?_, ?_⟩
  · rw [hV]; exact L1 (splitDn P h hP) _ _ hC1
  · rw [hV]; exact L1 (splitDn P h hP) _ _ hC2

end DanceMod2
