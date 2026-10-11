module

public import RequestProject.DanceMod2.PartR

/-!
# `C50b_the_dance_modulo_two.md`: Part K — the reduction modulo 4

(K1) every function of `Kr` is constant modulo `4` (C47 (K6)); (K2) `kap` turns `prodFun` into
the product of the commutative ring `RA (ZMod (2 ^ 2))` of Part R; (K3) `kap (GC h Γ) = kap (GB Γ)`;
(K4) the pivot and its right inverse `rinv (h + 1) (GP h Γ)` are inverse in `RA (ZMod (2 ^ 2))`,
and `kap` of the Schur complement `schurG h Γ` is `D − β Q β`.
-/

@[expose] public section

noncomputable section

namespace DanceMod2

open Cleanliness Finset
open RingK (Kr prodFun)

/-- Helper for Part K of `C50b_the_dance_modulo_two.md`: `4 = 0` in `ZMod (2 ^ 2)`. -/
lemma four_zmod : (4 : ZMod (2 ^ 2)) = 0 := by decide

/-- Helper for Part K of `C50b_the_dance_modulo_two.md`: `red4 (4 * z) = 0`. -/
lemma red4_four_mul (z : ℤ_[2]) : red4 (4 * z) = 0 := by
  rw [map_mul, map_ofNat, four_zmod, zero_mul]

/-- Helper for (M2) of `C50b_the_dance_modulo_two.md`: the kernel of `red4` is `4 ℤ_[2]`. -/
lemma red4_eq_zero_iff (x : ℤ_[2]) : red4 x = 0 ↔ ∃ z, x = 4 * z := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b, by rw [← hb]; push_cast; ring⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, by push_cast; ring⟩

/-- **(K1)** of `C50b_the_dance_modulo_two.md`: for `ϑ ∈ Kr` and every `y`,
`red4 (ϑ y) = red4 (ϑ 0)`. -/
theorem K1 {ϑ : ℤ_[2] → ℤ_[2]} (hϑ : ϑ ∈ Kr) (y : ℤ_[2]) : red4 (ϑ y) = red4 (ϑ 0) := by
  obtain ⟨r, rfl⟩ := hϑ
  obtain ⟨z, hz⟩ := (RingK.K6 r y).1
  obtain ⟨z', hz'⟩ := (RingK.K6 r 0).1
  rw [show r.eval y = r.a + 4 * z by rw [← hz]; ring,
    show r.eval 0 = r.a + 4 * z' by rw [← hz']; ring, map_add, map_add, red4_four_mul,
    red4_four_mul]

/-- **(K2)** of `C50b_the_dance_modulo_two.md`, the product: for `InK Γ`, `InK Γ'` and every `h`,
`kap (prodFun h Γ Γ') = kap Γ * kap Γ'`. Stated more generally than in the file: only `InK Γ'`
is needed (the factors of `Γ'` are the shifted ones), so `InK Γ` is dropped here. -/
theorem K2_mul (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ' : InK Γ') :
    kap (prodFun h Γ Γ') = kap Γ * kap Γ' := by
  refine RA.ext fun Δ m => ?_
  simp only [kap, prodFun, RA.mul_apply, map_sum, map_mul, map_natCast]
  refine sum_congr rfl fun Δ₁ _ => sum_congr rfl fun a _ => ?_
  rw [K1 (hΓ' _ _)]

/-- **(K2)** of `C50b_the_dance_modulo_two.md`, the sum (no hypothesis):
`kap (Γ + Γ') = kap Γ + kap Γ'`. -/
theorem K2_add (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : kap (Γ + Γ') = kap Γ + kap Γ' := by
  refine RA.ext fun Δ m => ?_
  simp only [kap, RA.add_apply, Pi.add_apply, map_add]

/-- **(K2)** of `C50b_the_dance_modulo_two.md`, the difference (no hypothesis):
`kap (Γ - Γ') = kap Γ - kap Γ'`. -/
theorem K2_sub (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : kap (Γ - Γ') = kap Γ - kap Γ' := by
  refine RA.ext fun Δ m => ?_
  simp only [kap, RA.sub_apply, Pi.sub_apply, map_sub]

/-- **(K2)** of `C50b_the_dance_modulo_two.md`, the unit:
`kap (fun Δ m _ => if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) = 1`. -/
theorem K2_one : kap (fun Δ m _ => if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) = 1 := by
  refine RA.ext fun Δ m => ?_
  simp only [kap, RA.one_apply]
  split_ifs <;> simp

/-- **(K2)** of `C50b_the_dance_modulo_two.md`: for `Γ Γ'` with `InK Γ` and `InK Γ'`, and every
`h`: `kap (prodFun h Γ Γ') = kap Γ * kap Γ'`, `kap (Γ + Γ') = kap Γ + kap Γ'`,
`kap (Γ - Γ') = kap Γ - kap Γ'` and `kap` of the unit system is `1`. (The hypothesis `InK Γ` of
the file is kept, as an anonymous binder, although the proof does not need it.) -/
theorem K2 (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (_ : InK Γ) (hΓ' : InK Γ') :
    kap (prodFun h Γ Γ') = kap Γ * kap Γ' ∧ kap (Γ + Γ') = kap Γ + kap Γ' ∧
      kap (Γ - Γ') = kap Γ - kap Γ' ∧
      kap (fun Δ m _ => if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) = 1 :=
  ⟨K2_mul h Γ Γ' hΓ', K2_add Γ Γ', K2_sub Γ Γ', K2_one⟩

/-- **(K3)** of `C50b_the_dance_modulo_two.md`: for `InK Γ` and every `h`,
`kap (GC h Γ) = kap (GB Γ)`. -/
theorem K3 (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hK : InK Γ) :
    kap (GC h Γ) = kap (GB Γ) := by
  refine RA.ext fun Δ q => ?_
  simp only [kap, GC, GB, map_mul]
  rw [K1 (hK Δ (2 * q))]

/-- **(K4)** of `C50b_the_dance_modulo_two.md`: for `InK Γ`, `CoefB Γ` and every `h`, with
`Q := rinv (h + 1) (GP h Γ)`: `kap (GP h Γ) * kap Q = 1` and
`kap (schurG h Γ) = kap (GD Γ) - kap (GB Γ) * kap Q * kap (GB Γ)`. -/
theorem K4 (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hK : InK Γ) (hB : CoefB Γ) :
    kap (GP h Γ) * kap (rinv (h + 1) (GP h Γ)) = 1 ∧
      kap (schurG h Γ) =
        kap (GD Γ) - kap (GB Γ) * kap (rinv (h + 1) (GP h Γ)) * kap (GB Γ) := by
  obtain ⟨hu, hQ⟩ := GP_hyp h Γ hK hB
  obtain ⟨-, hGC, -, -, -, -⟩ := W2 h Γ hK
  refine ⟨?_, ?_⟩
  · rw [← K2_mul (h + 1) _ _ hQ, prodFun_rinv _ _ hu, K2_one]
  · rw [schurG, K2_sub, K2_mul _ _ _ hGC, K2_mul _ _ _ hQ, K3 h Γ hK]

end DanceMod2
