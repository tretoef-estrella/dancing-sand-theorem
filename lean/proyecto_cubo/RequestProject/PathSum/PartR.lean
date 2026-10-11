module

public import RequestProject.PathSum.PartP
public import RequestProject.InvFloors.All

/-!
# `C43_path_sum.md`: (R) the relation of the final inverses

`R`: C42's `InvFloors.C109` for `Ξ` and for `Σ` (same `l`, hence the same `InvFloors.gamma`),
then (P1) and (P2) at the same `L = oY' + 2^k − 1 − oX` and `f = oY' + 2^k − 1`. If the `Σ`
entry is `0` then `γ = 0` (as `sL ≠ 0`) or `oX > oY' + 2^k − 1`, and the `Ξ` entry is `0` too.
-/

@[expose] public section

noncomputable section

namespace PathSum

open FormalOps FormalDance Doubling Finset

/-- **(R)** of `C43_path_sum.md` (the final inverses): for `α ≥ 2`, `c ≥ 1`, `‖η‖ = 1`,
`‖ζ m f‖ ≤ 1` (`m ≥ 2`), `l B` with `B ≥ l + 1`, two-sided inverses `YΞ` of `XiOp α c η ζ` and
`YSig` of `SigOp α c η` (in the sense of `Agree … 1`), and `GΞ`, `GSig` related by `DanceRel` to the
constant one-slot systems `Ξ` and `Σ`: for all final slots `X`, `Y'`,
* if `(finalM GSig)⁻¹ Y' X = 0` then `(finalM GΞ)⁻¹ Y' X = 0`;
* otherwise there is `e` with `(finalM GΞ)⁻¹ Y' X = (finalM GSig)⁻¹ Y' X * (1 + e)` and
  `‖e‖ ≤ 2 ^ (−(α − 1 : ℤ))`.
(`B` is only needed to apply C42's `C109`; the conclusion does not depend on it.) -/
theorem R {α c : ℕ} (hα : 2 ≤ α) (hc : 1 ≤ c) {η : ℚ_[2]} (hη : ‖η‖ = 1)
    {ζ : ℕ → ℤ → ℚ_[2]} (hζ : ∀ m, 2 ≤ m → ∀ f, ‖ζ m f‖ ≤ 1) (l B : ℕ) (hB : l + 1 ≤ B)
    (YΞ YSig : Bf ℚ_[2])
    (hΞY : Agree (XiOp α c η ζ * YΞ) 1) (hYΞ : Agree (YΞ * XiOp α c η ζ) 1)
    (hSigY : Agree (SigOp α c η * YSig) 1) (hYSig : Agree (YSig * SigOp α c η) 1)
    (GΞ GSig : Matrix (Fin (Dance.slots (Families.ds l) 1)) (Fin (Dance.slots (Families.ds l) 1))
      (Bf ℚ_[2]))
    (hGΞ : DanceRel (Families.ds l) 1 (fun _ _ => XiOp α c η ζ) GΞ)
    (hGSig : DanceRel (Families.ds l) 1 (fun _ _ => SigOp α c η) GSig) :
    ∀ X Y' : Fin (Dance.slots (Families.ds l) 1),
      ((finalM GSig)⁻¹ Y' X = 0 → (finalM GΞ)⁻¹ Y' X = 0) ∧
      ((finalM GSig)⁻¹ Y' X ≠ 0 → ∃ e : ℚ_[2],
        (finalM GΞ)⁻¹ Y' X = (finalM GSig)⁻¹ Y' X * (1 + e) ∧
          ‖e‖ ≤ (2 : ℝ) ^ (-(α - 1 : ℤ))) := by
  obtain ⟨-, hΞ⟩ := InvFloors.C109 l B hB (XiOp α c η ζ) YΞ hΞY hYΞ GΞ hGΞ
  obtain ⟨-, hSig⟩ := InvFloors.C109 l B hB (SigOp α c η) YSig hSigY hYSig GSig hGSig
  intro X Y'
  set oX := Rulers.oE (Windows.Dset (Families.ds l) X)
  set oY := Rulers.oE (Windows.Dset (Families.ds l) Y')
  set P := 2 ^ (Families.ds l).length
  by_cases hle : oX ≤ oY + P - 1
  · have hfL : ((oY + P - 1 - oX : ℕ) : ℤ) ≤ ((oY + P - 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.sub_le _ _
    rw [(hΞ X Y').1 hle, (hSig X Y').1 hle, P1 hc η YSig hSigY _ _ hfL]
    obtain ⟨hne, e, he, hen⟩ := P2 hα hc hη hζ YΞ hΞY _ _ hfL
    rw [he]
    refine ⟨fun h0 => ?_, fun _ => ⟨e, by ring, hen⟩⟩
    rw [mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_mul]
    · exact absurd h0 hne
  · have h1 := (hΞ X Y').2 (by omega)
    have h2 := (hSig X Y').2 (by omega)
    exact ⟨fun _ => h1, fun h => absurd h2 h⟩

end PathSum
