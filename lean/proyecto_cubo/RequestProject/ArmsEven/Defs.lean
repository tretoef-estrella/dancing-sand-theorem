module

public import RequestProject.DanceMod2.All
public import RequestProject.FoldOdd.All
public import RequestProject.DanceXi.All

/-!
# `C50c_the_arms_of_the_even_families.md`: Definitions (new)

Namespace `ArmsEven`. Nothing listed in the Setting of the file is redefined: `Bf` is C40's
(`FormalOps`); `MAgree`, `CleanStep`, `DanceRel` are C40b's (`FormalDance`); `XiOpZ` is C46's
(`Smith2`); `KRep`, `Kr`, `oS`, `Dn`, `covSys`, `prodFun`, `thetaSys`, `theta` are C47's (`RingK`);
`InK`, `PayA`, `CoefB`, `Good`, `G0` are C48's (`Cleanliness`); `finOneDnEmpty` is C48b's
(`DanceXi`); `KF`, `kJ`, `PsiF`, `ShInvF`, `shInvC` are C49's (`FoldOdd`); `PairRel` is C50's
(`GlueDance`); `RA`, `red4`, `kap`, `Cong2` are C50b's (`DanceMod2`).

Throughout, `A := ℤ_[2]` and `Sys := Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]` (written out in full in the
statements); `e∅ : Dn ∅` is written `⟨∅, Finset.empty_subset _⟩`.

The three new definitions are written exactly as in the file: `uSys`, `eI`, `GPsi`.
-/

@[expose] public section

noncomputable section

namespace ArmsEven

/-- Definitions (new) of `C50c_the_arms_of_the_even_families.md`: the unit system,
`uSys Δ m _ = if Δ = ∅ ∧ m = 0 then 1 else 0`. -/
def uSys : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] := fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0

/-- Definitions (new) of `C50c_the_arms_of_the_even_families.md`:
`eI i = (i + 2) / 2 - (i + 1) / 2` (`1` for even `i`, `0` for odd `i`). -/
def eI (i : ℕ) : ℕ := (i + 2) / 2 - (i + 1) / 2

/-- Definitions (new) of `C50c_the_arms_of_the_even_families.md`: the operator `Ψ_j` with payment
`4 (y + e)`, written in positions shifted by `e` from its own:
`GPsi e j Δ m y = if Δ = ∅ then (if m = 0 then 4 * (y + e) else kJ j m) else 0`. -/
def GPsi (e j : ℕ) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] := fun Δ m y =>
  if Δ = ∅ then (if m = 0 then 4 * (y + (e : ℤ_[2])) else FoldOdd.kJ j m) else 0

end ArmsEven
