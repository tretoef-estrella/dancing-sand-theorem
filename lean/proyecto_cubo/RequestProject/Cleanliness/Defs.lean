module

public import RequestProject.RingK.All
public import RequestProject.Smith2.Defs

/-!
# `C48_cleanliness_one_move.md`: Definitions (new)

Namespace `Cleanliness`. Nothing listed in the Setting of the file is redefined: `KRep`, `Kr`,
`theta`, `RS`, `oS`, `Dn`, `covSys`, `thetaSys`, `prodFun` are C47's (`RingK`), `Bf`, `tw00`,
`tw11`, `tw10`, `tw01`, `vplus`, `vprime` are C40's (`FormalOps`), `dfi` is C20's
(`Doubling.dfi`), `MAgree`, `twP`, `twC`, `twB`, `twD`, `vsplit`, `CleanStep` are C40b's
(`FormalDance`) and `XiOpZ` is C46's (`Smith2.XiOpZ`).

The coefficient functions of covariant systems have type `Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]`
(`Γ Δ m y`). The new definitions are written exactly as in the file:

* `InK`, `PayA` (condition (a)), `CoefB` (condition (b)), `Good`;
* the blocks `GB`, `GC`, `GP`, `GD` of the twist move at level `h` (`2 ^ h` is
  `(2 : ℤ_[2]) ^ h`; `GD` is defined by cases on the order, `0` and `q + 1`);
* `vsplitG` (the `V`-split of the coefficient functions);
* `splitDn P h hP : Dn P × Fin 2 ≃ Dn (insert h P)`, `(D, 0) ↦ D`, `(D, 1) ↦ insert h D`, with
  inverse `D ↦ (D.erase h, if h ∈ D then 1 else 0)`;
* `G0 α η z` (the operator at level `0`).
-/

@[expose] public section

noncomputable section

namespace Cleanliness

open RingK FormalOps FormalDance Doubling Finset

/-- Definitions (new) 1 of `C48_cleanliness_one_move.md`: every coefficient function of `Γ`
lies in the class `Kr`. -/
def InK (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Prop := ∀ Δ m, Γ Δ m ∈ Kr

/-- Definitions (new) 2 of `C48_cleanliness_one_move.md`, condition (a): the payments are
`≡ 0 (mod 4)`. -/
def PayA (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Prop := ∀ y, ∃ z, Γ ∅ 0 y = 4 * z

/-- Definitions (new) 3 of `C48_cleanliness_one_move.md`, condition (b): the diagonal
coefficients of `F` are units. -/
def CoefB (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Prop := ∀ y, IsUnit (Γ ∅ 1 y)

/-- Definitions (new) 4 of `C48_cleanliness_one_move.md`: the class of good systems. -/
def Good (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Prop := InK Γ ∧ PayA Γ ∧ CoefB Γ

/-- Definitions (new) 5 of `C48_cleanliness_one_move.md`: the block `B` of the twist move,
`GB Γ Δ q y = dfi q * Γ Δ (2q) y`. -/
def GB (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] :=
  fun Δ q y => dfi q * Γ Δ (2 * q) y

/-- Definitions (new) 5 of `C48_cleanliness_one_move.md`: the block `C` of the twist move at
level `h`, `GC h Γ Δ q y = dfi q * Γ Δ (2q) (y + 2^h)`. -/
def GC (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] :=
  fun Δ q y => dfi q * Γ Δ (2 * q) (y + (2 : ℤ_[2]) ^ h)

/-- Definitions (new) 5 of `C48_cleanliness_one_move.md`: the pivot block `P` of the twist move
at level `h`, `GP h Γ Δ q y = dfi (q + 1) * Γ Δ (2q + 1) (y + 2^h)`. -/
def GP (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] :=
  fun Δ q y => dfi (q + 1) * Γ Δ (2 * q + 1) (y + (2 : ℤ_[2]) ^ h)

/-- Definitions (new) 5 of `C48_cleanliness_one_move.md`: the block `D` of the twist move,
`GD Γ Δ 0 y = 0` and `GD Γ Δ (q + 1) y = (2q + 2) * dfi (q + 1) * Γ Δ (2q + 1) y`. -/
def GD (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]
  | _, 0, _ => 0
  | Δ, q + 1, y => ((2 * q + 2 : ℕ) : ℤ_[2]) * dfi (q + 1) * Γ Δ (2 * q + 1) y

/-- Definitions (new) 6 of `C48_cleanliness_one_move.md`: the `V`-split of the coefficient
functions at level `h`. -/
def vsplitG (h : ℕ) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] :=
  fun Δ m y => if h ∈ Δ then Γ (Δ.erase h) (m + 1) y else Γ Δ m y

/-- Definitions (new) 7 of `C48_cleanliness_one_move.md`: for `h ∉ P`, the equivalence
`Dn P × Fin 2 ≃ Dn (insert h P)`, `(D, 0) ↦ D`, `(D, 1) ↦ insert h D`, with inverse
`D ↦ (D.erase h, if h ∈ D then 1 else 0)`. -/
def splitDn (P : Finset ℕ) (h : ℕ) (hP : h ∉ P) : Dn P × Fin 2 ≃ Dn (insert h P) where
  toFun q := if q.2 = 0 then ⟨q.1.1, q.1.2.trans (subset_insert h P)⟩
    else ⟨insert h q.1.1, insert_subset_insert h q.1.2⟩
  invFun D := (⟨D.1.erase h, fun t ht => by
      have h1 := mem_erase.1 ht
      have h2 := D.2 h1.2
      rcases mem_insert.1 h2 with h3 | h3
      · exact absurd h3 h1.1
      · exact h3⟩, if h ∈ D.1 then 1 else 0)
  left_inv := by
    rintro ⟨D, g⟩
    have hD : h ∉ D.1 := fun hh => hP (D.2 hh)
    fin_cases g
    · simp [hD]
    · simp [hD, erase_insert hD]
  right_inv := by
    rintro ⟨D, hD⟩
    by_cases hh : h ∈ D
    · simp [hh, insert_erase hh]
    · simp [hh]

/-- Definitions (new) 8 of `C48_cleanliness_one_move.md`: the operator at level `0`,
`2^α (D + c) + ηF + Σ_{m ≥ 2} z_m F^{(m)}`, as coefficient functions. -/
def G0 (α : ℕ) (η : ℤ_[2]) (z : ℕ → ℤ_[2]) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] :=
  fun Δ m y => if Δ = ∅ then (if m = 0 then 2 ^ α * y else if m = 1 then η else z m) else 0

end Cleanliness
