module

public import RequestProject.FormalAct.All
public import RequestProject.DanceXi.All
public import RequestProject.FoldCube.All

/-!
# `C49_the_fold_law_on_the_odd_families.md`: Definitions (new)

Namespace `FoldOdd`. Only the new definitions of the file are introduced here: `cst`, `chC`,
`shC`, `shInvC`, `ChF`, `ShF`, `ShInvF` (for any commutative ring `A`) and `KF`, `kJ`, `PsiF`,
`SigF` (over `ℤ_[2]`). Everything else (C40 `FormalOps.Bf`, `Bf.dg`, `Bf.fd`, C20
`Doubling.dfi`, …) is reused unchanged.

Encodings:
* `cst a : Bf A` is the series with `coef m f = a m` (constant in the floor `f`).
* `chC m = dfi m`, `shC m = dfi (m + 1)`, as functions `ℕ → A`.
* `shInvC` is defined by well-founded recursion through a sum over `Fin m`; the two equations of
  the file, `shInvC 0 = 1` and `shInvC m = − Σ_{b ∈ range m} C(m, b) * shC (m − b) * shInvC b`
  for `m ≥ 1`, are the lemmas `shInvC_zero` and `shInvC_eq`.
-/

@[expose] public section

noncomputable section

namespace FoldOdd

open FormalOps Doubling Finset

variable {A : Type*} [CommRing A]

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: the series with constant
coefficients, `cst a := ⟨fun m _ => a m⟩`. -/
def cst (a : ℕ → A) : Bf A := ⟨fun m _ => a m⟩

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `chC m := dfi m`. -/
def chC (m : ℕ) : A := dfi m

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `shC m := dfi (m + 1)`. -/
def shC (m : ℕ) : A := dfi (m + 1)

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `shInvC` by strong
recursion, `shInvC 0 = 1` and `shInvC m = − Σ_{b < m} C(m, b) * shC (m − b) * shInvC b` for
`m ≥ 1` (see `shInvC_zero`, `shInvC_eq`). -/
def shInvC : ℕ → A
  | 0 => 1
  | m + 1 => -∑ b : Fin (m + 1), ((m + 1).choose b : A) * shC (m + 1 - b) * shInvC b
decreasing_by exact b.isLt

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: the first defining equation
`shInvC 0 = 1`. -/
@[simp] lemma shInvC_zero : shInvC (A := A) 0 = 1 := by
  rw [shInvC]

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: the second defining
equation, for `m ≥ 1`, `shInvC m = − Σ_{b ∈ range m} C(m, b) * shC (m − b) * shInvC b`. -/
lemma shInvC_eq (m : ℕ) (hm : 1 ≤ m) :
    shInvC (A := A) m = -∑ b ∈ range m, (m.choose b : A) * shC (m - b) * shInvC b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [shInvC, Fin.sum_univ_eq_sum_range
    (fun b => (((k + 1).choose b : ℕ) : A) * shC (k + 1 - b) * shInvC b)]

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `ChF := cst chC`. -/
def ChF : Bf A := cst chC

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `ShF := cst shC`. -/
def ShF : Bf A := cst shC

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `ShInvF := cst shInvC`. -/
def ShInvF : Bf A := cst shInvC

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`:
`KF j := (ChF − ((−1 : ℤ_[2]) ^ j) • 1) * ShInvF` over `ℤ_[2]`. -/
def KF (j : ℕ) : Bf ℤ_[2] := (ChF - ((-1 : ℤ_[2]) ^ j) • (1 : Bf ℤ_[2])) * ShInvF

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`: `kJ j m := (KF j).coef m 0`. -/
def kJ (j m : ℕ) : ℤ_[2] := (KF j).coef m 0

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`:
`PsiF j := Bf.dg (fun f => 4 * f + 2 * j) + KF j` (the paper's `Ψ_j`). -/
def PsiF (j : ℕ) : Bf ℤ_[2] := Bf.dg (fun f => 4 * (f : ℤ_[2]) + 2 * (j : ℤ_[2])) + KF j

/-- Definitions (new) of `C49_the_fold_law_on_the_odd_families.md`:
`SigF c := Bf.dg (fun f => 4 * (f + c)) + Bf.fd 1` (the paper's `Σ_c = F + 4(D + c)`). -/
def SigF (c : ℕ) : Bf ℤ_[2] := Bf.dg (fun f => 4 * ((f : ℤ_[2]) + c)) + Bf.fd 1

/-- Definitions (new): simp lemma, `(cst a).coef m f = a m`. -/
@[simp] lemma coef_cst (a : ℕ → A) (m : ℕ) (f : ℤ) : (cst a).coef m f = a m := rfl

end FoldOdd
