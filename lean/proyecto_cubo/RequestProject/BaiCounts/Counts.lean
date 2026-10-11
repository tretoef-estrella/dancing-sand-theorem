module

public import RequestProject.MainTheorem.All

/-!
# `C34_bais_counts.md`: Part S — the counts of the families

Encodings (namespace `BaiCounts`):

* `λ` is written `lam`; `k λ = (ds λ).length`, `|I λ| = Dance.mCount (ds λ)` (C32 `ds`, C13
  `mCount`).
* `c1 lam` is the file's `c₁(λ) := 2 ^ (mCount (ds λ) + (ds λ).length − 2)` if `(ds λ).length ≥ 2`
  and `0` otherwise (the number of small clocks with `a = 1`).
* `FamDec.L n` is the list of families of C31 and `FamDec.m lam n = (L n).count lam`; the sum over
  the positions of `L n` is a sum over `j : Fin (L n).length`, with `λ_j = (L n).get j`.
-/

@[expose] public section

namespace BaiCounts

open Finset Families

/-- *Part F* (F2) / *Part S* (S3) of `C34_bais_counts.md`: `c₁(λ)`, the number of small clocks
with `a = 1`: `2 ^ (mCount (ds λ) + (ds λ).length − 2)` if `(ds λ).length ≥ 2`, and `0`
otherwise. -/
def c1 (lam : ℕ) : ℕ :=
  if 2 ≤ (ds lam).length then 2 ^ (Dance.mCount (ds lam) + (ds lam).length - 2) else 0

/-! ### (S1) -/

/-- **(S1)** of `C34_bais_counts.md`: for every `λ`,
`Fintype.card (Dance.Idx (ds λ)) = 2 ^ ((ds λ).length + mCount (ds λ))` (`= dim T(λ)`).
From C13 `card_Idx`. -/
theorem S1 (lam : ℕ) :
    Fintype.card (Dance.Idx (ds lam)) = 2 ^ ((ds lam).length + Dance.mCount (ds lam)) :=
  Dance.card_Idx _

/-! ### (S2) -/

/-- The weight `2^{k(λ) + |I(λ)|}` of a family (auxiliary for (S2) of `C34_bais_counts.md`). -/
abbrev wt (lam : ℕ) : ℕ := 2 ^ ((ds lam).length + Dance.mCount (ds lam))

/-- `2^{k+|I|}` of `2l + 1` is twice that of `l` (auxiliary for (S2) of `C34_bais_counts.md`). -/
lemma wt_odd (l : ℕ) : wt (2 * l + 1) = 2 * wt l := by
  simp only [wt, ds_odd, List.length_cons, Dance.mCount]
  rw [show (ds l).length + 1 + Dance.mCount (ds l) = (ds l).length + Dance.mCount (ds l) + 1 by
    ring, pow_succ]
  ring

/-- `2^{k+|I|}` of `2l + 2` is four times that of `l` (auxiliary for (S2) of `C34_bais_counts.md`). -/
lemma wt_even (l : ℕ) : wt (2 * l + 2) = 4 * wt l := by
  simp only [wt, ds_even, List.length_cons, Dance.mCount]
  rw [show (ds l).length + 1 + (Dance.mCount (ds l) + 1) =
    (ds l).length + Dance.mCount (ds l) + 2 by ring, pow_add]
  ring

/-- `2^{k+|I|}` of `0` is `1` (auxiliary for (S2) of `C34_bais_counts.md`). -/
lemma wt_zero : wt 0 = 1 := by simp [wt, ds_zero, Dance.mCount]

/-- The rule `Σ_{μ ∈ Vdot λ} 2^{k(μ)+|I(μ)|} = 2 · 2^{k(λ)+|I(λ)|}` of the sketch of (S2) of
`C34_bais_counts.md`. -/
lemma sum_wt_Vdot (lam : ℕ) : ((FamDec.Vdot lam).map wt).sum = 2 * wt lam := by
  induction lam using Nat.strong_induction_on with
  | _ lam ih =>
    rcases cases3 lam with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [FamDec.Vdot_zero]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, wt_zero]
      rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, wt_odd, wt_zero]
    · rw [FamDec.Vdot_odd]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [wt_even, wt_odd]
      ring
    · rw [FamDec.Vdot_even, List.map_append, List.sum_append, List.map_map]
      have h1 : ((FamDec.Vdot l).map (wt ∘ fun ν => 2 * ν + 1)).sum =
          2 * ((FamDec.Vdot l).map wt).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        exact List.map_congr_left fun ν _ => wt_odd ν
      rw [h1, ih l (by omega)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [wt_odd, wt_even]
      ring

/-- A list sum over a `flatMap` (auxiliary for (S2) of `C34_bais_counts.md`). -/
lemma sum_map_flatMap (l : List ℕ) (g : ℕ → List ℕ) (w : ℕ → ℕ) :
    ((l.flatMap g).map w).sum = (l.map fun a => ((g a).map w).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- `Σ_{λ ∈ L n} 2^{k(λ)+|I(λ)|} = 2^n`, as a list sum (auxiliary for (S2) of
`C34_bais_counts.md`). -/
lemma sum_wt_L (n : ℕ) : ((FamDec.L n).map wt).sum = 2 ^ n := by
  induction n with
  | zero => simp [FamDec.L, wt_zero]
  | succ n ih =>
    rw [show FamDec.L (n + 1) = (FamDec.L n).flatMap FamDec.Vdot from rfl, sum_map_flatMap]
    simp_rw [sum_wt_Vdot]
    rw [List.sum_map_mul_left, ih, pow_succ]
    ring

/-- **(S2)** of `C34_bais_counts.md`: for every `n`,
`Σ_{j : Fin (L n).length} 2 ^ ((ds λ_j).length + mCount (ds λ_j)) = 2 ^ n`, `λ_j = (L n).get j`.
By induction on `n` with the rule `Vdot`. -/
theorem S2 (n : ℕ) :
    ∑ j : Fin (FamDec.L n).length,
      2 ^ ((ds ((FamDec.L n).get j)).length + Dance.mCount (ds ((FamDec.L n).get j))) = 2 ^ n := by
  rw [← sum_wt_L n, ← Fin.sum_univ_fun_getElem]
  rfl

/-! ### (S3) -/

/-- `ds 1 = [false]` (auxiliary for (S3) of `C34_bais_counts.md`). -/
lemma ds_one : ds 1 = [false] := by rw [show (1 : ℕ) = 2 * 0 + 1 by rfl, ds_odd, ds_zero]

/-- `ds 2 = [true]` (auxiliary for (S3) of `C34_bais_counts.md`). -/
lemma ds_two : ds 2 = [true] := by rw [show (2 : ℕ) = 2 * 0 + 2 by rfl, ds_even, ds_zero]

/-- **(S3)** of `C34_bais_counts.md`, second item: the families with `(ds λ).length ≤ 1` and
`λ ≥ 1` are exactly `λ = 1` and `λ = 2`. -/
theorem S3_short (lam : ℕ) : (1 ≤ lam ∧ (ds lam).length ≤ 1) ↔ (lam = 1 ∨ lam = 2) := by
  constructor
  · rintro ⟨h1, hk⟩
    have hb := B0b lam
    have hlt := Rulers.oE_lt (Windows.Ids (ds lam)) (ds lam).length
      (fun t ht => mem_range.1 (MainTheorem.S3_subset lam ht))
    have hpow : 2 ^ (ds lam).length ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
    unfold Rulers.oE at hlt
    omega
  · rintro (rfl | rfl)
    · simp [ds_one]
    · simp [ds_two]

/-- The per-family identity behind (S3) of `C34_bais_counts.md`: for `λ ≥ 1`,
`4 c₁(λ) + [λ = 1]·2 + [λ = 2]·4 = 2^{k(λ)+|I(λ)|}`. -/
lemma c1_identity (lam : ℕ) (hlam : 1 ≤ lam) :
    c1 lam * 4 + (if lam = 1 then 2 else 0) + (if lam = 2 then 4 else 0) = wt lam := by
  have hk := MainTheorem.S2_length lam hlam
  by_cases h2 : 2 ≤ (ds lam).length
  · have hne1 : lam ≠ 1 := fun h => by subst h; simp [ds_one] at h2
    have hne2 : lam ≠ 2 := fun h => by subst h; simp [ds_two] at h2
    rw [c1, if_pos h2, if_neg hne1, if_neg hne2, wt,
      show (ds lam).length + Dance.mCount (ds lam) =
        (Dance.mCount (ds lam) + (ds lam).length - 2) + 2 by omega, pow_add]
    ring
  · rw [c1, if_neg h2]
    rcases (S3_short lam).1 ⟨hlam, by omega⟩ with rfl | rfl
    · simp [wt, ds_one, Dance.mCount]
    · simp [wt, ds_two, Dance.mCount]

/-- **(S3)** of `C34_bais_counts.md`, first item: for every `n ≥ 1`,
`Σ_j c₁(λ_j) · 4 + 2 · m 1 n + 4 · m 2 n = 2 ^ n`, `λ_j = (L n).get j`. -/
theorem S3 (n : ℕ) (hn : 1 ≤ n) :
    (∑ j : Fin (FamDec.L n).length, c1 ((FamDec.L n).get j) * 4) + 2 * FamDec.m 1 n +
      4 * FamDec.m 2 n = 2 ^ n := by
  have h := sum_wt_L n
  have e : ((FamDec.L n).map wt).sum = ((FamDec.L n).map fun lam => c1 lam * 4).sum +
      ((FamDec.L n).map fun lam => if lam = 1 then 2 else 0).sum +
      ((FamDec.L n).map fun lam => if lam = 2 then 4 else 0).sum := by
    rw [← List.sum_map_add, ← List.sum_map_add]
    congr 1
    exact List.map_congr_left fun lam hl => (c1_identity lam (FamDec.M3 n hn lam hl).1).symm
  rw [FamDec.sum_map_eq_count_mul _ _ 1 2 (fun _ _ => rfl),
    FamDec.sum_map_eq_count_mul _ _ 2 4 (fun _ _ => rfl)] at e
  have hsum : ∑ j : Fin (FamDec.L n).length, c1 ((FamDec.L n).get j) * 4 =
      ((FamDec.L n).map fun lam => c1 lam * 4).sum :=
    Fin.sum_univ_fun_getElem (FamDec.L n) (fun lam => c1 lam * 4)
  rw [← h, e, hsum]
  simp only [FamDec.m]
  ring

end BaiCounts
