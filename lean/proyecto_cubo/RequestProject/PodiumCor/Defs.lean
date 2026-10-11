module

public import RequestProject.BaiCounts.All
public import RequestProject.PodiumWalk.All

/-!
# `C36_the_podium_corollary.md`: the definitions (*Definitions*)

Namespace `PodiumCor`.  Nothing listed in the Setting of `C36_the_podium_corollary.md` is
redefined; this file only adds the objects of its *Definitions* section.

## Encodings

* **Layers.** For an additive commutative group `G` and `j : ℕ`,
  `layer G j := Nat.card (2^j G ⧸ (2^{j+1} G as a subgroup of 2^j G))`, written with C34's
  `BaiCounts.twoPow` exactly as in the file (`Nat.card` is `0` for an infinite quotient).
* **Exponents.** `cExp G r := sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ layer G (e − 1)}` (`sSup` in `ℕ`, which
  is `0` for an empty or unbounded set), exactly as in the file.
* **The exponents read off the families** are multisets of natural numbers (`Multiset ℕ`).  For a
  family `λ` (`lam`), `d = Families.ds lam`, `k = d.length`, `I = Windows.Ids d`, `s = I.card`,
  `N = 2 ^ s`:
  - `smallExps lam := Σ_{a ∈ Finset.Ico 1 k} Multiset.replicate (2 ^ (s + k − 1 − a)) a`;
  - `bigExps lam 0` is the multiset of the `(yPool0 d q).toNat`, `q < N − 1`, and
    `bigExps lam (i + 1)` is the multiset of the `(yPool d (i + 1) p).toNat`, `p < N`
    (written as `Multiset.map` over `(Finset.range _).val`);
  - `famExps lam i := smallExps lam + bigExps lam i`;
  - `exps n := ((FamDec.L n).map (fun lam => famExps lam ((n − lam) / 2))).sum`.
  (`s` is `(Windows.Ids d).card`, which is `Dance.mCount d` by C33 `S3_card`.)
* **`g`.** `gmax N : ℤ` is `max_{1 ≤ x < N} φ(x)` (as `Finset.sup'` over `Finset.Ico 1 N`) when
  `N ≥ 2`, and `0` when `N ≤ 1`; its defining property is (g0) (`g0`).
* `S n`, the 2-part of the sandpile group of the cube, is `CubeLaplacian.Syl2 (CubeLaplacian.K n)`
  (an additive subgroup, viewed as an additive commutative group), written out.
-/

@[expose] public section

namespace PodiumCor

open Finset

/-- *Definitions* of `C36_the_podium_corollary.md` (**Layers**): for an additive commutative group
`G` and `j : ℕ`, `layer G j := |2^j G / 2^{j+1} G|`, as
`Nat.card (twoPow G j ⧸ (twoPow G (j + 1)).addSubgroupOf (twoPow G j))`. -/
noncomputable def layer (G : Type*) [AddCommGroup G] (j : ℕ) : ℕ :=
  Nat.card (BaiCounts.twoPow G j ⧸
    (BaiCounts.twoPow G (j + 1)).addSubgroupOf (BaiCounts.twoPow G j))

/-- *Definitions* of `C36_the_podium_corollary.md` (**Exponents**):
`cExp G r := sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ layer G (e − 1)}` (`sSup` in `ℕ`). -/
noncomputable def cExp (G : Type*) [AddCommGroup G] (r : ℕ) : ℕ :=
  sSup {e : ℕ | 1 ≤ e ∧ 2 ^ r ≤ layer G (e - 1)}

/-- *Definitions* of `C36_the_podium_corollary.md` (the small exponents of the family `λ`):
`smallExps λ := Σ_{a ∈ Ico 1 k} replicate (2 ^ (s + k − 1 − a)) a`, with `d = ds λ`,
`k = d.length`, `s = (Ids d).card`. -/
def smallExps (lam : ℕ) : Multiset ℕ :=
  ∑ a ∈ Ico 1 (Families.ds lam).length,
    Multiset.replicate (2 ^ ((Windows.Ids (Families.ds lam)).card +
      (Families.ds lam).length - 1 - a)) a

/-- *Definitions* of `C36_the_podium_corollary.md` (the big exponents of the family `λ` at shift
`i`): `bigExps λ 0` is the multiset of the `(yPool0 d q).toNat`, `q < N − 1`, and for `i ≥ 1`,
`bigExps λ i` is the multiset of the `(yPool d i p).toNat`, `p < N` (`N = 2 ^ (Ids d).card`). -/
noncomputable def bigExps (lam : ℕ) : ℕ → Multiset ℕ
  | 0 => (range (2 ^ (Windows.Ids (Families.ds lam)).card - 1)).val.map
      (fun q => (FamilyGroup.yPool0 (Families.ds lam) q).toNat)
  | i + 1 => (range (2 ^ (Windows.Ids (Families.ds lam)).card)).val.map
      (fun p => (FamilyGroup.yPool (Families.ds lam) (i + 1) p).toNat)

/-- *Definitions* of `C36_the_podium_corollary.md`: `famExps λ i := smallExps λ + bigExps λ i`. -/
noncomputable def famExps (lam i : ℕ) : Multiset ℕ := smallExps lam + bigExps lam i

/-- *Definitions* of `C36_the_podium_corollary.md`:
`exps n := ((L n).map (fun λ => famExps λ ((n − λ) / 2))).sum` (the extra `ℤ_2` of the family
`λ = n` at shift `0` is left out). -/
noncomputable def exps (n : ℕ) : Multiset ℕ :=
  ((FamDec.L n).map (fun lam => famExps lam ((n - lam) / 2))).sum

/-- *Definitions* of `C36_the_podium_corollary.md` (**`g`**): `gmax N := max_{1 ≤ x < N} φ(x)` for
`N ≥ 2` (as `Finset.sup'` over `Ico 1 N`), and `0` for `N ≤ 1`. -/
noncomputable def gmax (N : ℕ) : ℤ :=
  if h : 1 < N then (Ico 1 N).sup' ⟨1, by simp; omega⟩ Rulers.phi else 0

/-- **(g0)** of `C36_the_podium_corollary.md`: for `N ≥ 2`, `gmax N` is a value `φ(x)` with
`1 ≤ x < N`, and `φ(x) ≤ gmax N` for every `1 ≤ x < N`. -/
theorem g0 (N : ℕ) (hN : 2 ≤ N) :
    (∃ x, 1 ≤ x ∧ x < N ∧ gmax N = Rulers.phi x) ∧
      ∀ x, 1 ≤ x → x < N → Rulers.phi x ≤ gmax N := by
  have h : 1 < N := by omega
  refine ⟨?_, fun x h1 h2 => ?_⟩
  · obtain ⟨x, hx, he⟩ := exists_mem_eq_sup' (⟨1, by simp; omega⟩ : (Ico 1 N).Nonempty) Rulers.phi
    simp only [mem_Ico] at hx
    exact ⟨x, hx.1, hx.2, by rw [gmax, dif_pos h, he]⟩
  · rw [gmax, dif_pos h]
    exact le_sup' Rulers.phi (by simp; omega)

end PodiumCor
