module

public import RequestProject.FoldLaw.All
public import RequestProject.PodiumCor.All
public import RequestProject.Mirror.All

/-!
# `C53_the_small_cases.md`: Part T — the case `n = 2`

* (T0) `T0`: `Syl2 (K 2) ≃+ ZMod 4`.
* (T1) `T1`: `PodiumCor.gmax 2 = 1`.
* (G1-2) `G1_two`: `PodiumCor.G1` at `n = 2`.

Proof of (T0): the exponent multiset of `Syl2 (K 2)` (C36 `exps 2`) is `{2}` (C37 (X4) at
`e = 1`), so C36 (E1) gives `layer j = 2` for `j < 2` and `layer j = 1` for `j ≥ 2`.  Writing
`Syl2 (K 2) ≃+ Π_i ZMod (2 ^ f i)` (finite abelian `2`-group), the layers count the `i` with
`j < f i`, so there is exactly one factor, and it has `f = 2`.
-/

@[expose] public section

noncomputable section

namespace SmallCases

open CubeLaplacian BaiCounts PodiumCor Families

/-- `L 2 = [2]` (auxiliary for Part T of `C53_the_small_cases.md`). -/
lemma L_two : FamDec.L 2 = [2] := by
  have v0 := FamDec.Vdot_zero
  have v1 : FamDec.Vdot 1 = [2] := FamDec.Vdot_odd 0
  rw [FamDec.L_succ, FamDec.L_succ, FamDec.L_zero]
  simp [v0, v1]

/-- `famExps 1 0 = 0` (auxiliary for Part T of `C53_the_small_cases.md`). -/
lemma famExps_one_zero : famExps 1 0 = 0 := by
  have hc : (Windows.Ids (ds 1)).card = 0 := by rw [PodiumCor.ds_one]; decide
  have hl : (ds 1).length = 1 := by rw [PodiumCor.ds_one]; rfl
  unfold famExps smallExps bigExps
  rw [hc, hl]
  simp

/-- `exps 2 = {2}`, i.e. `Syl_2 K(Q_2) ≅ ℤ/4` (auxiliary for Part T of
`C53_the_small_cases.md`). -/
lemma exps_two : exps 2 = {2} := by
  have h := Mirror.X4 1 le_rfl
  rw [show (2 : ℕ) ^ 1 = 2 from rfl, show 2 - 1 = 1 from rfl, famExps_one_zero] at h
  unfold exps
  rw [L_two]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show (2 - 2) / 2 = 0 from rfl, h]
  rfl

/-- The layers of `ZMod (2 ^ f)`: `layer (ZMod (2 ^ f)) j = 2 ^ (if j < f then 1 else 0)`
(auxiliary for Part T of `C53_the_small_cases.md`). -/
lemma layer_zmod (f j : ℕ) : layer (ZMod (2 ^ f)) j = 2 ^ (if j < f then 1 else 0) := by
  rw [← layer_Q_pow f j]
  exact (layer_congr (Mirror.QequivZMod f).toAddEquiv j).symm

/-- The layers of `Syl2 (K 2)`: `2` for `j < 2`, `1` for `j ≥ 2` (auxiliary for Part T of
`C53_the_small_cases.md`). -/
lemma layer_two (j : ℕ) :
    layer (Syl2 (K 2)) j = 2 ^ (if j < 2 then 1 else 0) := by
  rw [E1 2 (by norm_num) j, exps_two]
  rw [← Multiset.cons_zero]
  split_ifs with h
  · rw [Multiset.countP_cons_of_pos _ h, Multiset.countP_zero]
  · rw [Multiset.countP_cons_of_neg _ h, Multiset.countP_zero]

/-- **(T0)** of `C53_the_small_cases.md` (Part T):
`Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 2) ≃+ ZMod 4)`. -/
theorem T0 : Nonempty (CubeLaplacian.Syl2 (CubeLaplacian.K 2) ≃+ ZMod 4) := by
  classical
  haveI := K_finite 2
  obtain ⟨ι, hι, f, hf1, ⟨e⟩⟩ := FoldLaw.two_group_structure (Syl2 (K 2)) fun x => by
    obtain ⟨k, hk⟩ := x.2
    exact ⟨k, Subtype.ext hk⟩
  have hL : ∀ j, (2 : ℕ) ^ (∑ i, if j < f i then 1 else 0) = 2 ^ (if j < 2 then 1 else 0) := by
    intro j
    rw [← layer_two j, layer_congr e j, layer_pi,
      Finset.prod_congr rfl fun i _ => layer_zmod (f i) j, Finset.prod_pow_eq_pow_sum]
  have h0 := Nat.pow_right_injective le_rfl (hL 0)
  have h1 := Nat.pow_right_injective le_rfl (hL 1)
  have h2 := Nat.pow_right_injective le_rfl (hL 2)
  simp only at h0 h1 h2
  have hc : Fintype.card ι = 1 := by
    rw [Finset.sum_congr rfl fun i _ => if_pos (show 0 < f i from hf1 i)] at h0
    simpa using h0
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 hc
  haveI : Unique ι := ⟨⟨i0⟩, hi0⟩
  rw [Fintype.sum_unique] at h1 h2
  have hf : f default = 2 := by
    split_ifs at h1 h2 with a b <;> omega
  exact ⟨e.trans ((AddEquiv.piUnique _).trans
    (ZMod.ringEquivCongr (by rw [hf]; norm_num)).toAddEquiv)⟩

/-- **(T1)** of `C53_the_small_cases.md` (Part T): `PodiumCor.gmax 2 = 1` (`gmax 2 = φ(1) = 1`). -/
theorem T1 : PodiumCor.gmax 2 = 1 := PodiumCor.gmax_two

/-- **(G1-2)** of `C53_the_small_cases.md` (Part T): `PodiumCor.G1` at `n = 2`, in exactly its
form: `(c 1 : ℤ) = max (gmax 2) (v_2(2) + 2 − 1)` (both sides are `2`), and the second clause
(`2 ≤ r ≤ 1`) is empty. -/
theorem G1_two :
    (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 2)) 1 : ℤ) =
        max (PodiumCor.gmax 2) ((Rulers.v2 2 : ℤ) + 2 - 1) ∧
      ∀ r, 2 ≤ r → r ≤ 2 - 1 →
        (PodiumCor.cExp (CubeLaplacian.Syl2 (CubeLaplacian.K 2)) r : ℤ) = PodiumCor.gmax 2 := by
  refine ⟨?_, fun r hr2 hr => by omega⟩
  have hc : cExp (Syl2 (K 2)) 1 = 2 :=
    cExp_eq_of_counts_nat 2 1 2 (by norm_num) le_rfl (by norm_num)
      (by rw [exps_two]; decide) (by rw [exps_two]; decide)
  rw [hc, T1, v2_two_mod_four 2 (by norm_num)]
  norm_num

end SmallCases
