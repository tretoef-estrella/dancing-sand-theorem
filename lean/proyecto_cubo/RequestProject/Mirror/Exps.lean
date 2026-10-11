module

public import RequestProject.Mirror.Theorem
public import RequestProject.Mirror.Fit

/-!
# `C37_the_mirror_that_doubles.md`: Part X — Corollary 1.7 for the exponents

Namespace `Mirror`.  C16's `FamilyGroup.yPool`, `yPool0`; C36's `PodiumCor.smallExps`,
`bigExps`, `famExps`, `exps` (multisets of natural numbers) are used directly.  For `e ≥ 1` and
odd `λ < 2^e − 1` the shift is `i = (2^e − 1 − λ) / 2`, written out.
-/

@[expose] public section

namespace Mirror

open Finset Families

/-! ### (X1) -/

/-- **(X1)** of `C37_the_mirror_that_doubles.md`: let `e ≥ 1`, `λ` odd with `λ < 2^e − 1` and
`i := (2^e − 1 − λ) / 2`.  Then `yPool (ds (λ + 1)) i j = yPool (ds λ) i (j / 2)` for every `j`:
the raw sequence of `(λ + 1, i)` in o-order is that of `(λ, i)` with every entry written twice.
From (A2), (A3), (C1) and (F2). -/
theorem X1 (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) (j : ℕ) :
    FamilyGroup.yPool (ds (lam + 1)) ((2 ^ e - 1 - lam) / 2) j =
      FamilyGroup.yPool (ds lam) ((2 ^ e - 1 - lam) / 2) (j / 2) := by
  unfold FamilyGroup.yPool
  have h0 := A2_zero_notMem lam hodd
  have hseq : (fun j => Rulers.clock (ds (lam + 1)).length (Windows.Ids (ds (lam + 1)))
      ((2 ^ e - 1 - lam) / 2) (TheoremF.dancer (Windows.Ids (ds (lam + 1))) j)) =
      fun j => (fun q => Rulers.clock (ds lam).length (Windows.Ids (ds lam))
        ((2 ^ e - 1 - lam) / 2) (TheoremF.dancer (Windows.Ids (ds lam)) q)) (j / 2) := by
    funext j
    have hsub := TheoremF.lemma_0a (Windows.Ids (ds lam)) (j / 2)
    obtain ⟨hC, hC'⟩ := C1 e he lam hodd hlt hsub
    rcases Nat.even_or_odd' j with ⟨q, rfl | rfl⟩
    · have hd : TheoremF.dancer (Windows.Ids (ds (lam + 1))) (2 * q) =
          TheoremF.dancer (Windows.Ids (ds lam)) ((2 * q) / 2) := by
        rw [A2_Ids lam hodd, A3_even _ h0, show 2 * q / 2 = q by omega]
      rw [hd]; exact hC
    · have hd : TheoremF.dancer (Windows.Ids (ds (lam + 1))) (2 * q + 1) =
          insert 0 (TheoremF.dancer (Windows.Ids (ds lam)) ((2 * q + 1) / 2)) := by
        rw [A2_Ids lam hodd, A3_odd _ h0, show (2 * q + 1) / 2 = q by omega]
      rw [hd]; exact hC'
  have hN : 2 ^ Dance.mCount (ds (lam + 1)) = 2 * 2 ^ Dance.mCount (ds lam) := by
    rw [A2_mCount lam hodd, pow_succ, mul_comm]
  rw [hseq, hN]
  exact F2 (2 ^ Dance.mCount (ds lam)) (fun q => Rulers.clock (ds lam).length
    (Windows.Ids (ds lam)) ((2 ^ e - 1 - lam) / 2) (TheoremF.dancer (Windows.Ids (ds lam)) q)) j

/-! ### (X2), (X3) -/

/-- Doubling a sequence doubles its multiset of values:
`(range (2n)).map (g ∘ (· / 2)) = (range n).map g + (range n).map g` (auxiliary for (X2) of
`C37_the_mirror_that_doubles.md`). -/
lemma map_range_double {α : Type*} (g : ℕ → α) (n : ℕ) :
    (range (2 * n)).val.map (fun p => g (p / 2)) = (range n).val.map g + (range n).val.map g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [range_val, Multiset.range_succ, Multiset.map_cons] at ih ⊢
    rw [ih, show (2 * n + 1) / 2 = n by omega, show 2 * n / 2 = n by omega, Multiset.cons_add,
      Multiset.add_cons]

/-- **(X2)** of `C37_the_mirror_that_doubles.md`: let `e ≥ 1`, `λ` odd with `λ < 2^e − 1` and
`i := (2^e − 1 − λ) / 2`.  Then `bigExps (λ + 1) i = bigExps λ i + bigExps λ i`.  From (X1)
(`2^{s+1}` positions). -/
theorem X2 (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) :
    PodiumCor.bigExps (lam + 1) ((2 ^ e - 1 - lam) / 2) =
      PodiumCor.bigExps lam ((2 ^ e - 1 - lam) / 2) +
        PodiumCor.bigExps lam ((2 ^ e - 1 - lam) / 2) := by
  have hX := X1 e he lam hodd hlt
  have he2 : 2 ^ e % 2 = 0 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ]; omega
  obtain ⟨i', hi'⟩ : ∃ i', (2 ^ e - 1 - lam) / 2 = i' + 1 := ⟨(2 ^ e - 1 - lam) / 2 - 1, by omega⟩
  rw [hi'] at hX ⊢
  simp only [PodiumCor.bigExps]
  rw [A2_card lam hodd, pow_succ, mul_comm]
  have hf : (fun p => (FamilyGroup.yPool (ds (lam + 1)) (i' + 1) p).toNat) =
      fun p => (fun q => (FamilyGroup.yPool (ds lam) (i' + 1) q).toNat) (p / 2) := by
    funext p; rw [hX p]
  rw [hf]
  exact map_range_double (fun q => (FamilyGroup.yPool (ds lam) (i' + 1) q).toNat) _

/-- **(X3)** of `C37_the_mirror_that_doubles.md`: let `e ≥ 1`, `λ` odd with `λ < 2^e − 1` and
`i := (2^e − 1 − λ) / 2`.  Then `famExps (λ + 1) i = famExps λ i + famExps λ i`.  From (A4) and
(X2). -/
theorem X3 (e : ℕ) (he : 1 ≤ e) (lam : ℕ) (hodd : lam % 2 = 1) (hlt : lam < 2 ^ e - 1) :
    PodiumCor.famExps (lam + 1) ((2 ^ e - 1 - lam) / 2) =
      PodiumCor.famExps lam ((2 ^ e - 1 - lam) / 2) +
        PodiumCor.famExps lam ((2 ^ e - 1 - lam) / 2) := by
  unfold PodiumCor.famExps
  rw [A4 lam hodd, X2 e he lam hodd hlt]
  abel

/-! ### (X4) -/

/-- `ds (2^e − 1) = [false, …, false]` (`e` entries): the family `2^e − 1` has `k = e` and
`I = ∅` (auxiliary for (X4) of `C37_the_mirror_that_doubles.md`). -/
lemma ds_two_pow_sub_one (e : ℕ) : ds (2 ^ e - 1) = List.replicate e false := by
  induction e with
  | zero => simp [ds_zero]
  | succ e ih =>
    have : 2 ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 := by
      have := Nat.one_le_two_pow (n := e); rw [pow_succ]; omega
    rw [this, ds_odd, ih, List.replicate_succ]

/-- The family `2^e − 1` has `k = e` (auxiliary for (X4) of `C37_the_mirror_that_doubles.md`). -/
lemma length_ds_two_pow_sub_one (e : ℕ) : (ds (2 ^ e - 1)).length = e := by
  rw [ds_two_pow_sub_one, List.length_replicate]

/-- The family `2^e − 1` has `I = ∅` (auxiliary for (X4) of `C37_the_mirror_that_doubles.md`). -/
lemma Ids_ds_two_pow_sub_one (e : ℕ) : Windows.Ids (ds (2 ^ e - 1)) = ∅ := by
  rw [ds_two_pow_sub_one]
  induction e with
  | zero => rfl
  | succ e ih => rw [List.replicate_succ, Windows.Ids_cons, ih]; simp

/-- The integer fit of a sequence of length one is the sequence itself (auxiliary for (X4) of
`C37_the_mirror_that_doubles.md`). -/
lemma ifit_one (x : ℕ → ℤ) : AntitonicFit.ifit 1 x 0 = x 0 := by
  rw [AntitonicFit.ifit_of_lt (by norm_num)]
  have hL : AntitonicFit.levelSet 1 (AntitonicFit.fit 1 (AntitonicFit.toR x)) 0 = {0} := by
    ext i
    simp only [AntitonicFit.levelSet, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩; omega
    · rintro rfl; exact ⟨by norm_num, rfl⟩
  rw [hL]
  simp [AntitonicFit.blockF]

/-- The one big clock of the family `2^e` at shift `0`:
`yPool0 (ds (2^e)) 0 = clock e {0} 0 {0} = 2^e + e − 1` (auxiliary for (X4) of
`C37_the_mirror_that_doubles.md`). -/
lemma yPool0_top (e : ℕ) (he : 1 ≤ e) :
    FamilyGroup.yPool0 (ds (2 ^ e)) 0 = ((2 ^ e + e - 1 : ℕ) : ℤ) := by
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ e = N + 1 := ⟨2 ^ e - 1, by have := Nat.one_le_two_pow (n := e); omega⟩
  have hNe : N = 2 ^ e - 1 := by omega
  have hodd : N % 2 = 1 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ] at hN; omega
  have hl : (ds N).length = e := by rw [hNe]; exact length_ds_two_pow_sub_one e
  have hI : Windows.Ids (ds N) = ∅ := by rw [hNe]; exact Ids_ds_two_pow_sub_one e
  have hm : Dance.mCount (ds (N + 1)) = 1 := by
    rw [A2_mCount N hodd, ← Windows.card_Ids, hI, card_empty]
  rw [hN]
  unfold FamilyGroup.yPool0
  rw [hm, show 2 ^ 1 - 1 = 1 by rfl, ifit_one, A2_length N hodd, A2_Ids N hodd, hl, hI]
  have hd : TheoremF.dancer (insert 0 ∅) (0 + 1) = insert 0 ∅ := by
    have := A3_odd ∅ (by simp) 0
    rwa [TheoremF.dancer_zero] at this
  rw [hd]
  have hr : (insert 0 ∅ : Finset ℕ) ⊆ range e := by simp; omega
  have hB := B2 e (insert 0 ∅) hr (subset_refl _) 0 e
    (by rw [Rulers.oE, sum_insert (by simp), sum_empty, hN]; ring) (by simp [Rulers.oE])
  rw [hB]
  have hh : Rulers.hSum e (insert 0 ∅) (insert 0 ∅) = e := by
    rw [Rulers.hSum, sum_insert (by simp), sum_empty, add_zero,
      A5_h_zero e ∅ (by simp) (by simp), Rulers.t1, Rulers.minOr_empty]
  rw [hh, show (0 + Rulers.oE (insert 0 ∅) : ℕ) = 1 by simp [Rulers.oE]]
  have : 1 ≤ N + 1 + e := by omega
  have h2 : (2 : ℤ) ^ e = N + 1 := by exact_mod_cast hN
  push_cast [this]
  rw [h2, Rulers.s2_zero]
  ring

/-- **(X4)** of `C37_the_mirror_that_doubles.md` (the top family): for `e ≥ 1`,
`famExps (2^e) 0 = famExps (2^e − 1) 0 + famExps (2^e − 1) 0 + {2^e + e − 1}`.  The family
`2^e − 1` has `k = e`, `I = ∅`, so `bigExps (2^e − 1) 0 = 0`; the family `2^e` has its small clocks
twice (A4) and the one big clock `2^e + e − 1` at shift `0`. -/
theorem X4 (e : ℕ) (he : 1 ≤ e) :
    PodiumCor.famExps (2 ^ e) 0 =
      PodiumCor.famExps (2 ^ e - 1) 0 + PodiumCor.famExps (2 ^ e - 1) 0 + {2 ^ e + e - 1} := by
  have hv := yPool0_top e he
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ e = N + 1 := ⟨2 ^ e - 1, by have := Nat.one_le_two_pow (n := e); omega⟩
  have hNe : N = 2 ^ e - 1 := by omega
  have hodd : N % 2 = 1 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ] at hN; omega
  have hI : Windows.Ids (ds N) = ∅ := by rw [hNe]; exact Ids_ds_two_pow_sub_one e
  have hc : (Windows.Ids (ds (N + 1))).card = 1 := by
    rw [A2_card N hodd, hI, card_empty]
  rw [hN] at hv ⊢
  rw [Nat.add_sub_cancel]
  unfold PodiumCor.famExps
  rw [A4 N hodd]
  simp only [PodiumCor.bigExps, hc, hI, card_empty, pow_zero, pow_one, Nat.sub_self,
    show 2 - 1 = 1 by rfl, range_zero, range_one, Finset.empty_val, Multiset.map_zero,
    singleton_val, Multiset.map_singleton, hv, Int.toNat_natCast, add_zero]

/-! ### (X5) -/

/-- `Σ_{x ∈ l} [x = N] v = count N l • v` (auxiliary for (X5) of
`C37_the_mirror_that_doubles.md`). -/
lemma sum_map_ite_eq_count {M : Type*} [AddCommMonoid M] (l : List ℕ) (N : ℕ) (v : M) :
    (l.map fun x => if x = N then v else 0).sum = l.count N • v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : a = N
    · subst h; simp [add_smul, add_comm]
    · simp [h]

/-- **(X5)** of `C37_the_mirror_that_doubles.md` (Corollary 1.7, exponent form): for `e ≥ 1`,
`exps (2^e) = exps (2^e − 1) + exps (2^e − 1) + {2^e + e − 1}`.  By (A1) the families of `2^e`
are the `λ + 1`, `λ ∈ L (2^e − 1)`, with the same shift; the family `2^e − 1` gives (X4), and
every other family is odd and `< 2^e − 1`, so (X3) applies. -/
theorem X5 (e : ℕ) (he : 1 ≤ e) :
    PodiumCor.exps (2 ^ e) = PodiumCor.exps (2 ^ e - 1) + PodiumCor.exps (2 ^ e - 1) +
      {2 ^ e + e - 1} := by
  obtain ⟨N, hN⟩ : ∃ N, 2 ^ e = N + 1 := ⟨2 ^ e - 1, by have := Nat.one_le_two_pow (n := e); omega⟩
  have hNe : N = 2 ^ e - 1 := by omega
  have hodd : N % 2 = 1 := by
    obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
    rw [pow_succ] at hN; omega
  have hfam : ∀ lam ∈ FamDec.L N, PodiumCor.famExps (lam + 1) ((N + 1 - (lam + 1)) / 2) =
      PodiumCor.famExps lam ((N - lam) / 2) + PodiumCor.famExps lam ((N - lam) / 2) +
        (if lam = N then {2 ^ e + e - 1} else 0) := by
    intro lam hlam
    have hlo := A1_odd N hodd lam hlam
    have hle := FamDec.le_of_mem_L N lam hlam
    rcases Nat.lt_or_ge lam N with hlt | hge
    · rw [if_neg (by omega), add_zero, show (N + 1 - (lam + 1)) / 2 = (2 ^ e - 1 - lam) / 2 by
        omega, show (N - lam) / 2 = (2 ^ e - 1 - lam) / 2 by omega]
      exact X3 e he lam hlo (by omega)
    · obtain rfl : lam = N := by omega
      rw [if_pos rfl, Nat.sub_self, Nat.zero_div, show lam + 1 = 2 ^ e by omega,
        show lam = 2 ^ e - 1 by omega, Nat.sub_self, Nat.zero_div]
      exact X4 e he
  unfold PodiumCor.exps
  rw [hN, Nat.add_sub_cancel, A1_map N hodd, List.map_map]
  have hmap : List.map ((fun lam => PodiumCor.famExps lam ((N + 1 - lam) / 2)) ∘ fun x => x + 1)
      (FamDec.L N) = (FamDec.L N).map (fun lam => PodiumCor.famExps lam ((N - lam) / 2) +
        PodiumCor.famExps lam ((N - lam) / 2) + (if lam = N then {2 ^ e + e - 1} else 0)) :=
    List.map_congr_left (fun lam hlam => hfam lam hlam)
  rw [hmap]
  rw [List.sum_map_add, List.sum_map_add, sum_map_ite_eq_count]
  have h1 : (FamDec.L N).count N = 1 := FamDec.m_self N
  rw [h1, one_smul, hN]

end Mirror
