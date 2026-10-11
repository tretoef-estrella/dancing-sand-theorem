module

public import RequestProject.Windows.Basic
public import RequestProject.Families.Digits

/-!
# `C42_floors_and_corollary_10_9.md`: the bit bookkeeping of the dancers (auxiliary)

Auxiliary lemmas for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the floor
`Rulers.oE (Windows.Dset ds s)` of a final slot `s` for a digit list `d :: ds`, in terms of the
one of `ds` (C14 `Windows.Ids`, `Windows.rank`, `Windows.Dset`, C3 `Rulers.oE`).
-/

@[expose] public section

namespace InvFloors

open Finset Windows

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: `o(E + 1) = 2 · o(E)`. -/
lemma oE_image_succ (E : Finset ℕ) : Rulers.oE (E.image (· + 1)) = 2 * Rulers.oE E := by
  unfold Rulers.oE
  rw [sum_image (fun a _ b _ h => by omega), mul_sum]
  exact sum_congr rfl fun t _ => by ring

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the rank of `t + 1` in
`I(d :: ds)`. -/
lemma rank_Ids_cons_succ (d : Bool) (ds : List Bool) (t : ℕ) :
    rank (Ids (d :: ds)) (t + 1) = (if d = true then 1 else 0) + rank (Ids ds) t := by
  unfold rank
  rw [Ids_cons, filter_union]
  have hdisj : Disjoint ((if d = true then ({0} : Finset ℕ) else ∅).filter (· < t + 1))
      (((Ids ds).image (· + 1)).filter (· < t + 1)) := by
    rw [disjoint_left]
    intro a ha hb
    simp only [mem_filter, mem_image] at ha hb
    obtain ⟨⟨u, -, rfl⟩, -⟩ := hb
    split_ifs at ha <;> simp at ha
  rw [card_union_of_disjoint hdisj]
  congr 1
  · split_ifs <;> simp [filter_singleton]
  · rw [filter_image, card_image_of_injective _ (add_left_injective 1)]
    congr 1
    ext u; simp

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the rank of `0` is `0`. -/
lemma rank_zero (I : Finset ℕ) : rank I 0 = 0 := by
  simp [rank]

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the dancers of a slot after a
twist digit, `D(false :: ds, s) = D(ds, s) + 1`. -/
lemma Dset_cons_false (ds : List Bool) (s : ℕ) :
    Dset (false :: ds) s = (Dset ds s).image (· + 1) := by
  ext t
  rcases t with _ | t
  · simp [Dset, mem_Ids]
  · rw [mem_image]
    unfold Dset
    rw [mem_filter, rank_Ids_cons_succ, mem_Ids, List.getElem?_cons_succ, ← mem_Ids]
    simp only [Dance.mCount, Bool.false_eq_true, if_false, zero_add, mem_filter]
    constructor
    · intro h; exact ⟨t, h, rfl⟩
    · rintro ⟨u, hu, hut⟩
      obtain rfl : u = t := by omega
      exact hu

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the dancers of a slot after a
split digit, `D(true :: ds, s) = (bit m(ds) of s ? {0} : ∅) ∪ (D(ds, s) + 1)`. -/
lemma Dset_cons_true (ds : List Bool) (s : ℕ) :
    Dset (true :: ds) s = (if Nat.testBit s (Dance.mCount ds) = true then {0} else ∅) ∪
      (Dset ds s).image (· + 1) := by
  ext t
  rcases t with _ | t
  · unfold Dset
    rw [mem_filter, rank_zero, mem_union, mem_image]
    have h0 : (0 : ℕ) ∈ Ids (true :: ds) := by rw [mem_Ids]; rfl
    simp only [h0, true_and, Dance.mCount, Nat.add_sub_cancel, Nat.sub_zero]
    split_ifs with h <;> simp [h]
  · rw [mem_union, mem_image]
    unfold Dset
    rw [mem_filter, rank_Ids_cons_succ, mem_Ids, List.getElem?_cons_succ, ← mem_Ids]
    simp only [if_true, Dance.mCount, mem_filter]
    have e : Dance.mCount ds + 1 - 1 - (1 + rank (Ids ds) t) =
        Dance.mCount ds - 1 - rank (Ids ds) t := by omega
    rw [e]
    constructor
    · intro h; right; exact ⟨t, h, rfl⟩
    · rintro (h | ⟨u, hu, hut⟩)
      · split_ifs at h <;> simp at h
      · obtain rfl : u = t := by omega
        exact hu

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the floor after a twist digit,
`o(D(false :: ds, s)) = 2 · o(D(ds, s))`. -/
lemma oE_Dset_cons_false (ds : List Bool) (s : ℕ) :
    Rulers.oE (Dset (false :: ds) s) = 2 * Rulers.oE (Dset ds s) := by
  rw [Dset_cons_false, oE_image_succ]

/-- Auxiliary for (F4)–(F6) of `C42_floors_and_corollary_10_9.md`: the floor after a split digit,
`o(D(true :: ds, s)) = (s / 2^{m(ds)}) % 2 + 2 · o(D(ds, s))`. -/
lemma oE_Dset_cons_true (ds : List Bool) (s : ℕ) :
    Rulers.oE (Dset (true :: ds) s) = s / 2 ^ Dance.mCount ds % 2 + 2 * Rulers.oE (Dset ds s) := by
  rw [Dset_cons_true]
  have hdisj : Disjoint (if Nat.testBit s (Dance.mCount ds) = true then ({0} : Finset ℕ) else ∅)
      ((Dset ds s).image (· + 1)) := by
    rw [disjoint_left]
    intro a ha hb
    simp only [mem_image] at hb
    obtain ⟨u, -, rfl⟩ := hb
    split_ifs at ha <;> simp at ha
  rw [Rulers.oE_union hdisj, oE_image_succ]
  congr 1
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ Dance.mCount ds) with h | h <;>
    simp [h, Rulers.oE]

/-- Auxiliary for (F6) of `C42_floors_and_corollary_10_9.md`: the dancers lie in `I(ds)`. -/
lemma Dset_subset_Ids (ds : List Bool) (s : ℕ) : Dset ds s ⊆ Ids ds := filter_subset _ _

end InvFloors
