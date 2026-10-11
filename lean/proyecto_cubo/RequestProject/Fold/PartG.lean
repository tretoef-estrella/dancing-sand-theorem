module

public import RequestProject.Fold.Defs

/-!
# `C38_the_fold_in_the_group_ring.md`: Part G — the fold in the group ring

For every commutative ring `A` and every `n`:
* (G1) `transl A n` is an involution commuting with `lap A n` (`G1`);
* (G2) `push A n` is surjective, its kernel is `range (transl A n − 1)`, and
  `push ∘ lap = lapBar ∘ push` (`G2`, with the parts `push_surjective`, `ker_push`, `push_lap`);
* (G3) the isomorphism `(Gbar n → A) ⧸ range (lapBar A n) ≃ₗ[A] (G n → A) ⧸ foldSub A n` induced
  by `push` (`G3equiv`, `G3`, `G3equiv_symm_mk`), and its case `A = ℤ` for `cokerBar n`
  (`G3Z`).
-/

@[expose] public section

noncomputable section

namespace Fold

open CubeLaplacian Finset

variable (A : Type*) [CommRing A] (n : ℕ)

/-! ### Basic facts on the antipode and the fold -/

lemma aElt_add_self : aElt n + aElt n = 0 := by
  funext i; simp only [aElt, Pi.add_apply, Pi.zero_apply]; decide

lemma mk_aElt : mk n (aElt n) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)

lemma mk_add_aElt (g : G n) : mk n (g + aElt n) = mk n g := by
  rw [map_add, mk_aElt, add_zero]

lemma mem_zmultiples_aElt {h : G n} :
    h ∈ AddSubgroup.zmultiples (aElt n) ↔ h = 0 ∨ h = aElt n := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (k : ZMod 2) with h | h
    · left; funext i; simp [aElt, h]
    · right; funext i; simp [aElt, h]
  · rintro (rfl | rfl)
    · exact zero_mem _
    · exact AddSubgroup.mem_zmultiples _

/-- (G2, sketch) the coset of `g` is `{g, g + aElt n}`. -/
lemma mk_eq_iff {g g' : G n} : mk n g' = mk n g ↔ g' = g ∨ g' = g + aElt n := by
  rw [mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem,
    mem_zmultiples_aElt, sub_eq_zero, sub_eq_iff_eq_add, add_comm (aElt n)]

lemma mk_surjective : Function.Surjective (mk n) := QuotientAddGroup.mk'_surjective _

open Classical in
lemma push_apply' (f : G n → A) (x : Gbar n) :
    push A n f x = ∑ g, if mk n g = x then f g else 0 := by
  rw [← Finset.sum_filter]; rfl

/-- (G2, auxiliary) shifting the summation variable. -/
lemma sum_shift (f : G n → A) (x : Gbar n) (c : G n) :
    (∑ g, if mk n g = x then f (g + c) else 0) = push A n f (x + mk n c) := by
  classical
  rw [push_apply']
  refine Fintype.sum_equiv (Equiv.addRight c) _ _ fun g => ?_
  simp only [Equiv.coe_addRight, map_add, add_left_inj]

/-- (G2, sketch) `push f (mk g)` is `f g + f (g + a)` (or `f g` when `a = 0`, i.e. `n = 0`). -/
lemma push_mk (f : G n → A) (g : G n) :
    push A n f (mk n g) = if aElt n = 0 then f g else f g + f (g + aElt n) := by
  classical
  have hfib : (univ.filter fun g' => mk n g' = mk n g) = {g, g + aElt n} := by
    ext g'; simp [mk_eq_iff]
  show ∑ g' ∈ univ.filter (fun g' => mk n g' = mk n g), f g' = _
  rw [hfib]
  split_ifs with ha
  · simp [ha]
  · rw [Finset.sum_pair]
    intro h
    exact ha (Eq.symm (by simpa using congrArg (fun z => -g + z) h))

/-! ### (G1) -/

/-- **(G1)** of `C38_the_fold_in_the_group_ring.md`: `transl A n ∘ₗ transl A n = 1` and
`transl A n ∘ₗ lap A n = lap A n ∘ₗ transl A n`. -/
theorem G1 : transl A n ∘ₗ transl A n = 1 ∧ transl A n ∘ₗ lap A n = lap A n ∘ₗ transl A n := by
  refine ⟨LinearMap.ext fun f => funext fun g => ?_, LinearMap.ext fun f => funext fun g => ?_⟩
  · simp [transl_apply, add_assoc, aElt_add_self]
  · simp only [LinearMap.comp_apply, transl_apply, lap_apply]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 1
    abel

/-! ### (G2) -/

/-- **(G2)** of `C38_the_fold_in_the_group_ring.md`, first part: `push A n` is surjective. -/
theorem push_surjective : Function.Surjective (push A n) := by
  classical
  intro u
  let s := Function.surjInv (mk_surjective n)
  have hs : ∀ x, mk n (s x) = x := Function.surjInv_eq (mk_surjective n)
  refine ⟨fun g => if g = s (mk n g) then u (mk n g) else 0, funext fun x => ?_⟩
  show ∑ g ∈ univ.filter (fun g => mk n g = x), _ = _
  rw [Finset.sum_congr rfl (g := fun g => if g = s x then u x else 0)]
  · rw [Finset.sum_ite_eq']
    simp [hs]
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    subst hg; rfl

/-- **(G2)** of `C38_the_fold_in_the_group_ring.md`, second part:
`ker (push A n) = range (transl A n − 1)`. -/
theorem ker_push : LinearMap.ker (push A n) = LinearMap.range (transl A n - 1) := by
  classical
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    have hfib : ∀ g, (if aElt n = 0 then f g else f g + f (g + aElt n)) = 0 := fun g => by
      rw [← push_mk, hf]; rfl
    let s := Function.surjInv (mk_surjective n)
    have hs : ∀ x, mk n (s x) = x := Function.surjInv_eq (mk_surjective n)
    refine ⟨fun g => if g = s (mk n g) then 0 else f (g + aElt n), funext fun g => ?_⟩
    simp only [LinearMap.sub_apply, transl_apply, Module.End.one_apply, Pi.sub_apply,
      mk_add_aElt]
    have hr : s (mk n g) = g ∨ s (mk n g) = g + aElt n := (mk_eq_iff n).1 (hs _)
    by_cases ha : aElt n = 0
    · have h1 := hfib g
      simp only [ha, if_true] at h1
      simp [ha, h1]
    · have h1 := hfib g
      simp only [ha, if_false] at h1
      have hne : g + aElt n ≠ g := fun h => ha (by simpa using congrArg (fun z => -g + z) h)
      rcases hr with hr | hr
      · rw [hr, if_neg hne, if_pos rfl, add_assoc, aElt_add_self, add_zero, sub_zero]
      · rw [hr, if_pos rfl, if_neg (Ne.symm hne), zero_sub]
        linear_combination -h1
  · rintro ⟨h, rfl⟩
    funext x
    rw [LinearMap.sub_apply, map_sub, Pi.sub_apply, Module.End.one_apply, Pi.zero_apply,
      sub_eq_zero]
    show push A n (fun g => h (g + aElt n)) x = _
    rw [push_apply', sum_shift, mk_aElt, add_zero]

/-- **(G2)** of `C38_the_fold_in_the_group_ring.md`, third part:
`push A n ∘ₗ lap A n = lapBar A n ∘ₗ push A n`. -/
theorem push_lap : push A n ∘ₗ lap A n = lapBar A n ∘ₗ push A n := by
  classical
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.comp_apply]
  rw [push_apply', lapBar_apply, push_apply']
  simp only [← sum_shift, lap_apply]
  rw [Finset.mul_sum, Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine sum_congr rfl fun g _ => ?_
  split_ifs <;> simp

/-- **(G2)** of `C38_the_fold_in_the_group_ring.md`: `push A n` is surjective,
`ker (push A n) = range (transl A n − 1)` and `push A n ∘ₗ lap A n = lapBar A n ∘ₗ push A n`. -/
theorem G2 : Function.Surjective (push A n) ∧
    LinearMap.ker (push A n) = LinearMap.range (transl A n - 1) ∧
    push A n ∘ₗ lap A n = lapBar A n ∘ₗ push A n :=
  ⟨push_surjective A n, ker_push A n, push_lap A n⟩

/-! ### (G3) -/

/-- (G3, auxiliary) the preimage of `range (lapBar A n)` under `push` is `foldSub A n`. -/
lemma comap_push_range_lapBar :
    Submodule.comap (push A n) (LinearMap.range (lapBar A n)) = foldSub A n := by
  have : LinearMap.range (lapBar A n) = Submodule.map (push A n) (LinearMap.range (lap A n)) := by
    rw [← LinearMap.range_comp, push_lap, LinearMap.range_comp,
      LinearMap.range_eq_top.2 (push_surjective A n), Submodule.map_top]
  rw [this, Submodule.comap_map_eq, ker_push]; rfl

lemma ker_mkQ_push :
    LinearMap.ker ((LinearMap.range (lapBar A n)).mkQ ∘ₗ push A n) = foldSub A n := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ, comap_push_range_lapBar]

lemma mkQ_push_surjective :
    Function.Surjective ((LinearMap.range (lapBar A n)).mkQ ∘ₗ push A n) :=
  (Submodule.mkQ_surjective _).comp (push_surjective A n)

/-- **(G3)** of `C38_the_fold_in_the_group_ring.md` (explicit equivalence):
`(Gbar n → A) ⧸ range (lapBar A n) ≃ₗ[A] (G n → A) ⧸ foldSub A n`, induced by `push`
(see `G3equiv_symm_mk`). -/
def G3equiv : ((Gbar n → A) ⧸ LinearMap.range (lapBar A n)) ≃ₗ[A] ((G n → A) ⧸ foldSub A n) :=
  ((Submodule.quotEquivOfEq _ _ (ker_mkQ_push A n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (mkQ_push_surjective A n))).symm

/-- **(G3)** of `C38_the_fold_in_the_group_ring.md`: the equivalence `G3equiv` is induced by
`push`: its inverse sends the class of `f` to the class of `push A n f`. -/
theorem G3equiv_symm_mk (f : G n → A) :
    (G3equiv A n).symm (Submodule.Quotient.mk f) = Submodule.Quotient.mk (push A n f) := rfl

/-- **(G3)** of `C38_the_fold_in_the_group_ring.md`: for every commutative ring `A` and every
`n`, `(Gbar n → A) ⧸ range (lapBar A n) ≃ₗ[A] (G n → A) ⧸ foldSub A n`. -/
theorem G3 : Nonempty (((Gbar n → A) ⧸ LinearMap.range (lapBar A n)) ≃ₗ[A]
    ((G n → A) ⧸ foldSub A n)) :=
  ⟨G3equiv A n⟩

/-- **(G3)** of `C38_the_fold_in_the_group_ring.md`, the case `A = ℤ` (explicit equivalence):
`cokerBar n ≃ₗ[ℤ] (G n → ℤ) ⧸ foldSub ℤ n`. -/
def G3Zequiv : cokerBar n ≃ₗ[ℤ] ((G n → ℤ) ⧸ foldSub ℤ n) := G3equiv ℤ n

/-- **(G3)** of `C38_the_fold_in_the_group_ring.md`, the case `A = ℤ`:
`cokerBar n ≃ₗ[ℤ] (G n → ℤ) ⧸ foldSub ℤ n`. -/
theorem G3Z : Nonempty (cokerBar n ≃ₗ[ℤ] ((G n → ℤ) ⧸ foldSub ℤ n)) := ⟨G3Zequiv n⟩

end Fold
