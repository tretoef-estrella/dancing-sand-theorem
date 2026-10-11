module

public import RequestProject.FormalDance.Defs

/-!
# `C40b_the_formal_dance_of_payment_systems.md`: Part C — agreement is a congruence

* (C1) `Agree.refl`, `Agree.symm`, `Agree.trans`, `MAgree.refl`, `MAgree.symm`, `MAgree.trans`,
  collected in `C1` (`Equivalence Agree ∧ Equivalence MAgree`);
* (C2) `Agree.add`, `Agree.sub`, `Agree.mul`, `Agree.smul`, `MAgree.add`, `MAgree.sub`,
  `MAgree.mul`, `MAgree.smul`, collected in `C2`;
* (C3) `Agree.tw00`, …, `Agree.vprime`, `MAgree.twP`, …, `MAgree.vsplit`, collected in `C3`;
* (C4) `C4`.
-/

@[expose] public section

noncomputable section

namespace FormalDance

open FormalOps Finset

variable {A : Type*} [CommRing A]

/-! ### (C1) -/

/-- (C1) of `C40b_the_formal_dance_of_payment_systems.md`: `Agree` is reflexive. -/
theorem Agree.refl (x : Bf A) : Agree x x := fun _ _ _ => rfl

/-- (C1) of `C40b_the_formal_dance_of_payment_systems.md`: `Agree` is symmetric. -/
theorem Agree.symm {x y : Bf A} (h : Agree x y) : Agree y x := fun m f hf => (h m f hf).symm

/-- (C1) of `C40b_the_formal_dance_of_payment_systems.md`: `Agree` is transitive. -/
theorem Agree.trans {x y z : Bf A} (h : Agree x y) (h' : Agree y z) : Agree x z :=
  fun m f hf => (h m f hf).trans (h' m f hf)

lemma Agree.of_eq {x y : Bf A} (h : x = y) : Agree x y := h ▸ Agree.refl x

section M
variable {n : Type*}

/-- (C1) of `C40b_the_formal_dance_of_payment_systems.md`: `MAgree` is reflexive. -/
theorem MAgree.refl (G : Matrix n n (Bf A)) : MAgree G G := fun _ _ => Agree.refl _

/-- (C1) of `C40b_the_formal_dance_of_payment_systems.md`: `MAgree` is symmetric. -/
theorem MAgree.symm {G H : Matrix n n (Bf A)} (h : MAgree G H) : MAgree H G :=
  fun s s' => (h s s').symm

/-- (C1) of `C40b_the_formal_dance_of_payment_systems.md`: `MAgree` is transitive. -/
theorem MAgree.trans {G H K : Matrix n n (Bf A)} (h : MAgree G H) (h' : MAgree H K) :
    MAgree G K := fun s s' => (h s s').trans (h' s s')

lemma MAgree.of_eq {G H : Matrix n n (Bf A)} (h : G = H) : MAgree G H := h ▸ MAgree.refl G

end M

/-- **(C1)** of `C40b_the_formal_dance_of_payment_systems.md`: `Agree` and `MAgree` are
equivalence relations. -/
theorem C1 (n : Type*) :
    Equivalence (Agree (A := A)) ∧ Equivalence (MAgree (A := A) (n := n)) :=
  ⟨⟨Agree.refl, Agree.symm, Agree.trans⟩, ⟨MAgree.refl, MAgree.symm, MAgree.trans⟩⟩

/-! ### (C2) -/

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `+`. -/
theorem Agree.add {x x' y y' : Bf A} (hx : Agree x x') (hy : Agree y y') :
    Agree (x + y) (x' + y') := fun m f hf => by simp [hx m f hf, hy m f hf]

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `−`. -/
theorem Agree.sub {x x' y y' : Bf A} (hx : Agree x x') (hy : Agree y y') :
    Agree (x - y) (x' - y') := fun m f hf => by simp [hx m f hf, hy m f hf]

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `*`. -/
theorem Agree.mul {x x' y y' : Bf A} (hx : Agree x x') (hy : Agree y y') :
    Agree (x * y) (x' * y') := fun m f hf => by
  simp only [Bf.coef_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  rw [hx a f (by omega), hy (m - a) (f - a) (by omega)]

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `A`-scalars. -/
theorem Agree.smul (a : A) {x x' : Bf A} (hx : Agree x x') : Agree (a • x) (a • x') :=
  fun m f hf => by simp [hx m f hf]

lemma Agree.sum {ι : Type*} (s : Finset ι) {x y : ι → Bf A} (h : ∀ i ∈ s, Agree (x i) (y i)) :
    Agree (∑ i ∈ s, x i) (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Agree.refl (0 : Bf A)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

section M
variable {n : Type*}

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the matrix sum. -/
theorem MAgree.add {G G' H H' : Matrix n n (Bf A)} (hG : MAgree G G') (hH : MAgree H H') :
    MAgree (G + H) (G' + H') := fun s s' => (hG s s').add (hH s s')

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the matrix
difference. -/
theorem MAgree.sub {G G' H H' : Matrix n n (Bf A)} (hG : MAgree G G') (hH : MAgree H H') :
    MAgree (G - H) (G' - H') := fun s s' => (hG s s').sub (hH s s')

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the matrix product. -/
theorem MAgree.mul [Fintype n] {G G' H H' : Matrix n n (Bf A)} (hG : MAgree G G')
    (hH : MAgree H H') : MAgree (G * H) (G' * H') := fun s s' => by
  simp only [Matrix.mul_apply]
  exact Agree.sum _ fun t _ => (hG s t).mul (hH t s')

/-- (C2) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `A`-scalars on
matrices. -/
theorem MAgree.smul (a : A) {G G' : Matrix n n (Bf A)} (hG : MAgree G G') :
    MAgree (a • G) (a • G') := fun s s' => (hG s s').smul a

end M

/-- **(C2)** of `C40b_the_formal_dance_of_payment_systems.md`: agreement is compatible with `+`,
`−`, `*`, `A`-scalars, for formal operators and for matrices (over `Fintype n` for the
product). -/
theorem C2 (n : Type*) [Fintype n] :
    (∀ x x' y y' : Bf A, Agree x x' → Agree y y' →
      Agree (x + y) (x' + y') ∧ Agree (x - y) (x' - y') ∧ Agree (x * y) (x' * y') ∧
      ∀ a : A, Agree (a • x) (a • x')) ∧
    (∀ G G' H H' : Matrix n n (Bf A), MAgree G G' → MAgree H H' →
      MAgree (G + H) (G' + H') ∧ MAgree (G - H) (G' - H') ∧ MAgree (G * H) (G' * H') ∧
      ∀ a : A, MAgree (a • G) (a • G')) :=
  ⟨fun _ _ _ _ hx hy => ⟨hx.add hy, hx.sub hy, hx.mul hy, fun a => hx.smul a⟩,
    fun _ _ _ _ hG hH => ⟨hG.add hH, hG.sub hH, hG.mul hH, fun a => hG.smul a⟩⟩

/-! ### (C3) -/

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `tw00`. -/
theorem Agree.tw00 {x y : Bf A} (h : Agree x y) : Agree (tw00 x) (tw00 y) := fun q f hf => by
  simp only [coef_tw00]; rw [h _ _ (by push_cast; omega)]

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `tw11`. -/
theorem Agree.tw11 {x y : Bf A} (h : Agree x y) : Agree (tw11 x) (tw11 y) := fun q f hf => by
  simp only [coef_tw11]; rw [h _ _ (by push_cast; omega)]

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `tw10`. -/
theorem Agree.tw10 {x y : Bf A} (h : Agree x y) : Agree (tw10 x) (tw10 y) := fun q f hf => by
  simp only [coef_tw10]; rw [h _ _ (by push_cast; omega)]

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `tw01`. -/
theorem Agree.tw01 {x y : Bf A} (h : Agree x y) : Agree (tw01 x) (tw01 y) := fun q f hf => by
  cases q with
  | zero => rfl
  | succ q => simp only [coef_tw01_succ]; rw [h _ _ (by push_cast at hf ⊢; omega)]

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `vplus`. -/
theorem Agree.vplus {x y : Bf A} (h : Agree x y) : Agree (vplus x) (vplus y) := fun m g hg => by
  simp only [coef_vplus]; rw [h _ _ (by omega)]

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for `vprime`. -/
theorem Agree.vprime {x y : Bf A} (h : Agree x y) : Agree (vprime x) (vprime y) :=
  fun m g hg => by simp only [coef_vprime]; rw [h _ _ (by push_cast; omega)]

section M
variable {n : Type*} {G H : Matrix n n (Bf A)}

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the pivot block. -/
theorem MAgree.twP (h : MAgree G H) : MAgree (twP G) (twP H) := fun s s' => (h s s').tw10
/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the block `C`. -/
theorem MAgree.twC (h : MAgree G H) : MAgree (twC G) (twC H) := fun s s' => (h s s').tw11
/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the block `B`. -/
theorem MAgree.twB (h : MAgree G H) : MAgree (twB G) (twB H) := fun s s' => (h s s').tw00
/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the block `Dd`. -/
theorem MAgree.twD (h : MAgree G H) : MAgree (twD G) (twD H) := fun s s' => (h s s').tw01

/-- (C3) of `C40b_the_formal_dance_of_payment_systems.md`: congruence for the V-split. -/
theorem MAgree.vsplit (h : MAgree G H) : MAgree (vsplit G) (vsplit H) := fun q q' => by
  unfold FormalDance.vsplit
  split_ifs
  · exact h _ _
  · exact (h _ _).vprime
  · exact (h _ _).vplus
  · exact Agree.refl _

end M

/-- **(C3)** of `C40b_the_formal_dance_of_payment_systems.md`: agreement is preserved by the
twist map, the V-split, and hence by the twist blocks and `vsplit` of matrices. -/
theorem C3 (n : Type*) :
    (∀ x y : Bf A, Agree x y →
      Agree (tw00 x) (tw00 y) ∧ Agree (tw11 x) (tw11 y) ∧ Agree (tw10 x) (tw10 y) ∧
      Agree (tw01 x) (tw01 y) ∧ Agree (vplus x) (vplus y) ∧ Agree (vprime x) (vprime y)) ∧
    (∀ G H : Matrix n n (Bf A), MAgree G H →
      MAgree (twP G) (twP H) ∧ MAgree (twC G) (twC H) ∧ MAgree (twB G) (twB H) ∧
      MAgree (twD G) (twD H) ∧ MAgree (vsplit G) (vsplit H)) :=
  ⟨fun _ _ h => ⟨h.tw00, h.tw11, h.tw10, h.tw01, h.vplus, h.vprime⟩,
    fun _ _ h => ⟨h.twP, h.twC, h.twB, h.twD, h.vsplit⟩⟩

/-! ### (C4) -/

/-- Under (top W), the coordinate `i` of `N.Fd m v` vanishes unless the floor
`(W − wt i) / 2` is at least `m` (from C18 (W)). -/
lemma Fd_apply_eq_zero_of_floor_lt {N : DPLattice A} {W : ℤ}
    (htop : ∀ i, N.wt i ≤ W) (m : ℕ) (v : N.ι → A) (i : N.ι)
    (hi : (W - N.wt i) / 2 < m) : N.Fd m v i = 0 := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : A) : N.ι → A) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, Pi.smul_apply, N.isDP.W_F j m i ?_, smul_zero]
  have := htop j
  omega

/-- **(C4)** of `C40b_the_formal_dance_of_payment_systems.md`: agreement does not change the
action. More general than stated: only the first half `N.wt i ≤ W` of (top W) is used (the
parity condition `Even (W − N.wt i)` is not needed). -/
theorem C4 {N : DPLattice A} {W : ℤ} (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i))
    {x y : Bf A} (h : Agree x y) (B : ℕ) : act N W B x = act N W B y := by
  unfold act
  refine Finset.sum_congr rfl fun m _ => ?_
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [Module.End.mul_apply, flD_apply]
  by_cases hi : (W - N.wt i) / 2 < m
  · rw [Fd_apply_eq_zero_of_floor_lt (fun i => (htop i).1) m v i hi, mul_zero, mul_zero]
  · rw [h m _ (by omega)]

end FormalDance
