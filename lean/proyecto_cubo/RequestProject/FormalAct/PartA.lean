module

public import RequestProject.FormalAct.Defs
public import RequestProject.FormalOps.All

/-!
# `C40c_the_action_of_a_system_and_one_move.md`: Part A — the action of a system

`A` is any commutative ring, `n` a `Fintype` with `DecidableEq`.

* (A1) `A1` (from C40b's `C4` entrywise);
* (A2) `sysAct_one`, `sysAct_mul`, `sysAct_add`, `sysAct_sub`, `sysAct_smul`, collected in `A2`
  (from C40's `B4` entrywise);
* (A3) `A3_conj` (the conjugation by `LinearEquiv.funCongrLeft`) and `A3` (the cokernels), via the
  explicit `A3equiv`;
* (A4) `A4_apply` and `A4` (the cokernels), via the explicit `A4equiv`.

Hypotheses: in (A2) the hypothesis `1 ≤ B` is only needed for the unit, and (nil BN), `BN ≤ B`
only for the product; the sum, difference and scalar statements hold for every `B` without
(nil BN) (`sysAct_add`, `sysAct_sub`, `sysAct_smul`: more general). The combined statement `A2`
carries all hypotheses, as in the file.
-/

@[expose] public section

noncomputable section

namespace FormalAct

open DPLattice FormalOps FormalDance Finset

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n]
  {N : DPLattice A} {W : ℤ}

/-! ### Auxiliary: `act` is additive -/

variable (N W) in
/-- Auxiliary: `act N W B` as an additive map (C40's `act_add`). -/
def actHom (B : ℕ) : Bf A →+ Module.End A (N.ι → A) :=
  AddMonoidHom.mk' (act N W B) (act_add B)

lemma act_zero' (B : ℕ) : act N W B (0 : Bf A) = 0 := (actHom N W B).map_zero

lemma act_sub' (B : ℕ) (x y : Bf A) : act N W B (x - y) = act N W B x - act N W B y :=
  (actHom N W B).map_sub x y

lemma act_sum' {ι : Type*} (B : ℕ) (s : Finset ι) (f : ι → Bf A) :
    act N W B (∑ i ∈ s, f i) = ∑ i ∈ s, act N W B (f i) :=
  map_sum (actHom N W B) f s

/-! ### (A1) -/

/-- **(A1)** of `C40c_the_action_of_a_system_and_one_move.md` (agreement): if `N` satisfies
(top W) and `MAgree G H`, then `sysAct N W B G = sysAct N W B H` for every `B`. -/
theorem A1 (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) {G H : Matrix n n (Bf A)}
    (h : MAgree G H) (B : ℕ) : sysAct N W B G = sysAct N W B H :=
  LinearMap.ext fun v => funext fun s => by
    simp only [sysAct_apply]
    exact Finset.sum_congr rfl fun s' _ => by rw [C4 htop (h s s') B]

/-! ### (A2) -/

/-- **(A2)** of `C40c_the_action_of_a_system_and_one_move.md`, the unit:
`sysAct N W B 1 = LinearMap.id` if `1 ≤ B` (without (nil BN): more general). -/
theorem sysAct_one [DecidableEq n] {B : ℕ} (hB1 : 1 ≤ B) :
    sysAct N W B (1 : Matrix n n (Bf A)) = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun s => ?_
  simp only [sysAct_apply, LinearMap.id_apply]
  rw [Finset.sum_eq_single s]
  · rw [Matrix.one_apply_eq, act_one hB1]; rfl
  · intro b _ hb; rw [Matrix.one_apply_ne (Ne.symm hb), act_zero']; rfl
  · simp

/-- **(A2)** of `C40c_the_action_of_a_system_and_one_move.md`, the product: under (nil BN) and
`BN ≤ B`, `sysAct N W B (G * H) = sysAct N W B G ∘ₗ sysAct N W B H`. -/
theorem sysAct_mul {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) {B : ℕ} (hB : BN ≤ B)
    (G H : Matrix n n (Bf A)) :
    sysAct N W B (G * H) = sysAct N W B G ∘ₗ sysAct N W B H := by
  refine LinearMap.ext fun v => funext fun s => ?_
  simp only [sysAct_apply, LinearMap.comp_apply, Matrix.mul_apply, act_sum', act_mul hnil hB,
    LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

/-- **(A2)** of `C40c_the_action_of_a_system_and_one_move.md`, the sum (for every `B`, without
(nil BN): more general). -/
theorem sysAct_add (B : ℕ) (G H : Matrix n n (Bf A)) :
    sysAct N W B (G + H) = sysAct N W B G + sysAct N W B H := by
  refine LinearMap.ext fun v => funext fun s => ?_
  simp [Matrix.add_apply, act_add, Finset.sum_add_distrib]

/-- **(A2)** of `C40c_the_action_of_a_system_and_one_move.md`, the difference (for every `B`,
without (nil BN): more general). -/
theorem sysAct_sub (B : ℕ) (G H : Matrix n n (Bf A)) :
    sysAct N W B (G - H) = sysAct N W B G - sysAct N W B H := by
  refine LinearMap.ext fun v => funext fun s => ?_
  simp [Matrix.sub_apply, act_sub', Finset.sum_sub_distrib]

/-- **(A2)** of `C40c_the_action_of_a_system_and_one_move.md`, scalars: for `a : A`,
`sysAct N W B (a • G) = a • sysAct N W B G` (for every `B`, without (nil BN): more general). -/
theorem sysAct_smul (B : ℕ) (a : A) (G : Matrix n n (Bf A)) :
    sysAct N W B (a • G) = a • sysAct N W B G := by
  refine LinearMap.ext fun v => funext fun s => ?_
  simp [Matrix.smul_apply, act_smul, Finset.smul_sum]

/-- **(A2)** of `C40c_the_action_of_a_system_and_one_move.md` (a ring map): if `N` satisfies
(nil BN), `BN ≤ B` and `1 ≤ B`, then `sysAct N W B 1 = LinearMap.id`,
`sysAct N W B (G * H) = sysAct N W B G ∘ₗ sysAct N W B H`, and `sysAct N W B` is compatible with
`+`, `−` and scalars `a : A`. -/
theorem A2 [DecidableEq n] {BN : ℕ} (hnil : ∀ s ≥ BN, N.Fd s = 0) {B : ℕ} (hB : BN ≤ B) (hB1 : 1 ≤ B) :
    sysAct N W B (1 : Matrix n n (Bf A)) = LinearMap.id ∧
    (∀ G H : Matrix n n (Bf A), sysAct N W B (G * H) = sysAct N W B G ∘ₗ sysAct N W B H) ∧
    (∀ G H : Matrix n n (Bf A), sysAct N W B (G + H) = sysAct N W B G + sysAct N W B H) ∧
    (∀ G H : Matrix n n (Bf A), sysAct N W B (G - H) = sysAct N W B G - sysAct N W B H) ∧
    (∀ (a : A) (G : Matrix n n (Bf A)), sysAct N W B (a • G) = a • sysAct N W B G) :=
  ⟨sysAct_one hB1, sysAct_mul hnil hB, sysAct_add B, sysAct_sub B, sysAct_smul B⟩

/-! ### (A3) -/

section A3

variable {n' : Type*} [Fintype n']

/-- **(A3)** of `C40c_the_action_of_a_system_and_one_move.md` (relabelling), first half: for
`e : n ≃ n'`, `G : Matrix n' n' (Bf A)` and `G_e := fun j j' => G (e j) (e j')`, `sysAct N W B G_e`
and `sysAct N W B G` are conjugate by the reindexing `LinearEquiv.funCongrLeft` along `e`
(`v ↦ v ∘ e`). (No hypothesis on `N` or `B` is needed.) -/
theorem A3_conj (B : ℕ) (e : n ≃ n') (G : Matrix n' n' (Bf A)) :
    sysAct N W B (fun j j' => G (e j) (e j')) =
      (LinearEquiv.funCongrLeft A (N.ι → A) e : (n' → N.ι → A) →ₗ[A] (n → N.ι → A)) ∘ₗ
        sysAct N W B G ∘ₗ
        ((LinearEquiv.funCongrLeft A (N.ι → A) e).symm : (n → N.ι → A) →ₗ[A] (n' → N.ι → A)) := by
  refine LinearMap.ext fun v => funext fun j => ?_
  simp only [sysAct_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  refine Fintype.sum_equiv e _ _ fun j' => ?_
  simp

/-- (A3), the cokernel isomorphism as an explicit linear equivalence (induced by
`(LinearEquiv.funCongrLeft A (N.ι → A) e).symm`, i.e. `w ↦ w ∘ e.symm`). -/
def A3equiv (B : ℕ) (e : n ≃ n') (G : Matrix n' n' (Bf A)) (c : A) :
    ((n → N.ι → A) ⧸ LinearMap.range (c • sysAct N W B (fun j j' => G (e j) (e j')))) ≃ₗ[A]
      ((n' → N.ι → A) ⧸ LinearMap.range (c • sysAct N W B G)) :=
  quotEquivConj (LinearEquiv.funCongrLeft A (N.ι → A) e).symm
    (LinearEquiv.funCongrLeft A (N.ι → A) e).symm _ _ (by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, A3_conj B e G, LinearEquiv.coe_coe,
        map_smul, LinearEquiv.symm_apply_apply])

/-- **(A3)** of `C40c_the_action_of_a_system_and_one_move.md` (relabelling), second half: for
every `c : A`, the cokernels of `c • sysAct N W B G_e` and of `c • sysAct N W B G` are isomorphic.
(No hypothesis on `N` or `B` is needed.) -/
theorem A3 (B : ℕ) (e : n ≃ n') (G : Matrix n' n' (Bf A)) (c : A) :
    Nonempty (((n → N.ι → A) ⧸ LinearMap.range (c • sysAct N W B (fun j j' => G (e j) (e j')))) ≃ₗ[A]
      ((n' → N.ι → A) ⧸ LinearMap.range (c • sysAct N W B G))) :=
  ⟨A3equiv B e G c⟩

end A3

/-! ### (A4) -/

/-- Auxiliary for (A4): on `one A` with `W = 0` and `1 ≤ B`, `act (one A) 0 B x` is the diagonal
operator of the coefficient `x.coef 0`. -/
lemma act_one_lattice {B : ℕ} (hB : 1 ≤ B) (x : Bf A) :
    act (one A) 0 B x = flD (one A) 0 (x.coef 0) := by
  rw [act, Finset.sum_eq_single 0]
  · rw [show (one A).Fd 0 = 1 from (one A).isDP.P0_F, mul_one]
  · intro m _ hm
    rw [show (one A).Fd m = 0 from if_neg hm, mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-- **(A4)** of `C40c_the_action_of_a_system_and_one_move.md` (the last level), first half: on
`one A` with `W = 0` and `1 ≤ B`, `sysAct (one A) 0 B G v s () = Σ_{s'} finalM G s s' * v s' ()`. -/
theorem A4_apply {B : ℕ} (hB : 1 ≤ B) (G : Matrix n n (Bf A)) (v : n → Unit → A) (s : n) :
    sysAct (one A) 0 B G v s () = ∑ s', finalM G s s' * v s' () := by
  simp only [sysAct_apply, Finset.sum_apply, act_one_lattice hB, flD_apply]
  rfl

/-- Auxiliary for (A4): `n → Unit → A ≃ₗ[A] n → A`, evaluation at `()`. -/
def unitEquiv : (n → Unit → A) ≃ₗ[A] (n → A) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.funUnique Unit A A

/-- (A4), the cokernel isomorphism as an explicit linear equivalence (induced by the evaluation
at `()`). -/
def A4equiv {B : ℕ} (hB : 1 ≤ B) (G : Matrix n n (Bf A)) (c : A) :
    ((n → Unit → A) ⧸ LinearMap.range (c • sysAct (one A) 0 B G)) ≃ₗ[A]
      ((n → A) ⧸ LinearMap.range (c • Matrix.mulVecLin (finalM G))) :=
  quotEquivConj unitEquiv unitEquiv _ _ (by
    refine LinearMap.ext fun v => funext fun s => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
      Pi.smul_apply, Matrix.mulVecLin_apply]
    show c • (∑ s', finalM G s s' * v s' ()) = c • sysAct (one A) 0 B G v s ()
    rw [A4_apply hB])

/-- **(A4)** of `C40c_the_action_of_a_system_and_one_move.md` (the last level), second half: on
`one A` with `W = 0` and `1 ≤ B`, for every `c : A`, the cokernel of `c • sysAct (one A) 0 B G` is
isomorphic to the cokernel of `c • Matrix.mulVecLin (finalM G)`. -/
theorem A4 {B : ℕ} (hB : 1 ≤ B) (G : Matrix n n (Bf A)) (c : A) :
    Nonempty (((n → Unit → A) ⧸ LinearMap.range (c • sysAct (one A) 0 B G)) ≃ₗ[A]
      ((n → A) ⧸ LinearMap.range (c • Matrix.mulVecLin (finalM G)))) :=
  ⟨A4equiv hB G c⟩

end FormalAct
