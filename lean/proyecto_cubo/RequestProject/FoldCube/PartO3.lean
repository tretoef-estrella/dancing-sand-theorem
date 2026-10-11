module

public import RequestProject.FoldCube.PartO1

/-!
# `C39b_the_cube_side_on_the_half_lattice.md`: Part O — (O3), (O4), (O5)

* (O3) `O3equiv`, `O3`: under (top) `∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)`,
  `(N.ι → A) ⧸ range (Gp N d) ≃ₗ[A] (N.ι → A) ⧸ range (SigmaOp N e)` with
  `e = if Even (d − W) then d else d + 1`. Following the sketch: with `u i = 2d + 1 − e − wt i`
  (the odd one of `d − wt i`, `d − wt i + 1`, a unit) and `σ i = Π_{g < (W − wt i)/2} (−u)` at
  weight `W − 2g`, one has `σ · Gp N d · (−u⁻¹) = SigmaOp N e · σ` (`Gp_conj`), and the diagonal
  operator `σ` induces the isomorphism.
* (O4) `O4`: the weights of `Filt.T A l` are `≤ l` and `≡ l mod 2`.
* (O5) `O5`, `O5_X`: Lemma 10.4(b) over `ℤ_[2]`.
-/

@[expose] public section

noncomputable section

namespace FoldCube

open DPLattice Doubling Fold FoldHalf

variable {A : Type*} [CommRing A]

/-! ### (O3) -/

section O3

lemma isUnit_odd_int [OddUnits A] {z : ℤ} (hz : Odd z) : IsUnit ((z : ℤ) : A) := by
  obtain ⟨k, rfl⟩ := hz
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    have := OddUnits.hodd (A := A) k
    push_cast at this ⊢
    exact this
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) - 1 := ⟨(-k - 1).toNat, by omega⟩
    have := (OddUnits.hodd (A := A) m).neg
    convert this using 1
    push_cast; ring

lemma dg_surjective {ι : Type*} {a : ι → A} (ha : ∀ k, IsUnit (a k)) :
    Function.Surjective (dg a) := fun f =>
  ⟨fun k => Ring.inverse (a k) * f k, by
    funext k; simp [← mul_assoc, Ring.mul_inverse_cancel _ (ha k)]⟩

lemma dg_injective {ι : Type*} {a : ι → A} (ha : ∀ k, IsUnit (a k)) :
    Function.Injective (dg a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  funext k
  have := congrFun hf k
  simp only [dg_apply, Pi.zero_apply] at this
  exact (ha k).mul_right_eq_zero.1 this

/-- `dg a * F * dg b = F * dg c` when `a k * b i = c i` whenever `wt k = wt i − 2` (Part O3). -/
lemma Fd_sandwich (M : DPLattice A) (a b c : M.ι → A)
    (h : ∀ i k, M.wt k = M.wt i - 2 → a k * b i = c i) :
    dg a * M.Fd 1 * dg b = M.Fd 1 * dg c := by
  refine ext_single fun i => ?_
  funext k
  simp only [Module.End.mul_apply, dg_single, map_smul, dg_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : M.wt k = M.wt i - 2
  · rw [← h i k hk]; ring
  · rw [M.isDP.W_F i 1 k (by simpa using hk)]; ring

lemma Gp_eq (N : DPLattice A) (d : ℤ) :
    Gp N d = N.Fd 1 - dg (fun k => ((2 * ((d - N.wt k) * (d - N.wt k + 1)) : ℤ) : A)) := by
  apply LinearMap.ext; intro f; funext k
  simp only [Gp, Jop, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.add_apply, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    Hop_apply, dg_apply, smul_eq_mul, map_sub, map_smul, map_add]
  push_cast; ring

lemma SigmaOp_eq (N : DPLattice A) (e : ℤ) :
    SigmaOp N e = N.Fd 1 + dg (fun k => (((2 * (e - N.wt k) : ℤ)) : A)) := by
  apply LinearMap.ext; intro f; funext k
  simp only [SigmaOp, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Hop_apply, dg_apply,
    smul_eq_mul]
  push_cast; ring

variable [OddUnits A] (N : DPLattice A) (W d e : ℤ)
  (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (he : e = if Even (d - W) then d else d + 1)

/-- `u` at weight `w`: `2d + 1 − e − w` (Part O3). -/
def uW (d e w : ℤ) : A := ((2 * d + 1 - e - w : ℤ) : A)

include he in
lemma odd_u (w : ℤ) (hw : Even (W - w)) : Odd (2 * d + 1 - e - w) := by
  split_ifs at he with h
  · rw [he]
    rw [show 2 * d + 1 - d - w = (d - W) + (W - w) + 1 by ring]
    exact (h.add hw).add_one
  · rw [he]
    rw [show 2 * d + 1 - (d + 1) - w = (d - W) + (W - w) by ring]
    exact (Int.not_even_iff_odd.1 h).add_even hw

include he in
lemma jj_eq (w : ℤ) : (d - w) * (d - w + 1) = (e - w) * (2 * d + 1 - e - w) := by
  split_ifs at he <;> subst he <;> ring

/-- the floor `f i = (W − wt i)/2` (Part O3). -/
def fN (N : DPLattice A) (W : ℤ) (i : N.ι) : ℕ := ((W - N.wt i) / 2).toNat

/-- `σ i = Π_{g < f i} (−u at weight W − 2g)` (Part O3). -/
def sig (N : DPLattice A) (W d e : ℤ) (i : N.ι) : A := ∏ g ∈ Finset.range (fN N W i), -(uW d e (W - 2 * g) : A)

include he in
lemma isUnit_uW (w : ℤ) (hw : Even (W - w)) : IsUnit (uW d e w : A) :=
  isUnit_odd_int (odd_u W d e he w hw)

include he in
lemma isUnit_sig (i : N.ι) : IsUnit (sig N W d e i : A) := by
  refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun g _ => ?_
  refine (isUnit_uW W d e he _ ?_).neg
  exact ⟨g, by ring⟩

omit [OddUnits A] in
include htop in
lemma sig_succ (i k : N.ι) (hk : N.wt k = N.wt i - 2) :
    sig N W d e k = sig N W d e i * -(uW d e (N.wt i) : A) := by
  obtain ⟨r, hr⟩ := (htop i).2
  have h0 := (htop i).1
  have hf : fN N W k = fN N W i + 1 := by simp only [fN]; omega
  have hw : W - 2 * ((fN N W i : ℕ) : ℤ) = N.wt i := by simp only [fN]; omega
  simp only [sig, hf, Finset.prod_range_succ, hw]

/-- `v k = −u⁻¹` at the weight of `k` (Part O3). -/
def vInv (N : DPLattice A) (d e : ℤ) (k : N.ι) : A := -Ring.inverse (uW d e (N.wt k) : A)

include htop he in
lemma uW_mul_inv (k : N.ι) : (uW d e (N.wt k) : A) * Ring.inverse (uW d e (N.wt k)) = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_uW W d e he _ (htop k).2)

include htop he in
/-- (O3) the conjugation identity `σ · Gp N d · (−u⁻¹) = SigmaOp N e · σ`. -/
lemma Gp_conj :
    dg (sig N W d e) * Gp N d * dg (vInv N d e) = SigmaOp N e * dg (sig N W d e) := by
  have hu := uW_mul_inv N W d e htop he
  rw [Gp_eq, SigmaOp_eq, mul_sub, sub_mul, add_mul,
    Fd_sandwich N _ _ (sig N W d e) (fun i k hk => by
      rw [sig_succ N W d e htop i k hk, vInv]; linear_combination (sig N W d e i) * hu i),
    dg_mul, dg_mul, dg_mul, sub_eq_add_neg]
  congr 1
  apply LinearMap.ext; intro f; funext k
  simp only [dg_apply, LinearMap.neg_apply, Pi.neg_apply, Pi.mul_apply, vInv]
  rw [jj_eq W d e he]
  have := hu k
  simp only [uW] at this ⊢
  push_cast at this ⊢
  linear_combination (2 * sig N W d e k * ((e : A) - N.wt k) * f k) * this

include htop he in
lemma sig_Gp_eq (w : N.ι → A) :
    dg (sig N W d e) (Gp N d w) =
      SigmaOp N e ((dg (sig N W d e) ∘ₗ dg (fun k => -(uW d e (N.wt k) : A))) w) := by
  have h := LinearMap.congr_fun (Gp_conj N W d e htop he) (dg (fun k => -(uW d e (N.wt k) : A)) w)
  simp only [Module.End.mul_apply] at h
  have hvw : dg (vInv N d e) (dg (fun k => -(uW d e (N.wt k) : A)) w) = w := by
    funext k
    have := uW_mul_inv N W d e htop he k
    simp only [dg_apply, vInv]
    linear_combination (w k) * this
  rw [hvw] at h
  rw [LinearMap.comp_apply, h]

include htop he in
lemma comap_sig :
    Submodule.comap (dg (sig N W d e)) (LinearMap.range (SigmaOp N e)) =
      LinearMap.range (Gp N d) :=
  comap_eq_of_map _ _ _
    (map_range_eq _ _ _ (dg (sig N W d e) ∘ₗ dg (fun k => -(uW d e (N.wt k) : A)))
      (by
        rw [LinearMap.coe_comp]
        exact (dg_surjective (isUnit_sig N W d e he)).comp
          (dg_surjective fun k => (isUnit_uW W d e he _ (htop k).2).neg))
      (sig_Gp_eq N W d e htop he))
    (by rw [LinearMap.ker_eq_bot.2 (dg_injective (isUnit_sig N W d e he))]; exact bot_le)

/-- **(O3)** of `C39b_the_cube_side_on_the_half_lattice.md` (floor units), with `e` given through
the hypothesis `he : e = if Even (d − W) then d else d + 1`: the diagonal operator `σ` induces
`(N.ι → A) ⧸ range (Gp N d) ≃ₗ[A] (N.ι → A) ⧸ range (SigmaOp N e)`. -/
def O3equiv : ((N.ι → A) ⧸ LinearMap.range (Gp N d)) ≃ₗ[A]
    (N.ι → A) ⧸ LinearMap.range (SigmaOp N e) :=
  quotEquivOfComap (dg (sig N W d e)) (dg_surjective (isUnit_sig N W d e he)) _ _
    (comap_sig N W d e htop he)

end O3

/-- **(O3)** of `C39b_the_cube_side_on_the_half_lattice.md` (floor units): over `A` with
`[Doubling.OddUnits A]`, for `N : DPLattice A` and `W : ℤ` with (top)
`∀ i, N.wt i ≤ W ∧ Even (W − N.wt i)`, and every `d : ℤ`, with `e := d` if `Even (d − W)` and
`e := d + 1` otherwise: `(N.ι → A) ⧸ range (Gp N d) ≃ₗ[A] (N.ι → A) ⧸ range (SigmaOp N e)`. -/
theorem O3 [OddUnits A] (N : DPLattice A) (W : ℤ) (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i))
    (d : ℤ) :
    Nonempty (((N.ι → A) ⧸ LinearMap.range (Gp N d)) ≃ₗ[A]
      (N.ι → A) ⧸ LinearMap.range (SigmaOp N (if Even (d - W) then d else d + 1))) :=
  ⟨O3equiv N W d _ htop rfl⟩

/-! ### (O4) -/

/-- **(O4)** of `C39b_the_cube_side_on_the_half_lattice.md` (weights of the dance lattices): over
`[IsDomain A] [CharZero A] [Doubling.OddUnits A]`,
`∀ i, (Filt.T A l).wt i ≤ l ∧ Even (l − (Filt.T A l).wt i)`. -/
theorem O4 [IsDomain A] [CharZero A] [OddUnits A] (l : ℕ) :
    ∀ i, (Filt.T A l).wt i ≤ l ∧ Even ((l : ℤ) - (Filt.T A l).wt i) := by
  induction l using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [Filt.T_zero]
      intro i
      exact ⟨le_refl _, ⟨0, rfl⟩⟩
    · obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
      · rw [Filt.T_odd]
        rintro ⟨e, i⟩
        obtain ⟨h1, h2⟩ := ih l (by omega) i
        rw [Int.even_iff] at h2
        show 2 * (Filt.T A l).wt i + wtV e ≤ ((2 * l + 1 : ℕ) : ℤ) ∧
          Even (((2 * l + 1 : ℕ) : ℤ) - (2 * (Filt.T A l).wt i + wtV e))
        rw [Int.even_iff]
        fin_cases e <;> simp only [Fin.zero_eta, Fin.mk_one, wtV_zero, wtV_one] <;> push_cast <;>
          constructor <;> omega
      · rw [show 2 * l + 1 + 1 = 2 * l + 2 by ring, Filt.T_even]
        rintro ⟨e, e', i⟩
        obtain ⟨h1, h2⟩ := ih l (by omega) i
        rw [Int.even_iff] at h2
        show wtV e + (2 * (Filt.T A l).wt i + wtV e') ≤ ((2 * l + 2 : ℕ) : ℤ) ∧
          Even (((2 * l + 2 : ℕ) : ℤ) - (wtV e + (2 * (Filt.T A l).wt i + wtV e')))
        rw [Int.even_iff]
        fin_cases e <;> fin_cases e' <;> simp only [Fin.zero_eta, Fin.mk_one, wtV_zero, wtV_one] <;>
          push_cast <;> constructor <;> omega

/-! ### (O5) -/

/-- (O5, general form) for `M = Doubling.phi N` and (top):
`twoM (coker tauOp M (2d+1)) ≃+ coker SigmaOp N e`, `e = if Even (d − W) then d else d + 1`,
from (O1), (O2), (O3). -/
theorem O5_general [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A) (W : ℤ)
    (htop : ∀ i, N.wt i ≤ W ∧ Even (W - N.wt i)) (d : ℤ) (M : DPLattice A) (hM : M = phi N) :
    Nonempty (FoldGroup.twoM ((M.ι → A) ⧸ LinearMap.range (tauOp M (2 * d + 1))) ≃+
      (N.ι → A) ⧸ LinearMap.range (SigmaOp N (if Even (d - W) then d else d + 1))) := by
  subst hM
  exact ⟨(FoldGroup.twoMCongr (O1equiv N d).toAddEquiv).trans
    ((O2equiv (O2_pi _) (Gp N d)).trans (O3equiv N W d _ htop rfl).toAddEquiv)⟩

lemma sigL_odd (l j : ℕ) :
    Families.sigL ℤ_[2] (2 * l + 1) 1 j = tauOp (Filt.T ℤ_[2] (2 * l + 1)) (2 * ((l : ℤ) + j) + 1) := by
  have h : (((2 * ((l : ℤ) + j) + 1 : ℤ)) : ℤ_[2]) = ((2 * l + 1 : ℕ) : ℤ_[2]) + 2 * (j : ℤ_[2]) := by
    push_cast; ring
  rw [Families.sigL, tauOp, h, add_sub_assoc]
  simp only [Nat.sub_self, pow_zero, one_smul]
  rfl

lemma e_eq (l j : ℕ) :
    (if Even ((l : ℤ) + j - l) then (l : ℤ) + j else (l : ℤ) + j + 1) =
      (l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ) := by
  simp only [show (l : ℤ) + j - l = j by ring, Int.even_coe_nat]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [show (k + k + 1) / 2 = k by omega]; push_cast; ring
  · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.1 h
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega]; push_cast; ring

/-- **(O5)** of `C39b_the_cube_side_on_the_half_lattice.md` (Lemma 10.4(b) over `ℤ_[2]`), first
form: for every `l, j : ℕ`, with `N := Filt.T ℤ_[2] l` and `c := (j + 1) / 2`,
`FoldGroup.twoM (((Filt.T ℤ_[2] (2 * l + 1)).ι → ℤ_[2]) ⧸ range (Families.sigL ℤ_[2] (2 * l + 1) 1 j))
≃+ (N.ι → ℤ_[2]) ⧸ range (SigmaOp N (l + 2 * c))`. -/
theorem O5 (l j : ℕ) :
    Nonempty (FoldGroup.twoM (((Filt.T ℤ_[2] (2 * l + 1)).ι → ℤ_[2]) ⧸
        LinearMap.range (Families.sigL ℤ_[2] (2 * l + 1) 1 j)) ≃+
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ)))) := by
  rw [sigL_odd, ← e_eq]
  exact O5_general _ l (fun i => O4 l i) _ _ (Filt.T_odd ℤ_[2] l)

/-- **(O5)** of `C39b_the_cube_side_on_the_half_lattice.md` (Lemma 10.4(b) over `ℤ_[2]`), second
form: for every `l, j : ℕ`, with `N := Filt.T ℤ_[2] l` and `c := (j + 1) / 2`,
`FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j) ≃+
(N.ι → ℤ_[2]) ⧸ range (SigmaOp N (l + 2 * c))` (from the first form and C32 `sigEquivZ`). -/
theorem O5_X (l j : ℕ) :
    Nonempty (FoldGroup.twoM (FamilyGroup.X (Families.ds (2 * l + 1)) 1 j) ≃+
      ((Filt.T ℤ_[2] l).ι → ℤ_[2]) ⧸
        LinearMap.range (SigmaOp (Filt.T ℤ_[2] l) ((l : ℤ) + 2 * (((j + 1) / 2 : ℕ) : ℤ)))) := by
  obtain ⟨e⟩ := O5 l j
  exact ⟨(FoldGroup.twoMCongr (Families.sigEquivZ (2 * l + 1) 1 j).symm.toAddEquiv).trans e⟩

end FoldCube
