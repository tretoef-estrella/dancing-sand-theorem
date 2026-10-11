module

public import RequestProject.InvFloors.Defs
public import RequestProject.InvFloors.Digits

/-!
# `C42_floors_and_corollary_10_9.md`: (F1)–(F6), the floors of `inH`, `outH`

All by strong induction on `l` (for all `r`), following the recursions of `InvBlock.inH`,
`InvBlock.outH`, `slotOf`, `ioIdx`:
* (F1) `F1`: `ri`, `unitEquiv⁻¹`, `inj₀`, `relabel⁻¹`, `vpack`, `castLat` send basis vectors to
  basis vectors (`ri_single`, `unitEquiv_symm_single`, `inj0_single`, `relab_symm_single`,
  `vpack_single`, `castLat_single`);
* (F2) `F2`: the same maps read a coordinate (`out1`, `relabel`, `vpack⁻¹`, `castLat⁻¹`);
* (F3) `F3`: `FormalProp.splitEquiv r j = (j / 2, j % 2)` and `Nat.div_div_eq_div_mul`;
* (F4), (F5) `F4`, `F5` from `floor_ioIdx`, with the weights `phiWt (e, i) = 2 wt i + wtV e`,
  `tensorWt (a, p) = wtV a + wt p`, and the bit bookkeeping of `Digits.lean`;
* (F6) `F6`: `Dset ⊆ Ids` and C32 (B0b) `l + 1 = 2^k + Σ_{t ∈ I} 2^t`.
-/

@[expose] public section

noncomputable section

namespace InvFloors

open DPLattice Doubling Filt FormalOps FormalDance FormalAct InvBlock

/-! ### The slot pair of `FormalProp.splitEquiv` -/

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F3)): `j = 2 (splitEquiv r j).1 + (splitEquiv r j).2`. -/
lemma splitEquiv_val (r : ℕ) (x : Fin (r * 2)) :
    (x : ℕ) = ((FormalProp.splitEquiv r x).2 : ℕ) + 2 * ((FormalProp.splitEquiv r x).1 : ℕ) := by
  have h := Dance.splitIso_apply r ((Dance.splitIso r).symm x)
  rw [OrderIso.apply_symm_apply] at h
  have h2 := congrArg Fin.val h
  rw [finProdFinEquiv_apply_val] at h2
  exact h2

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F3)): `(splitEquiv r j).1 = j / 2`. -/
lemma splitEquiv_fst (r : ℕ) (x : Fin (r * 2)) :
    ((FormalProp.splitEquiv r x).1 : ℕ) = (x : ℕ) / 2 := by
  have := splitEquiv_val r x
  have h2 := ((FormalProp.splitEquiv r x).2).isLt
  omega

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F4)–(F5)): `(splitEquiv r j).2 = j % 2`. -/
lemma splitEquiv_snd (r : ℕ) (x : Fin (r * 2)) :
    ((FormalProp.splitEquiv r x).2 : ℕ) = (x : ℕ) % 2 := by
  have := splitEquiv_val r x
  have h2 := ((FormalProp.splitEquiv r x).2).isLt
  omega

variable {A : Type*} [CommRing A]

/-! ### Basis vectors -/

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F1)): `ri` moves a basis vector along `Fin.cast`. -/
lemma ri_single {a b : ℕ} (h : a = b) (j : Fin a) :
    ri h (Pi.single j (1 : A)) = Pi.single (Fin.cast h j) 1 := by
  funext i
  simp only [ri_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; ext; simp
  · rintro rfl; ext; simp

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F1)): `unitEquiv⁻¹` of a basis vector. -/
lemma unitEquiv_symm_single {n : Type*} {_ : DecidableEq n} (s : n) :
    (unitEquiv : (n → Unit → A) ≃ₗ[A] (n → A)).symm (Pi.single s 1) =
      Pi.single s (Pi.single () 1) := by
  funext s' u
  by_cases hs : s' = s
  · subst hs; simp [unitEquiv]
  · simp [unitEquiv, hs]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F1)): `inj₀` of a basis vector is the basis
vector `(0, i)`. -/
lemma inj0_single {n ι : Type*} {_ : DecidableEq n} {_ : DecidableEq ι}
    [DecidableEq (Fin 2 × ι)] (s : n) (i : ι) :
    inj0 (A := A) (Pi.single s (Pi.single i 1)) = Pi.single s (Pi.single ((0 : Fin 2), i) 1) := by
  funext s' p
  rcases p with ⟨e, i'⟩
  by_cases hs : s' = s
  · subst hs
    by_cases he : e = 0
    · subst he; by_cases hi : i' = i
      · subst hi; simp
      · simp [hi]
    · simp [he]
  · simp [hs]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F1)): `relabel⁻¹` of a basis vector. -/
lemma relab_symm_single (r : ℕ) {X : Type*} [AddCommGroup X] [Module A X]
    [DecidableEq (Fin r × Fin 2)] (s : Fin (r * 2))
    (x : X) : (relab (A := A) r X).symm (Pi.single (M := fun _ => X) s x) =
      Pi.single (FormalProp.splitEquiv r s) x := by
  funext q
  rw [LinearEquiv.funCongrLeft_symm]
  show Pi.single (M := fun _ => X) s x ((FormalProp.splitEquiv r).symm q) = _
  by_cases hq : q = FormalProp.splitEquiv r s
  · subst hq; rw [Equiv.symm_apply_apply, Pi.single_eq_same, Pi.single_eq_same]
  · have : (FormalProp.splitEquiv r).symm q ≠ s := by
      intro h; apply hq; rw [← h, Equiv.apply_symm_apply]
    simp [hq, this]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F1)): `vpack` of a basis vector. -/
lemma vpack_single {n ι : Type*} [DecidableEq n] {_ : DecidableEq (n × Fin 2)}
    {_ : DecidableEq ι} [DecidableEq (Fin 2 × ι)] (q : n × Fin 2) (p : ι) :
    vpack (A := A) (Pi.single q (Pi.single p 1)) = Pi.single q.1 (Pi.single (q.2, p) 1) := by
  rcases q with ⟨s, a⟩
  funext s' ⟨e, p'⟩
  simp only [vpack_apply, Pi.add_apply, bvec_apply]
  by_cases hs : s' = s
  · subst hs
    by_cases he : e = a
    · subst he
      fin_cases e <;> simp [Pi.single_apply]
    · fin_cases e <;> fin_cases a <;> simp_all
  · fin_cases e <;> simp [hs]


/-! ### Reading coordinates -/

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F2)): `unitEquiv` reads at `()`. -/
lemma unitEquiv_read {n : Type*} (w : n → Unit → A) (s : n) :
    (unitEquiv : (n → Unit → A) ≃ₗ[A] (n → A)) w s = w s () := rfl

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F2)): `out₁` reads the index `(1, i)`. -/
lemma out1_read {n ι : Type*} (w : n → Fin 2 × ι → A) (s : n) (i : ι) :
    out1 w s i = w s (1, i) := rfl

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F2)): `relabel` reads at `splitEquiv r j`. -/
lemma relab_read (r : ℕ) {X : Type*} [AddCommGroup X] [Module A X] (u : Fin r × Fin 2 → X)
    (j : Fin (r * 2)) : relab (A := A) r X u j = u (FormalProp.splitEquiv r j) := rfl

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F2)): `vpack⁻¹` reads the slot `(s, a)`, index
`p` at the slot `s`, index `(a, p)`. -/
lemma vpack_symm_read {n ι : Type*} (w : n → Fin 2 × ι → A) (q : n × Fin 2) (p : ι) :
    (vpack (A := A)).symm w q p = w q.1 (q.2, p) := rfl

/-! ### Unfolding the recursions -/

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): an unfolding equation of the
recursion. -/
lemma slotOf_zero (r : ℕ) (j : Fin (Dance.slots (Families.ds 0) r)) :
    slotOf 0 r j = Fin.cast (slots_zero r) j := by
  rw [slotOf]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): an unfolding equation of the
recursion. -/
lemma slotOf_succ_pos {n : ℕ} (h : n % 2 = 0) (r : ℕ) (j : Fin (Dance.slots (Families.ds (n + 1)) r)) :
    slotOf (n + 1) r j = slotOf (n / 2) r (Fin.cast (slots_succ_pos h r) j) := by
  rw [slotOf.eq_2, dif_pos h]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): an unfolding equation of the
recursion. -/
lemma slotOf_succ_neg {n : ℕ} (h : ¬ n % 2 = 0) (r : ℕ)
    (j : Fin (Dance.slots (Families.ds (n + 1)) r)) :
    slotOf (n + 1) r j = (FormalProp.splitEquiv r (slotOf (n / 2) (r * 2)
        (Fin.cast (slots_succ_neg h r) j))).1 := by
  rw [slotOf.eq_2, dif_neg h]

variable [IsDomain A] [CharZero A] [OddUnits A]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): an unfolding equation of the
recursion. -/
lemma ioIdx_zero (b : Fin 2) (r : ℕ) (j : Fin (Dance.slots (Families.ds 0) r)) :
    ioIdx (A := A) b 0 r j = castIdx (T_zero (A := A)).symm (() : (one A).ι) := by
  rw [ioIdx]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): an unfolding equation of the
recursion. -/
lemma ioIdx_succ_pos (b : Fin 2) {n : ℕ} (h : n % 2 = 0) (r : ℕ)
    (j : Fin (Dance.slots (Families.ds (n + 1)) r)) :
    ioIdx (A := A) b (n + 1) r j = castIdx (T_succ_pos A h).symm
      ((b, ioIdx b (n / 2) r (Fin.cast (slots_succ_pos h r) j)) : (phi (T A (n / 2))).ι) := by
  rw [ioIdx.eq_2, dif_pos h]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, Definitions): an unfolding equation of the
recursion. -/
lemma ioIdx_succ_neg (b : Fin 2) {n : ℕ} (h : ¬ n % 2 = 0) (r : ℕ)
    (j : Fin (Dance.slots (Families.ds (n + 1)) r)) :
    ioIdx (A := A) b (n + 1) r j = castIdx (T_succ_neg A h).symm
      (((FormalProp.splitEquiv r (slotOf (n / 2) (r * 2) (Fin.cast (slots_succ_neg h r) j))).2,
        ((b, ioIdx b (n / 2) (r * 2) (Fin.cast (slots_succ_neg h r) j)) :
          (phi (T A (n / 2))).ι)) : (tensorV (phi (T A (n / 2)))).ι) := by
  rw [ioIdx.eq_2, dif_neg h]


/-! ### (F1)–(F3) -/

/-- (F1) of `C42_floors_and_corollary_10_9.md`, the induction (auxiliary). -/
theorem F1_aux (l : ℕ) : ∀ (r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)),
    inH (A := A) l r (Pi.single j 1) =
      Pi.single (slotOf l r j) (Pi.single (ioIdx (A := A) 0 l r j) 1) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases l with _ | n
  · intro r j
    rw [inH, slotOf_zero, ioIdx_zero]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ri_single]
    erw [unitEquiv_symm_single]
    erw [castLat_single]
  · intro r j
    by_cases h : n % 2 = 0
    · rw [inH, dif_pos h, slotOf_succ_pos h, ioIdx_succ_pos 0 h]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ri_single]
      rw [ih (n / 2) (by omega)]
      erw [inj0_single]
      erw [castLat_single]
    · rw [inH, dif_neg h, slotOf_succ_neg h, ioIdx_succ_neg 0 h]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ri_single]
      rw [ih (n / 2) (by omega)]
      erw [relab_symm_single]
      erw [inj0_single]
      erw [vpack_single]
      erw [castLat_single]

/-- (F2) of `C42_floors_and_corollary_10_9.md`, the induction (auxiliary). -/
theorem F2_aux (l : ℕ) : ∀ (r : ℕ) (w : Fin r → (T A l).ι → A)
    (j : Fin (Dance.slots (Families.ds l) r)),
    outH l r w j = w (slotOf l r j) (ioIdx (A := A) 1 l r j) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases l with _ | n
  · intro r w j
    rw [outH, slotOf_zero, ioIdx_zero]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ri_apply, unitEquiv_read]
    erw [castLat_symm_read]
  · intro r w j
    by_cases h : n % 2 = 0
    · rw [outH, dif_pos h, slotOf_succ_pos h, ioIdx_succ_pos 1 h]
      simp only [LinearMap.comp_apply, ri_apply]
      rw [ih (n / 2) (by omega), out1_read]
      erw [castLat_symm_read]
    · rw [outH, dif_neg h, slotOf_succ_neg h, ioIdx_succ_neg 1 h]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ri_apply]
      rw [ih (n / 2) (by omega), relab_read, out1_read]
      erw [vpack_symm_read]
      erw [castLat_symm_read]


/-- (F3) of `C42_floors_and_corollary_10_9.md`, the induction (auxiliary; `slotOf` involves no
ring). -/
theorem F3_aux (l : ℕ) : ∀ (r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)),
    ((slotOf l r j : Fin r) : ℕ) = (j : ℕ) / 2 ^ Dance.mCount (Families.ds l) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases l with _ | n
  · intro r j
    have hm : Dance.mCount (Families.ds 0) = 0 := by rw [Families.ds_zero]; rfl
    rw [slotOf_zero, hm, Fin.val_cast]
    simp
  · intro r j
    by_cases h : n % 2 = 0
    · have hm : Dance.mCount (Families.ds (n + 1)) = Dance.mCount (Families.ds (n / 2)) := by
        rw [ds_succ_pos h]; rfl
      rw [slotOf_succ_pos h, ih (n / 2) (by omega), hm, Fin.val_cast]
    · have hm : Dance.mCount (Families.ds (n + 1)) = Dance.mCount (Families.ds (n / 2)) + 1 := by
        rw [ds_succ_neg h]; rfl
      rw [slotOf_succ_neg h, splitEquiv_fst, ih (n / 2) (by omega), hm, Fin.val_cast,
        Nat.div_div_eq_div_mul, pow_succ]

/-- Auxiliary (`C42_floors_and_corollary_10_9.md`, (F4)–(F5)): `wtV a = 1 − 2a`. -/
lemma wtV_eq (a : Fin 2) : wtV a = 1 - 2 * ((a : ℕ) : ℤ) := by
  fin_cases a <;> rfl

/-- (F4), (F5) of `C42_floors_and_corollary_10_9.md` together (auxiliary): the floor of
`ioIdx b l r j` is `o_D + b (2^k − 1)`. -/
theorem floor_ioIdx (b : Fin 2) (l : ℕ) : ∀ (r : ℕ) (j : Fin (Dance.slots (Families.ds l) r)),
    (l : ℤ) - (T A l).wt (ioIdx b l r j) =
      2 * ((Rulers.oE (Windows.Dset (Families.ds l) j) : ℤ) +
        ((b : ℕ) : ℤ) * (2 ^ (Families.ds l).length - 1)) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  rcases l with _ | n
  · intro r j
    rw [ioIdx_zero, wt_castIdx]
    have hD : ∀ s, Windows.Dset (Families.ds 0) s = ∅ := by
      intro s; rw [Families.ds_zero]; rfl
    have hk : (Families.ds 0).length = 0 := by rw [Families.ds_zero]; rfl
    rw [hD, hk]
    simp [one, Rulers.oE]
  · intro r j
    by_cases h : n % 2 = 0
    · rw [ioIdx_succ_pos b h, wt_castIdx]
      have hw : ∀ i : (T A (n / 2)).ι, (phi (T A (n / 2))).wt ((b, i) : (phi (T A (n / 2))).ι) =
          2 * (T A (n / 2)).wt i + wtV b := fun _ => rfl
      rw [hw]
      have e := ih (n / 2) (by omega) r (Fin.cast (slots_succ_pos h r) j)
      have hD : ∀ s, Rulers.oE (Windows.Dset (Families.ds (n + 1)) s) =
          2 * Rulers.oE (Windows.Dset (Families.ds (n / 2)) s) := by
        intro s; rw [ds_succ_pos h, oE_Dset_cons_false]
      have hk : (Families.ds (n + 1)).length = (Families.ds (n / 2)).length + 1 := by
        rw [ds_succ_pos h]; rfl
      rw [hD, hk, wtV_eq, pow_succ]
      rw [Fin.val_cast] at e
      have hn : ((n + 1 : ℕ) : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + 1 := by omega
      rw [hn]
      push_cast
      have hb := b.isLt
      interval_cases hbv : (b : ℕ) <;> push_cast at e ⊢ <;> linarith
    · rw [ioIdx_succ_neg b h, wt_castIdx]
      set a := (FormalProp.splitEquiv r (slotOf (n / 2) (r * 2)
        (Fin.cast (slots_succ_neg h r) j))).2 with ha
      have hw : ∀ i : (T A (n / 2)).ι,
          (tensorV (phi (T A (n / 2)))).wt ((a, ((b, i) : (phi (T A (n / 2))).ι)) :
            (tensorV (phi (T A (n / 2)))).ι) = wtV a + (2 * (T A (n / 2)).wt i + wtV b) :=
        fun _ => rfl
      rw [hw]
      have e := ih (n / 2) (by omega) (r * 2) (Fin.cast (slots_succ_neg h r) j)
      have hD : ∀ s, Rulers.oE (Windows.Dset (Families.ds (n + 1)) s) =
          s / 2 ^ Dance.mCount (Families.ds (n / 2)) % 2 +
            2 * Rulers.oE (Windows.Dset (Families.ds (n / 2)) s) := by
        intro s; rw [ds_succ_neg h, oE_Dset_cons_true]
      have hk : (Families.ds (n + 1)).length = (Families.ds (n / 2)).length + 1 := by
        rw [ds_succ_neg h]; rfl
      have haval : (a : ℕ) = (j : ℕ) / 2 ^ Dance.mCount (Families.ds (n / 2)) % 2 := by
        rw [ha, splitEquiv_snd, F3_aux, Fin.val_cast]
      rw [hD, hk, wtV_eq, wtV_eq, pow_succ, ← haval]
      rw [Fin.val_cast] at e
      have hn : ((n + 1 : ℕ) : ℤ) = 2 * ((n / 2 : ℕ) : ℤ) + 2 := by omega
      rw [hn]
      push_cast
      have hb := b.isLt
      interval_cases hbv : (b : ℕ) <;> push_cast at e ⊢ <;> linarith

/-- (F6) of `C42_floors_and_corollary_10_9.md`, for every natural number `s` (more general than a
final slot): `o(D(ds, s)) + 2^k − 1 ≤ l`. -/
theorem F6_nat (l s : ℕ) :
    Rulers.oE (Windows.Dset (Families.ds l) s) + 2 ^ (Families.ds l).length - 1 ≤ l := by
  have h1 := Families.B0b l
  have h2 : Rulers.oE (Windows.Dset (Families.ds l) s) ≤
      ∑ t ∈ Windows.Ids (Families.ds l), 2 ^ t :=
    Finset.sum_le_sum_of_subset (Dset_subset_Ids _ _)
  omega

end InvFloors
