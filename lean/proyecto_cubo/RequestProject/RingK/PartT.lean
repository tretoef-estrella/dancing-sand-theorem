module

public import RequestProject.RingK.PartS
public import RequestProject.RingK.PartR

/-!
# `C47_the_ring_K_and_covariant_systems.md`: Part T — covariant systems (Lemma 10.14 (a), (b))

(T0)–(T3), for fixed `P : Finset ℕ`, `h : ℕ`, `c : ℤ_[2]`. The unit system `Γ₁` is written
inline as `fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0`.
-/

@[expose] public section

noncomputable section

namespace RingK

open Finset FormalOps

/-- **(T0)** of `C47_the_ring_K_and_covariant_systems.md`:
`oS (D₁ ∪ D₂) = oS D₁ + oS D₂` for disjoint `D₁`, `D₂`. -/
theorem T0 (D₁ D₂ : Finset ℕ) (hd : Disjoint D₁ D₂) : oS (D₁ ∪ D₂) = oS D₁ + oS D₂ := by
  unfold oS
  exact sum_union hd

/-- Helper for (T1) of `C47_the_ring_K_and_covariant_systems.md`: coefficients of a finite sum
of formal operators. -/
lemma Bf_coef_sum {ι : Type*} (s : Finset ι) (x : ι → Bf ℤ_[2]) (m : ℕ) (f : ℤ) :
    (∑ i ∈ s, x i).coef m f = ∑ i ∈ s, (x i).coef m f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, Bf.coef_add, ih]

/-- Helper for (T1) of `C47_the_ring_K_and_covariant_systems.md`: `o_D = o_{D₁} + o_{D \ D₁}`
for `D₁ ⊆ D`. -/
lemma oS_sdiff {D₁ D : Finset ℕ} (h : D₁ ⊆ D) : oS D = oS D₁ + oS (D \ D₁) := by
  rw [← T0 _ _ disjoint_sdiff, union_sdiff_of_subset h]

/-- Helper for (T1) of `C47_the_ring_K_and_covariant_systems.md`: the entries of a covariant
system. -/
@[simp] lemma covSys_coef (P : Finset ℕ) (h : ℕ) (c : ℤ_[2])
    (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (D D' : Dn P) (m : ℕ) (f : ℤ) :
    (covSys P h c Γ D D').coef m f = if D'.1 ⊆ D.1 then
      Γ (D.1 \ D'.1) m ((2 : ℤ_[2]) ^ h * f + oS D.1 + c) else 0 := rfl

/-- **(T1)** of `C47_the_ring_K_and_covariant_systems.md` (products):
`covSys P h c Γ * covSys P h c Γ' = covSys P h c (prodFun h Γ Γ')`. -/
theorem T1_mul (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    covSys P h c Γ * covSys P h c Γ' = covSys P h c (prodFun h Γ Γ') := by
  funext D D'
  refine Bf.ext fun m f => ?_
  rw [Matrix.mul_apply, Bf_coef_sum, covSys_coef]
  simp only [Bf.coef_mul, covSys_coef]
  split_ifs with hDD'
  · -- the terms with `D' ⊆ D₁ ⊆ D`
    have hterm : ∀ D₁ : Dn P, (∑ a ∈ range (m + 1), (m.choose a : ℤ_[2]) *
        (if D₁.1 ⊆ D.1 then Γ (D.1 \ D₁.1) a ((2 : ℤ_[2]) ^ h * f + oS D.1 + c) else 0) *
        (if D'.1 ⊆ D₁.1 then Γ' (D₁.1 \ D'.1) (m - a)
          ((2 : ℤ_[2]) ^ h * ((f - a : ℤ) : ℤ_[2]) + oS D₁.1 + c) else 0)) =
        if D₁.1 ⊆ D.1 ∧ D'.1 ⊆ D₁.1 then ∑ a ∈ range (m + 1), (m.choose a : ℤ_[2]) *
          Γ (D.1 \ D₁.1) a ((2 : ℤ_[2]) ^ h * f + oS D.1 + c) *
          Γ' (D₁.1 \ D'.1) (m - a) ((2 : ℤ_[2]) ^ h * ((f - a : ℤ) : ℤ_[2]) + oS D₁.1 + c)
        else 0 := by
      intro D₁
      by_cases h1 : D₁.1 ⊆ D.1 <;> by_cases h2 : D'.1 ⊆ D₁.1 <;> simp [h1, h2]
    simp only [hterm]
    rw [← sum_filter]
    unfold prodFun
    refine sum_nbij' (fun D₁ => D.1 \ D₁.1) (fun Δ₁ => ⟨D.1 \ Δ₁, sdiff_subset.trans D.2⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro D₁ hD₁
      simp only [mem_filter, mem_univ, true_and] at hD₁
      simp only [mem_powerset]
      exact sdiff_subset_sdiff (Subset.refl _) hD₁.2
    · intro Δ₁ hΔ₁
      simp only [mem_powerset] at hΔ₁
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨sdiff_subset, fun x hx => ?_⟩
      rw [mem_sdiff]
      refine ⟨hDD' hx, fun hx' => ?_⟩
      have := hΔ₁ hx'
      rw [mem_sdiff] at this
      exact this.2 hx
    · intro D₁ hD₁
      simp only [mem_filter, mem_univ, true_and] at hD₁
      exact Subtype.ext (Finset.sdiff_sdiff_eq_self hD₁.1)
    · intro Δ₁ hΔ₁
      simp only [mem_powerset] at hΔ₁
      exact Finset.sdiff_sdiff_eq_self (hΔ₁.trans sdiff_subset)
    · intro D₁ hD₁
      simp only [mem_filter, mem_univ, true_and] at hD₁
      refine sum_congr rfl fun a _ => ?_
      have hset : (D.1 \ D'.1) \ (D.1 \ D₁.1) = D₁.1 \ D'.1 := by
        ext x
        simp only [mem_sdiff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨by by_contra hx; exact h3 ⟨h1, hx⟩, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨hD₁.1 h1, h2⟩, fun h => h.2 h1⟩
      have hpos : (2 : ℤ_[2]) ^ h * ((f - a : ℤ) : ℤ_[2]) + oS D₁.1 + c =
          (2 : ℤ_[2]) ^ h * f + oS D.1 + c - a * 2 ^ h - oS (D.1 \ D₁.1) := by
        rw [oS_sdiff hD₁.1]
        push_cast
        ring
      rw [hset, hpos]
  · -- no term survives
    refine sum_eq_zero fun D₁ _ => sum_eq_zero fun a _ => ?_
    by_cases h1 : D₁.1 ⊆ D.1
    · by_cases h2 : D'.1 ⊆ D₁.1
      · exact absurd (h2.trans h1) hDD'
      · simp [h2]
    · simp [h1]

/-- **(T1)** of `C47_the_ring_K_and_covariant_systems.md` (sums):
`covSys P h c Γ + covSys P h c Γ' = covSys P h c (Γ + Γ')`. -/
theorem T1_add (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) :
    covSys P h c Γ + covSys P h c Γ' = covSys P h c (Γ + Γ') := by
  funext D D'
  refine Bf.ext fun m f => ?_
  rw [Matrix.add_apply, Bf.coef_add]
  simp only [covSys_coef]
  split_ifs <;> simp

/-- **(T1)** of `C47_the_ring_K_and_covariant_systems.md` (constant multiples):
`a • covSys P h c Γ = covSys P h c (a • Γ)`. -/
theorem T1_smul (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2])
    (a : ℤ_[2]) : a • covSys P h c Γ = covSys P h c (a • Γ) := by
  funext D D'
  refine Bf.ext fun m f => ?_
  rw [Matrix.smul_apply, Bf.coef_smul]
  simp only [covSys_coef]
  split_ifs <;> simp

/-- **(T1)** of `C47_the_ring_K_and_covariant_systems.md` (unit):
`1 = covSys P h c Γ₁` with `Γ₁ Δ m y = if Δ = ∅ ∧ m = 0 then 1 else 0`. -/
theorem T1_one (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) :
    (1 : Matrix (Dn P) (Dn P) (Bf ℤ_[2])) =
      covSys P h c (fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0) := by
  funext D D'
  refine Bf.ext fun m f => ?_
  rw [Matrix.one_apply, covSys_coef]
  by_cases hD : D = D'
  · subst hD
    simp
  · have hne : ¬ (D'.1 ⊆ D.1 ∧ D.1 \ D'.1 = ∅) := by
      rintro ⟨h1, h2⟩
      rw [sdiff_eq_empty_iff_subset] at h2
      exact hD (Subtype.ext (Subset.antisymm h2 h1))
    rw [if_neg hD, Bf.coef_zero]
    split_ifs with h1 h2
    · exact absurd ⟨h1, h2.1⟩ hne
    · rfl
    · rfl

/-- **(T1)** of `C47_the_ring_K_and_covariant_systems.md`, all together. -/
theorem T1 (P : Finset ℕ) (h : ℕ) (c : ℤ_[2]) :
    (∀ Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2],
      covSys P h c Γ * covSys P h c Γ' = covSys P h c (prodFun h Γ Γ')) ∧
    (∀ Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2],
      covSys P h c Γ + covSys P h c Γ' = covSys P h c (Γ + Γ')) ∧
    (∀ (a : ℤ_[2]) (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]),
      a • covSys P h c Γ = covSys P h c (a • Γ)) ∧
    (1 : Matrix (Dn P) (Dn P) (Bf ℤ_[2])) =
      covSys P h c (fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0) :=
  ⟨T1_mul P h c, T1_add P h c, fun a Γ => T1_smul P h c Γ a, T1_one P h c⟩

/-- Helper for (T2) of `C47_the_ring_K_and_covariant_systems.md`: `Kr` is closed under finite
sums. -/
lemma Kr_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ_[2] → ℤ_[2]) (hg : ∀ i ∈ s, g i ∈ Kr) :
    (∑ i ∈ s, g i) ∈ Kr := by
  classical
  induction s using Finset.induction_on with
  | empty => exact K3_const 0
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact K3_add (hg i (mem_insert_self i s)) (ih fun j hj => hg j (mem_insert_of_mem hj))

/-- Helper for (T2), (T3) of `C47_the_ring_K_and_covariant_systems.md`: `prodFun` as a double
sum of functions, each a constant multiple of `Γ Δ₁ a` times a shift of `Γ' (Δ \ Δ₁) (m − a)`. -/
lemma prodFun_eq (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) :
    prodFun h Γ Γ' Δ m = ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (m + 1),
      (fun y => (m.choose a : ℤ_[2]) * Γ Δ₁ a y) *
        (fun y => Γ' (Δ \ Δ₁) (m - a) (y - ((a : ℤ_[2]) * 2 ^ h + oS Δ₁))) := by
  funext y
  simp only [prodFun, Finset.sum_apply, Pi.mul_apply, sub_sub]

/-- **(T2)** of `C47_the_ring_K_and_covariant_systems.md`: if all `Γ Δ m`, `Γ' Δ m` are in `Kr`,
so are all `prodFun h Γ Γ' Δ m`; likewise sums, constant multiples and `Γ₁`. -/
theorem T2 (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : ∀ Δ m, Γ Δ m ∈ Kr)
    (hΓ' : ∀ Δ m, Γ' Δ m ∈ Kr) :
    (∀ Δ m, prodFun h Γ Γ' Δ m ∈ Kr) ∧ (∀ Δ m, (Γ + Γ') Δ m ∈ Kr) ∧
    (∀ (a : ℤ_[2]) Δ m, (a • Γ) Δ m ∈ Kr) ∧
    (∀ (Δ : Finset ℕ) (m : ℕ),
      (fun _ : ℤ_[2] => if Δ = ∅ ∧ m = 0 then (1 : ℤ_[2]) else 0) ∈ Kr) := by
  refine ⟨fun Δ m => ?_, fun Δ m => K3_add (hΓ Δ m) (hΓ' Δ m), fun a Δ m => K3_smul a (hΓ Δ m),
    fun Δ m => K3_const _⟩
  rw [prodFun_eq]
  exact Kr_sum _ _ fun Δ₁ _ => Kr_sum _ _ fun a _ =>
    K3_mul (K3_smul _ (hΓ _ _)) (K4 (hΓ' _ _) _)

/-- Helper for (T3) of `C47_the_ring_K_and_covariant_systems.md`: `theta 0 = 0`. -/
lemma theta_zero : theta 0 = 0 := by
  have := S1_const 0
  rw [map_zero, TrivSqZeroExt.inl_zero] at this
  exact this

/-- Helper for (T3) of `C47_the_ring_K_and_covariant_systems.md`: `theta` of a finite sum of
elements of `Kr`. -/
lemma theta_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ_[2] → ℤ_[2]) (hg : ∀ i ∈ s, g i ∈ Kr) :
    theta (∑ i ∈ s, g i) = ∑ i ∈ s, theta (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, g j ∈ Kr := fun j hj => hg j (mem_insert_of_mem hj)
    rw [sum_insert hi, sum_insert hi, S1_add (hg i (mem_insert_self i s)) (Kr_sum s g hs), ih hs]

/-- Helper for (T3) of `C47_the_ring_K_and_covariant_systems.md`: `thetaSys Γ Δ m = theta (Γ Δ m)`. -/
lemma thetaSys_apply (Γ : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (Δ : Finset ℕ) (m : ℕ) :
    thetaSys Γ Δ m = theta (Γ Δ m) := rfl

/-- Helper for (T3) of `C47_the_ring_K_and_covariant_systems.md`: `inl (red n) = n` in `𝒮`. -/
lemma inl_red_natCast (n : ℕ) : TrivSqZeroExt.inl (red (n : ℤ_[2])) = (n : S) := by
  rw [map_natCast, TrivSqZeroExt.inl_natCast]

/-- **(T3)** of `C47_the_ring_K_and_covariant_systems.md` (`Θ_h` is multiplicative): under the
hypotheses of (T2), `thetaSys (prodFun h Γ Γ') = thetaSys Γ * thetaSys Γ'`,
`thetaSys (Γ + Γ') = thetaSys Γ + thetaSys Γ'` and `thetaSys Γ₁ = 1`. -/
theorem T3 (h : ℕ) (Γ Γ' : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]) (hΓ : ∀ Δ m, Γ Δ m ∈ Kr)
    (hΓ' : ∀ Δ m, Γ' Δ m ∈ Kr) :
    thetaSys (prodFun h Γ Γ') = thetaSys Γ * thetaSys Γ' ∧
    thetaSys (Γ + Γ') = thetaSys Γ + thetaSys Γ' ∧
    thetaSys (fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0) = 1 := by
  refine ⟨RS.ext fun Δ m => ?_, RS.ext fun Δ m => ?_, RS.ext fun Δ m => ?_⟩
  · rw [thetaSys_apply, prodFun_eq, RS.mul_apply]
    rw [theta_sum _ _ fun Δ₁ _ => Kr_sum _ _ fun a _ =>
      K3_mul (K3_smul _ (hΓ _ _)) (K4 (hΓ' _ _) _)]
    refine sum_congr rfl fun Δ₁ _ => ?_
    rw [theta_sum _ _ fun a _ => K3_mul (K3_smul _ (hΓ _ _)) (K4 (hΓ' _ _) _)]
    refine sum_congr rfl fun a _ => ?_
    rw [S1_mul (K3_smul _ (hΓ _ _)) (K4 (hΓ' _ _) _), S1_smul _ (hΓ _ _), S2 (hΓ' _ _),
      inl_red_natCast, thetaSys_apply, thetaSys_apply]
  · rw [thetaSys_apply, RS.add_apply, thetaSys_apply, thetaSys_apply]
    exact S1_add (hΓ Δ m) (hΓ' Δ m)
  · rw [thetaSys_apply, RS.one_apply]
    by_cases hc : Δ = ∅ ∧ m = 0
    · simp only [hc, and_self, if_true]
      rw [S1_const, map_one, TrivSqZeroExt.inl_one]
    · simp only [hc, if_false]
      rw [S1_const, map_zero, TrivSqZeroExt.inl_zero]

end RingK
