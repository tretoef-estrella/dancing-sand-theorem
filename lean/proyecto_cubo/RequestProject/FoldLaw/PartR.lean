module

public import RequestProject.FoldLaw.PartL
public import RequestProject.FoldLaw.Groups

/-!
# `C51_theorem_DW.md`: Part R — the mod-2 layer

* (R) `R`: for `n ≥ 2`, the `𝔽_2`-rank of the Laplacian of the folded cube is `aN n`.

Proof: the cokernel of `lapBar (ZMod 2) n` and `cokerBar n ⧸ 2·cokerBar n` are both quotients of
`Gbar n → ℤ` by the same subgroup (reduction modulo `2`), so they have the same cardinality
`ℓ_0(cokerBar n) = ℓ_0(ℤ) · ℓ_0(KBar n) = 2 · ℓ_0(Syl2 (KBar n))`; then (L1), and the count
`|V| = |V ⧸ range| · |range|` with `|Gbar n| = 2 ^ (n − 1)`.
-/

@[expose] public section

noncomputable section

namespace FoldLaw

open CubeLaplacian Fold FoldGroup BaiCounts

variable (n : ℕ)

/-- Reduction modulo `2` of functions on `Gbar n` (auxiliary for (R) of `C51_theorem_DW.md`). -/
def red : (Gbar n → ℤ) →+ (Gbar n → ZMod 2) :=
  AddMonoidHom.compLeft (Int.castAddHom (ZMod 2)) (Gbar n)

lemma red_apply (u : Gbar n → ℤ) (x : Gbar n) : red n u x = (u x : ZMod 2) := rfl

lemma red_lapBar (u : Gbar n → ℤ) : red n (lapBar ℤ n u) = lapBar (ZMod 2) n (red n u) := by
  funext x
  simp [red_apply, lapBar_apply]

lemma red_surjective : Function.Surjective (red n) := fun v =>
  ⟨fun x => ((v x).val : ℤ), by funext x; simp [red_apply]⟩

/-- The common kernel of the two reductions (auxiliary for (R) of `C51_theorem_DW.md`). -/
lemma red_mem_range_iff (f : Gbar n → ℤ) :
    red n f ∈ LinearMap.range (lapBar (ZMod 2) n) ↔
      ∃ g : Gbar n → ℤ, f - 2 • g ∈ LinearMap.range (lapBar ℤ n) := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := red_surjective n v
    rw [← red_lapBar] at hv
    have hd : ∀ x, (2 : ℤ) ∣ (f - lapBar ℤ n u) x := fun x => by
      have := congrFun hv x
      rw [red_apply, red_apply] at this
      have h0 : (((f - lapBar ℤ n u) x : ℤ) : ZMod 2) = 0 := by
        rw [Pi.sub_apply, Int.cast_sub, this, sub_self]
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h0
    refine ⟨fun x => (f - lapBar ℤ n u) x / 2, u, ?_⟩
    funext x
    have hx : (2 : ℤ) ∣ f x - lapBar ℤ n u x := hd x
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [nsmul_eq_mul, Nat.cast_ofNat, Int.mul_ediv_cancel' hx]
    ring
  · rintro ⟨g, u, hu⟩
    refine ⟨red n u, ?_⟩
    rw [← red_lapBar, hu]
    funext x
    simp only [red_apply, Pi.sub_apply, Pi.smul_apply, Int.cast_sub]
    rw [nsmul_eq_mul]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, sub_zero]

/-- The cokernel of the mod-`2` folded Laplacian has cardinality `ℓ_0(cokerBar n)` (auxiliary for
(R) of `C51_theorem_DW.md`). -/
lemma card_coker_two :
    Nat.card ((Gbar n → ZMod 2) ⧸ LinearMap.range (lapBar (ZMod 2) n)) = l0 (cokerBar n) := by
  let S : AddSubgroup (Gbar n → ℤ) :=
    (LinearMap.range (lapBar (ZMod 2) n)).toAddSubgroup.comap (red n)
  let φ1 : (Gbar n → ℤ) →+ (Gbar n → ZMod 2) ⧸ LinearMap.range (lapBar (ZMod 2) n) :=
    (LinearMap.range (lapBar (ZMod 2) n)).mkQ.toAddMonoidHom.comp (red n)
  let φ2 : (Gbar n → ℤ) →+ cokerBar n ⧸ twoPow (cokerBar n) 1 :=
    (QuotientAddGroup.mk' (twoPow (cokerBar n) 1)).comp
      (LinearMap.range (lapBar ℤ n)).mkQ.toAddMonoidHom
  have h1 := card_quot_of_surj φ1
    ((Submodule.mkQ_surjective _).comp (red_surjective n)) S fun f => by
      simp only [φ1, S, AddSubgroup.mem_comap, AddMonoidHom.comp_apply,
        LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_toAddSubgroup]
  have h2 := card_quot_of_surj φ2
    ((QuotientAddGroup.mk'_surjective _).comp (Submodule.mkQ_surjective _)) S fun f => by
      simp only [φ2, S, AddSubgroup.mem_comap, AddMonoidHom.comp_apply,
        LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup, mem_twoPow,
        red_mem_range_iff]
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨Submodule.Quotient.mk g, ?_⟩
        rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        rw [← neg_mem_iff, neg_sub]; exact hg
      · rintro ⟨c, hc⟩
        obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ c
        refine ⟨g, ?_⟩
        rw [pow_one, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.eq] at hc
        rw [← neg_mem_iff, neg_sub]; exact hc
  rw [← h1, h2]
  rfl

/-- `|Gbar n| = 2 ^ (n − 1)` for `n ≥ 1` (auxiliary for (R) of `C51_theorem_DW.md`). -/
lemma card_Gbar (hn : 1 ≤ n) : Nat.card (Gbar n) = 2 ^ (n - 1) := by
  have hG : Nat.card (G n) = 2 ^ n := by simp [G]
  have ha : addOrderOf (aElt n) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine addOrderOf_eq_prime (funext fun i => ?_) fun h => ?_
    · rfl
    · have := congrFun h ⟨0, hn⟩
      simp [aElt] at this
  have hL := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (AddSubgroup.zmultiples (aElt n))
  rw [Nat.card_zmultiples, ha, hG] at hL
  have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [h2] at hL
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) hL).symm

/-- **(R)** of `C51_theorem_DW.md` (Part R, the mod-2 layer): for every `n ≥ 2`,
`Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) = BaiCounts.aN n`. -/
theorem R (hn : 2 ≤ n) :
    Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n)) = BaiCounts.aN n := by
  haveI := KBar_finite n
  set r := Module.finrank (ZMod 2) (LinearMap.range (Fold.lapBar (ZMod 2) n))
  have hc : Nat.card ((Gbar n → ZMod 2) ⧸ LinearMap.range (lapBar (ZMod 2) n)) =
      2 ^ (1 + (2 ^ (n - 1) - 1 - aN n)) := by
    rw [card_coker_two, l0_congr (cokerBarEquivKBar n).toAddEquiv, l0_prod, l0_int,
      ← l0_syl2, L1 n hn, pow_add, pow_one]
  have hr : Nat.card (LinearMap.range (lapBar (ZMod 2) n)) = 2 ^ r := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hV : Nat.card (Gbar n → ZMod 2) = 2 ^ 2 ^ (n - 1) := by
    rw [Nat.card_fun, Nat.card_zmod, card_Gbar n (by omega)]
  have hL := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (LinearMap.range (lapBar (ZMod 2) n)).toAddSubgroup
  have hL' : Nat.card (Gbar n → ZMod 2) =
      Nat.card ((Gbar n → ZMod 2) ⧸ LinearMap.range (lapBar (ZMod 2) n)) *
        Nat.card (LinearMap.range (lapBar (ZMod 2) n)) := hL
  rw [hV, hc, hr, ← pow_add] at hL'
  have := Nat.pow_right_injective le_rfl hL'
  have h1 := aN_le n hn
  have h2 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  omega

end FoldLaw
