module

public import RequestProject.Families.All
public import RequestProject.TheoremF.All

/-!
# `C33_the_main_theorem.md`: Part S — the shape of a family

Encodings (namespace `MainTheorem`):

* `λ` is written `lam : ℕ`; its digit list is C32's `Families.ds lam : List Bool`.
* `k λ := (ds λ).length`, `I λ := Windows.Ids (ds λ)` (a `Finset ℕ`), `N λ := 2 ^ Dance.mCount (ds λ)`;
  these abbreviations are written out in every statement (no new definitions).
* `Rulers.lam k I = 2 ^ k + oE I - 1` and `Rulers.oE E = Σ_{t ∈ E} 2 ^ t` are C3's.
* The dancers are C7's `TheoremF.dancer I p`.
* The small clocks are C16's `FamilyGroup.SC ds` and the big clocks C16's
  `FamilyGroup.Q e = ℤ_[2] ⧸ span {2 ^ e}`; `ℤ_[2]` is `PadicInt 2`.
-/

@[expose] public section

namespace MainTheorem

open Finset Families
open scoped Pointwise

/-! ### (S1) -/

/-- **(S1)** of `C33_the_main_theorem.md` (Part S): `Rulers.lam (k λ) (I λ) = λ`. -/
theorem S1_lam (lam : ℕ) : Rulers.lam (ds lam).length (Windows.Ids (ds lam)) = lam := by
  have h := B0b lam
  unfold Rulers.lam Rulers.oE
  omega

/-- **(S1)** of `C33_the_main_theorem.md` (Part S): `Rulers.oE (I λ) = Σ_{t ∈ I λ} 2^t`. -/
theorem S1_oE (lam : ℕ) :
    Rulers.oE (Windows.Ids (ds lam)) = ∑ t ∈ Windows.Ids (ds lam), 2 ^ t := rfl

/-- **(S1)** of `C33_the_main_theorem.md` (Part S): `λ + 1 = 2^{k λ} + Rulers.oE (I λ)`. -/
theorem S1_succ (lam : ℕ) :
    lam + 1 = 2 ^ (ds lam).length + Rulers.oE (Windows.Ids (ds lam)) := B0b lam

/-- **(S1)** of `C33_the_main_theorem.md` (Part S), consequence: the `ξ_D` of C3 is
`λ + 1 − 2 o_D`, the `ξ_D` of §1.2. -/
theorem S1_xi (lam : ℕ) (D : Finset ℕ) :
    Rulers.xi (ds lam).length (Windows.Ids (ds lam)) D = lam + 1 - 2 * Rulers.oE D := by
  rw [Rulers.xi, S1_lam]

/-! ### (S2) -/

/-- **(S2)** of `C33_the_main_theorem.md` (Part S): `ds λ = [] ↔ λ = 0`. -/
theorem S2 (lam : ℕ) : ds lam = [] ↔ lam = 0 := by
  constructor
  · intro h
    have hb := B0b lam
    rw [h] at hb
    simp [Windows.Ids] at hb
    omega
  · rintro rfl; exact ds_zero

/-- **(S2)** of `C33_the_main_theorem.md` (Part S), consequence: `1 ≤ k λ` for `λ ≥ 1`. -/
theorem S2_length (lam : ℕ) (h : 1 ≤ lam) : 1 ≤ (ds lam).length := by
  rcases Nat.eq_zero_or_pos (ds lam).length with h0 | h0
  · exact absurd ((S2 lam).1 (List.eq_nil_of_length_eq_zero h0)) (by omega)
  · exact h0

/-! ### (S3) -/

/-- **(S3)** of `C33_the_main_theorem.md` (Part S): `I λ ⊆ range (k λ)`. -/
theorem S3_subset (lam : ℕ) : Windows.Ids (ds lam) ⊆ range (ds lam).length :=
  filter_subset _ _

/-- **(S3)** of `C33_the_main_theorem.md` (Part S): `|I λ| = mCount (ds λ)` (so `N λ = 2^{|I|}`). -/
theorem S3_card (lam : ℕ) : (Windows.Ids (ds lam)).card = Dance.mCount (ds lam) :=
  Windows.card_Ids _

/-! ### (S4) -/

/-- `(Fin n → ℤ_[2]) ⧸ (2^a • ⊤) ≃ (Fin n → Q a)` (auxiliary for (S4) of
`C33_the_main_theorem.md`). -/
noncomputable def quotSmulTopEquiv (n a : ℕ) :
    ((Fin n → ℤ_[2]) ⧸ (2 : ℤ_[2]) ^ a • (⊤ : Submodule ℤ_[2] (Fin n → ℤ_[2]))) ≃ₗ[ℤ_[2]]
      (Fin n → FamilyGroup.Q a) := by
  have h : (2 : ℤ_[2]) ^ a • (⊤ : Submodule ℤ_[2] (Fin n → ℤ_[2])) =
      Submodule.pi Set.univ (fun _ : Fin n => (Ideal.span {(2 : ℤ_[2]) ^ a} : Submodule ℤ_[2] ℤ_[2])) := by
    ext v
    simp only [Submodule.mem_pi, Set.mem_univ, true_implies, Ideal.mem_span_singleton]
    constructor
    · intro hv
      rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv with ⟨w, -, rfl⟩
      intro j
      exact ⟨w j, by simp [mul_comm]⟩
    · intro hv
      choose w hw using hv
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, Submodule.mem_top, ?_⟩
      funext j
      simp [hw j, mul_comm]
  exact (Submodule.quotEquivOfEq _ _ h).trans (Submodule.quotientPi _)

/-- **(S4)** of `C33_the_main_theorem.md` (Part S), explicit equivalence:
`SC ds ≃ Π_{a : Fin k} (Fin (2^{k + m − 1 − a}) → Q a)`. -/
noncomputable def S4equiv (ds : List Bool) :
    FamilyGroup.SC ds ≃ₗ[ℤ_[2]]
      ((a : Fin ds.length) → Fin (2 ^ (ds.length + Dance.mCount ds - 1 - a)) → FamilyGroup.Q a) :=
  LinearEquiv.piCongrRight fun _ => quotSmulTopEquiv _ _

/-- **(S4)** of `C33_the_main_theorem.md` (Part S): for every `ds`,
`FamilyGroup.SC ds ≅ Π_{a : Fin k} (Fin (2^{k + m − 1 − a}) → FamilyGroup.Q a)`. -/
theorem S4 (ds : List Bool) :
    Nonempty (FamilyGroup.SC ds ≃ₗ[ℤ_[2]]
      ((a : Fin ds.length) → Fin (2 ^ (ds.length + Dance.mCount ds - 1 - a)) →
        FamilyGroup.Q a)) :=
  ⟨S4equiv ds⟩

/-- **(S4)** of `C33_the_main_theorem.md` (Part S): `FamilyGroup.Q 0` is a subsingleton (the factor
`a = 0` of the small clocks is zero). -/
theorem S4_Q0 : Subsingleton (FamilyGroup.Q 0) := by
  unfold FamilyGroup.Q
  rw [pow_zero, Ideal.span_singleton_one]
  exact Submodule.Quotient.subsingleton_iff.2 rfl

/-! ### (S5) -/

/-- **(S5)** of `C33_the_main_theorem.md` (Part S), o-order: for `p < q < N λ`,
`oE (dancer (I λ) p) < oE (dancer (I λ) q)`. -/
theorem S5_order (lam : ℕ) {p q : ℕ} (hpq : p < q) (hq : q < 2 ^ Dance.mCount (ds lam)) :
    Rulers.oE (TheoremF.dancer (Windows.Ids (ds lam)) p) <
      Rulers.oE (TheoremF.dancer (Windows.Ids (ds lam)) q) :=
  TheoremF.lemma_0b hpq (by rw [S3_card]; exact hq)

/-- **(S5)** of `C33_the_main_theorem.md` (Part S): `dancer (I λ) 0 = ∅`.  (More general: for every
`I`.) -/
theorem S5_zero (I : Finset ℕ) : TheoremF.dancer I 0 = ∅ := by
  unfold TheoremF.dancer
  apply filter_false_of_mem
  intro t _
  simp [Houses.bit]

/-- **(S5)** of `C33_the_main_theorem.md` (Part S): every `D ⊆ I λ` is `dancer (I λ) p` for exactly
one `p < N λ`. -/
theorem S5_unique (lam : ℕ) {D : Finset ℕ} (hD : D ⊆ Windows.Ids (ds lam)) :
    ∃! p, p < 2 ^ Dance.mCount (ds lam) ∧ TheoremF.dancer (Windows.Ids (ds lam)) p = D := by
  rw [← S3_card]
  exact TheoremF.lemma_0c_existsUnique hD

end MainTheorem
