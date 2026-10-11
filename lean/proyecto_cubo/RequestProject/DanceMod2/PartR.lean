module

public import RequestProject.DanceMod2.Defs

/-!
# `C50b_the_dance_modulo_two.md`: Part R — the ring `RA R`

(R1): for every commutative ring `R`, `RA R` with `RA.one` and `RA.mul` is a commutative ring
(`RA.instCommRing`), with `RA.mul_apply` and `RA.one_apply`. The proof is C47's (R1)
(`RingK/PartR.lean`) with `R` in place of `𝒮`; the three reindexing lemmas of C47
(`RingK.RS.powerset_assoc`, `RingK.RS.range_assoc`, `RingK.RS.sum_powerset_sdiff`) are already
stated for an arbitrary coefficient (semi)ring and are reused as they are.

(R2): `(β * β) Δ q = (if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0) + 2 * x`, through the pairing
lemma `sum_involution_two` (a sum over a set with an involution preserving the summand is twice
something, when the summand at the fixed points is twice something).
-/

@[expose] public section

noncomputable section

namespace DanceMod2

open Finset

namespace RA

variable {R : Type*} [CommRing R]

/-- (R1) of `C50b_the_dance_modulo_two.md`: `(1 : RA R) Δ q` is given by the formula of `one`. -/
lemma one_apply (Δ : Finset ℕ) (q : ℕ) :
    (1 : RA R) Δ q = if Δ = ∅ ∧ q = 0 then 1 else 0 := rfl

/-- (R1) of `C50b_the_dance_modulo_two.md`: `(β * γ) Δ q` is given by the formula of `mul`. -/
lemma mul_apply (β γ : RA R) (Δ : Finset ℕ) (q : ℕ) :
    (β * γ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
      (Nat.choose q a : R) * β Δ₁ a * γ (Δ \ Δ₁) (q - a) := rfl

/-- (R1) of `C50b_the_dance_modulo_two.md`: the product of `RA R` is commutative. -/
theorem mul_comm' (β γ : RA R) : β * γ = γ * β := by
  refine RA.ext fun Δ q => ?_
  rw [mul_apply, mul_apply]
  refine (RingK.RS.sum_powerset_sdiff (M := R) Δ _).symm.trans
    (sum_congr rfl fun Δ₁ hΔ₁ => ?_)
  rw [mem_powerset] at hΔ₁
  beta_reduce
  rw [← sum_range_reflect]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  rw [Finset.sdiff_sdiff_eq_self hΔ₁, show q + 1 - 1 - a = q - a by omega,
    show q - (q - a) = a by omega, Nat.choose_symm (by omega)]
  ring

/-- (R1) of `C50b_the_dance_modulo_two.md`: the product of `RA R` is associative. -/
theorem mul_assoc' (β γ δ : RA R) : β * γ * δ = β * (γ * δ) := by
  refine RA.ext fun Δ q => ?_
  have L : (β * γ * δ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ Δ₂ ∈ Δ₁.powerset,
      ∑ a ∈ range (q + 1), ∑ b ∈ range (a + 1), ((q.choose a : R) * (a.choose b : R)) *
        (β Δ₂ b * γ (Δ₁ \ Δ₂) (a - b) * δ (Δ \ Δ₁) (q - a)) := by
    simp only [mul_apply, sum_mul, mul_sum]
    refine sum_congr rfl fun Δ₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun Δ₂ _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  have R' : (β * (γ * δ)) Δ q = ∑ Δ₂ ∈ Δ.powerset, ∑ Δ₃ ∈ (Δ \ Δ₂).powerset,
      ∑ b ∈ range (q + 1), ∑ c ∈ range (q - b + 1), ((q.choose b : R) * ((q - b).choose c : R)) *
        (β Δ₂ b * γ Δ₃ c * δ ((Δ \ Δ₂) \ Δ₃) (q - b - c)) := by
    simp only [mul_apply, mul_sum]
    refine sum_congr rfl fun Δ₂ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun Δ₃ _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring
  rw [L, R']
  refine Eq.trans ?_ (RingK.RS.powerset_assoc Δ (fun D₁ D₂ D₃ => ∑ b ∈ range (q + 1),
    ∑ c ∈ range (q - b + 1),
    ((q.choose b : R) * ((q - b).choose c : R)) * (β D₁ b * γ D₂ c * δ D₃ (q - b - c))))
  refine sum_congr rfl fun Δ₁ _ => sum_congr rfl fun Δ₂ _ => ?_
  exact RingK.RS.range_assoc q (fun b c d => β Δ₂ b * γ (Δ₁ \ Δ₂) c * δ (Δ \ Δ₁) d)

/-- (R1) of `C50b_the_dance_modulo_two.md`: `1` is a left unit. -/
theorem one_mul' (β : RA R) : 1 * β = β := by
  refine RA.ext fun Δ q => ?_
  rw [mul_apply, sum_eq_single ∅, sum_eq_single 0]
  · simp [one_apply]
  · intro b _ hb; simp [one_apply, hb]
  · intro h; simp at h
  · intro Δ₁ _ h
    exact sum_eq_zero fun a _ => by simp [one_apply, h]
  · intro h; simp at h

/-- (R1) of `C50b_the_dance_modulo_two.md`: left distributivity. -/
theorem left_distrib' (β γ δ : RA R) : β * (γ + δ) = β * γ + β * δ := by
  refine RA.ext fun Δ q => ?_
  simp only [mul_apply, add_apply, mul_add, sum_add_distrib]

/-- **(R1)** of `C50b_the_dance_modulo_two.md`: for every commutative ring `R`, `RA R` with the
pointwise addition and the unit `one` and product `mul` of the file is a commutative ring. -/
instance instCommRing : CommRing (RA R) :=
  { (inferInstance : AddCommGroup (RA R)) with
    mul := (· * ·)
    one := 1
    left_distrib := left_distrib'
    right_distrib := fun β γ δ => by
      rw [mul_comm' (β + γ), left_distrib', mul_comm' δ, mul_comm' δ]
    zero_mul := fun β => by refine RA.ext fun Δ q => ?_; simp [mul_apply, zero_apply]
    mul_zero := fun β => by refine RA.ext fun Δ q => ?_; simp [mul_apply, zero_apply]
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := fun β => by rw [mul_comm', one_mul']
    mul_comm := mul_comm' }

end RA

/-- **(R1)** of `C50b_the_dance_modulo_two.md`: for every commutative ring `R`, `RA R` is a
commutative ring (`RA.instCommRing`), with `(β * γ) Δ q` given by the formula of `mul` and
`(1 : RA R) Δ q` by the formula of `one`. -/
theorem R1 (R : Type*) [CommRing R] :
    (∀ β γ : RA R, β * γ = γ * β) ∧ (∀ β γ δ : RA R, β * γ * δ = β * (γ * δ)) ∧
    (∀ (β γ : RA R) Δ q, (β * γ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ a ∈ range (q + 1),
      (Nat.choose q a : R) * β Δ₁ a * γ (Δ \ Δ₁) (q - a)) ∧
    (∀ Δ q, (1 : RA R) Δ q = if Δ = ∅ ∧ q = 0 then 1 else 0) :=
  ⟨mul_comm, mul_assoc, RA.mul_apply, RA.one_apply⟩

/-- Helper for (R2) of `C50b_the_dance_modulo_two.md`: if every summand is twice something, so is
the sum. -/
lemma sum_two_mul_exists {α R : Type*} [CommRing R] (s : Finset α) (f : α → R)
    (hf : ∀ x ∈ s, ∃ w, f x = 2 * w) : ∃ w, ∑ x ∈ s, f x = 2 * w := by
  choose! w hw using hf
  exact ⟨∑ x ∈ s, w x, by rw [mul_sum]; exact sum_congr rfl hw⟩

/-- Helper for (R2) of `C50b_the_dance_modulo_two.md` (pairing): for an involution `σ` of `s`
preserving `f`, if `f` is twice something at every fixed point then `∑_{x ∈ s} f x` is twice
something. -/
lemma sum_involution_two {α R : Type*} [DecidableEq α] [CommRing R] (σ : α → α) (f : α → R) :
    ∀ s : Finset α, (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ (σ x) = x) → (∀ x ∈ s, f (σ x) = f x) →
      (∀ x ∈ s, σ x = x → ∃ w, f x = 2 * w) → ∃ w, ∑ x ∈ s, f x = 2 * w := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hs hσ hf hfix
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨0, by simp⟩
  by_cases hxx : σ x = x
  · -- remove the fixed point `x`
    have hsub : s.erase x ⊂ s := erase_ssubset hx
    obtain ⟨w, hw⟩ := ih _ hsub
      (fun y hy => by
        rw [mem_erase] at hy ⊢
        refine ⟨fun h => hy.1 ?_, hs y hy.2⟩
        rw [← hσ y hy.2, h, hxx])
      (fun y hy => hσ y (mem_of_mem_erase hy)) (fun y hy => hf y (mem_of_mem_erase hy))
      (fun y hy => hfix y (mem_of_mem_erase hy))
    obtain ⟨v, hv⟩ := hfix x hx hxx
    exact ⟨v + w, by rw [← add_sum_erase s f hx, hw, hv]; ring⟩
  · -- remove the pair `{x, σ x}`
    have hσx : σ x ∈ s.erase x := mem_erase.2 ⟨hxx, hs x hx⟩
    set t := (s.erase x).erase (σ x)
    have hsub : t ⊂ s := ((erase_ssubset hσx).trans (erase_ssubset hx))
    have hmem : ∀ y ∈ t, y ≠ σ x ∧ y ≠ x ∧ y ∈ s := fun y hy => by
      simp only [t, mem_erase] at hy; exact ⟨hy.1, hy.2.1, hy.2.2⟩
    obtain ⟨w, hw⟩ := ih _ hsub
      (fun y hy => by
        obtain ⟨h1, h2, h3⟩ := hmem y hy
        simp only [t, mem_erase]
        refine ⟨fun h => h2 ?_, fun h => h1 ?_, hs y h3⟩
        · rw [← hσ y h3, h, hσ x hx]
        · rw [← hσ y h3, h])
      (fun y hy => hσ y (hmem y hy).2.2) (fun y hy => hf y (hmem y hy).2.2)
      (fun y hy => hfix y (hmem y hy).2.2)
    refine ⟨f x + w, ?_⟩
    rw [← add_sum_erase s f hx, ← add_sum_erase _ f hσx, hw, hf x hx]
    ring

/-- **(R2)** of `C50b_the_dance_modulo_two.md`: for every commutative ring `R`, `β : RA R`, `Δ`
and `q`, `∃ x : R, (β * β) Δ q = (if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0) + 2 * x`. -/
theorem R2 {R : Type*} [CommRing R] (β : RA R) (Δ : Finset ℕ) (q : ℕ) :
    ∃ x : R, (β * β) Δ q = (if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0) + 2 * x := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, by simp [RA.mul_apply]⟩
  · simp only [zero_add]
    rw [RA.mul_apply, ← sum_product']
    refine sum_involution_two (fun x => (Δ \ x.1, q - x.2)) _ _ ?_ ?_ ?_ ?_
    · rintro ⟨Δ₁, a⟩ hx
      simp only [mem_product, mem_powerset, mem_range] at hx ⊢
      exact ⟨sdiff_subset, by omega⟩
    · rintro ⟨Δ₁, a⟩ hx
      simp only [mem_product, mem_powerset, mem_range] at hx
      simp only [Prod.mk.injEq]
      exact ⟨Finset.sdiff_sdiff_eq_self hx.1, by omega⟩
    · rintro ⟨Δ₁, a⟩ hx
      simp only [mem_product, mem_powerset, mem_range] at hx
      dsimp only
      rw [Finset.sdiff_sdiff_eq_self hx.1, show q - (q - a) = a by omega,
        Nat.choose_symm (by omega)]
      ring
    · rintro ⟨Δ₁, a⟩ hx heq
      simp only [mem_product, mem_powerset, mem_range] at hx
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      have hΔ₁ : Δ₁ = ∅ := by
        ext t
        simp only [Finset.notMem_empty, iff_false]
        intro ht
        have := h1 ▸ ht
        rw [mem_sdiff] at this
        exact this.2 ht
      have hΔ : Δ = ∅ := by rw [← sdiff_empty (s := Δ), ← hΔ₁, h1, hΔ₁]
      have hq : q ≠ 0 := fun hq => h ⟨hΔ, hq⟩
      have hq2 : q = 2 * a := by omega
      obtain ⟨k, hk⟩ : 2 ∣ q.choose a := by
        rw [hq2, ← Nat.centralBinom_eq_two_mul_choose]
        exact Nat.two_dvd_centralBinom_of_one_le (by omega)
      refine ⟨(k : R) * β Δ₁ a * β (Δ \ Δ₁) (q - a), ?_⟩
      dsimp only
      rw [hk]; push_cast; ring

end DanceMod2
