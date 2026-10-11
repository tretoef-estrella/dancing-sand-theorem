module

public import RequestProject.RingK.Defs

/-!
# `C47_the_ring_K_and_covariant_systems.md`: Part R — the ring `R_𝒮` (Lemma 10.14 (c))

(R1): `RS` with the operations of Definition 7 is a commutative ring (`RS.instCommRing`), in
which `2 = 0` (`R1`). (R2): `(β * β) Δ q = if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0`.
-/

@[expose] public section

noncomputable section

/- Instance search for `𝒮 = TrivSqZeroExt (ZMod 2) (PowerSeries (ZMod 2))` (used by `ring`) needs
more than the default budget. -/
set_option synthInstance.maxHeartbeats 400000

namespace RingK

open Finset

/-- Helper for Part R of `C47_the_ring_K_and_covariant_systems.md`: `2 = 0` in `𝒮`. -/
lemma two_S : (2 : S) = 0 := by
  rw [← one_add_one_eq_two]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_zero]; rfl
  · simp

/-- Helper for Part R of `C47_the_ring_K_and_covariant_systems.md`: `x + x = 0` in `𝒮`. -/
lemma add_self_S (x : S) : x + x = 0 := by
  rw [← two_mul, two_S, zero_mul]

/-- Helper for (R2) of `C47_the_ring_K_and_covariant_systems.md`: even naturals vanish in `𝒮`. -/
lemma natCast_S_of_two_dvd {n : ℕ} (h : 2 ∣ n) : (n : S) = 0 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_ofNat, two_S, zero_mul]

namespace RS

/-- Helper for (R1) of `C47_the_ring_K_and_covariant_systems.md`: reindexing ordered
decompositions `Δ = Δ₂ ⊔ Δ₃ ⊔ Δ₄` of a finite set. -/
lemma powerset_assoc {M : Type*} [AddCommMonoid M] (Δ : Finset ℕ)
    (g : Finset ℕ → Finset ℕ → Finset ℕ → M) :
    ∑ Δ₁ ∈ Δ.powerset, ∑ Δ₂ ∈ Δ₁.powerset, g Δ₂ (Δ₁ \ Δ₂) (Δ \ Δ₁) =
      ∑ Δ₂ ∈ Δ.powerset, ∑ Δ₃ ∈ (Δ \ Δ₂).powerset, g Δ₂ Δ₃ ((Δ \ Δ₂) \ Δ₃) := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1 \ x.2⟩) (fun x _ => ⟨x.1 ∪ x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨A, B⟩ hx
    simp only [mem_sigma, mem_powerset] at hx ⊢
    exact ⟨hx.2.trans hx.1, sdiff_subset_sdiff hx.1 (Subset.refl _)⟩
  · rintro ⟨A, B⟩ hx
    simp only [mem_sigma, mem_powerset] at hx ⊢
    exact ⟨union_subset hx.1 (hx.2.trans sdiff_subset), subset_union_left⟩
  · rintro ⟨A, B⟩ hx
    simp only [mem_sigma, mem_powerset] at hx
    simp [union_sdiff_of_subset hx.2]
  · rintro ⟨A, B⟩ hx
    simp only [mem_sigma, mem_powerset] at hx
    have hd : Disjoint A B := by
      rw [disjoint_iff_ne]
      intro a ha b hb hab
      have := hx.2 hb
      rw [mem_sdiff] at this
      exact this.2 (hab ▸ ha)
    simp [union_sdiff_cancel_left hd]
  · rintro ⟨A, B⟩ hx
    simp only [mem_sigma, mem_powerset] at hx
    congr 1
    ext t
    simp only [mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun h => h2 (hx.2 h)⟩, fun h => h2 h.1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, fun h => h3 ⟨h, h2⟩⟩

/-- Helper for (R1) of `C47_the_ring_K_and_covariant_systems.md`: the divided-power identity
`C(q, a) C(a, b) = C(q, b) C(q − b, a − b)` and the reindexing `a = b + c`. -/
lemma range_assoc {R : Type*} [CommSemiring R] (q : ℕ) (g : ℕ → ℕ → ℕ → R) :
    ∑ a ∈ range (q + 1), ∑ b ∈ range (a + 1),
        ((q.choose a : R) * (a.choose b : R)) * g b (a - b) (q - a) =
      ∑ b ∈ range (q + 1), ∑ c ∈ range (q - b + 1),
        ((q.choose b : R) * ((q - b).choose c : R)) * g b c (q - b - c) := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1 - x.2⟩) (fun x _ => ⟨x.1 + x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · rintro ⟨b, c⟩ hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · rintro ⟨a, b⟩ hx
    simp only [mem_sigma, mem_range] at hx
    simp only [Sigma.mk.injEq, heq_eq_eq]
    exact ⟨by omega, trivial⟩
  · rintro ⟨b, c⟩ hx
    simp only [mem_sigma, mem_range] at hx
    simp
  · rintro ⟨a, b⟩ hx
    simp only [mem_sigma, mem_range] at hx
    dsimp only
    rw [← Nat.cast_mul, Nat.choose_mul (by omega), Nat.cast_mul,
      show q - a = q - b - (a - b) by omega]

/-- Helper for (R1) of `C47_the_ring_K_and_covariant_systems.md`: `Δ₁ ↦ Δ \ Δ₁` is an
involution of `Δ.powerset`. -/
lemma sum_powerset_sdiff {M : Type*} [AddCommMonoid M] (Δ : Finset ℕ) (f : Finset ℕ → M) :
    ∑ Δ₁ ∈ Δ.powerset, f (Δ \ Δ₁) = ∑ Δ₁ ∈ Δ.powerset, f Δ₁ := by
  refine sum_nbij' (Δ \ ·) (Δ \ ·) ?_ ?_ ?_ ?_ ?_
  · intro A _; simp
  · intro A _; simp
  · intro A hA; simp only [mem_powerset] at hA; exact Finset.sdiff_sdiff_eq_self hA
  · intro A hA; simp only [mem_powerset] at hA; exact Finset.sdiff_sdiff_eq_self hA
  · intro A _; rfl

/-- (R1) of `C47_the_ring_K_and_covariant_systems.md`: the product of `R_𝒮` is commutative. -/
theorem mul_comm' (β γ : RS) : β * γ = γ * β := by
  refine RS.ext fun Δ q => ?_
  rw [mul_apply, mul_apply]
  refine (sum_powerset_sdiff (M := S) Δ _).symm.trans (sum_congr rfl fun Δ₁ hΔ₁ => ?_)
  rw [mem_powerset] at hΔ₁
  beta_reduce
  rw [← sum_range_reflect]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_range] at ha
  rw [Finset.sdiff_sdiff_eq_self hΔ₁, show q + 1 - 1 - a = q - a by omega,
    show q - (q - a) = a by omega, Nat.choose_symm (by omega)]
  ring

/-- (R1) of `C47_the_ring_K_and_covariant_systems.md`: the product of `R_𝒮` is associative. -/
theorem mul_assoc' (β γ δ : RS) : β * γ * δ = β * (γ * δ) := by
  refine RS.ext fun Δ q => ?_
  have L : (β * γ * δ) Δ q = ∑ Δ₁ ∈ Δ.powerset, ∑ Δ₂ ∈ Δ₁.powerset,
      ∑ a ∈ range (q + 1), ∑ b ∈ range (a + 1), ((q.choose a : S) * (a.choose b : S)) *
        (β Δ₂ b * γ (Δ₁ \ Δ₂) (a - b) * δ (Δ \ Δ₁) (q - a)) := by
    simp only [mul_apply, sum_mul, mul_sum]
    refine sum_congr rfl fun Δ₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun Δ₂ _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  have R : (β * (γ * δ)) Δ q = ∑ Δ₂ ∈ Δ.powerset, ∑ Δ₃ ∈ (Δ \ Δ₂).powerset,
      ∑ b ∈ range (q + 1), ∑ c ∈ range (q - b + 1), ((q.choose b : S) * ((q - b).choose c : S)) *
        (β Δ₂ b * γ Δ₃ c * δ ((Δ \ Δ₂) \ Δ₃) (q - b - c)) := by
    simp only [mul_apply, mul_sum]
    refine sum_congr rfl fun Δ₂ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun Δ₃ _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring
  rw [L, R]
  refine Eq.trans ?_ (powerset_assoc Δ (fun D₁ D₂ D₃ => ∑ b ∈ range (q + 1),
    ∑ c ∈ range (q - b + 1),
    ((q.choose b : S) * ((q - b).choose c : S)) * (β D₁ b * γ D₂ c * δ D₃ (q - b - c))))
  refine sum_congr rfl fun Δ₁ _ => sum_congr rfl fun Δ₂ _ => ?_
  exact range_assoc q (fun b c d => β Δ₂ b * γ (Δ₁ \ Δ₂) c * δ (Δ \ Δ₁) d)

/-- (R1) of `C47_the_ring_K_and_covariant_systems.md`: `1` is a left unit. -/
theorem one_mul' (β : RS) : 1 * β = β := by
  refine RS.ext fun Δ q => ?_
  rw [mul_apply, sum_eq_single ∅, sum_eq_single 0]
  · simp [one_apply]
  · intro b _ hb; simp [one_apply, hb]
  · intro h; simp at h
  · intro Δ₁ _ h
    exact sum_eq_zero fun a _ => by simp [one_apply, h]
  · intro h; simp at h

/-- (R1) of `C47_the_ring_K_and_covariant_systems.md`: left distributivity. -/
theorem left_distrib' (β γ δ : RS) : β * (γ + δ) = β * γ + β * δ := by
  refine RS.ext fun Δ q => ?_
  simp only [mul_apply, add_apply, mul_add, sum_add_distrib]

/-- **(R1)** of `C47_the_ring_K_and_covariant_systems.md`: `RS` with the pointwise addition and
the unit and product of Definition 7 is a commutative ring. -/
instance instCommRing : CommRing RS :=
  { (inferInstance : AddCommGroup RS) with
    mul := (· * ·)
    one := 1
    left_distrib := left_distrib'
    right_distrib := fun β γ δ => by
      rw [mul_comm' (β + γ), left_distrib', mul_comm' δ, mul_comm' δ]
    zero_mul := fun β => by refine RS.ext fun Δ q => ?_; simp [mul_apply, zero_apply]
    mul_zero := fun β => by refine RS.ext fun Δ q => ?_; simp [mul_apply, zero_apply]
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := fun β => by rw [mul_comm', one_mul']
    mul_comm := mul_comm' }

end RS

/-- **(R1)** of `C47_the_ring_K_and_covariant_systems.md`: `RS` is a commutative ring
(`RS.instCommRing`) whose product is commutative and associative, and `(2 : RS) = 0`. -/
theorem R1 : (∀ β γ : RS, β * γ = γ * β) ∧ (∀ β γ δ : RS, β * γ * δ = β * (γ * δ)) ∧
    (2 : RS) = 0 := by
  refine ⟨mul_comm, mul_assoc, ?_⟩
  rw [← one_add_one_eq_two]
  refine RS.ext fun Δ q => ?_
  rw [RS.add_apply, add_self_S, RS.zero_apply]

/-- **(R2)** of `C47_the_ring_K_and_covariant_systems.md`: for every `β : RS`,
`(β * β) Δ q = if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0`. -/
theorem R2 (β : RS) (Δ : Finset ℕ) (q : ℕ) :
    (β * β) Δ q = if Δ = ∅ ∧ q = 0 then β ∅ 0 * β ∅ 0 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [RS.mul_apply]
  · rw [RS.mul_apply, ← sum_product']
    refine sum_involution (fun x _ => (Δ \ x.1, q - x.2)) ?_ ?_ ?_ ?_
    · rintro ⟨Δ₁, a⟩ hx
      simp only [mem_product, mem_powerset, mem_range] at hx
      dsimp only
      rw [Finset.sdiff_sdiff_eq_self hx.1, show q - (q - a) = a by omega, Nat.choose_symm (by omega)]
      rw [show (q.choose a : S) * β (Δ \ Δ₁) (q - a) * β Δ₁ a =
        (q.choose a : S) * β Δ₁ a * β (Δ \ Δ₁) (q - a) by ring]
      exact add_self_S _
    · rintro ⟨Δ₁, a⟩ hx hne heq
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
      apply hne
      have hq2 : q = 2 * a := by omega
      have h2 : (q.choose a : S) = 0 := by
        apply natCast_S_of_two_dvd
        rw [hq2, ← Nat.centralBinom_eq_two_mul_choose]
        exact Nat.two_dvd_centralBinom_of_one_le (by omega)
      dsimp only
      rw [h2, zero_mul, zero_mul]
    · rintro ⟨Δ₁, a⟩ hx
      simp only [mem_product, mem_powerset, mem_range] at hx ⊢
      exact ⟨sdiff_subset, by omega⟩
    · rintro ⟨Δ₁, a⟩ hx
      simp only [mem_product, mem_powerset, mem_range] at hx
      simp only [Prod.mk.injEq]
      exact ⟨Finset.sdiff_sdiff_eq_self hx.1, by omega⟩

end RingK
