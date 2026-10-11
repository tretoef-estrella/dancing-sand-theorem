module

public import RequestProject.OddParts.Defs

/-!
# `C52_odd_parts.md`: Part Q — the transfer lemma

* (Q0) `Q0`, (Q1) `Q1`, (Q2) `Q2`.

Auxiliary facts used in Parts B and C: transport of `Sylp` along additive equivalences
(`sylpCongr`), removal of a factor without `p`-part (`sylpProdBotRight`), the transfer for quotients
(`sylpQuotTransfer`), and the cokernel of a diagonal map (`diagQuotEquiv`).
-/

@[expose] public section

noncomputable section

namespace OddParts

open Finset

/-- **(Q0)** of `C52_odd_parts.md`: `Sylp 2 T = CubeLaplacian.Syl2 T`. -/
theorem Q0 (T : Type*) [AddCommGroup T] : Sylp 2 T = CubeLaplacian.Syl2 T := rfl

lemma mem_Sylp {p : ℕ} {T : Type*} [AddCommGroup T] {y : T} :
    y ∈ Sylp p T ↔ ∃ k : ℕ, (p ^ k : ℕ) • y = 0 := Iff.rfl

/-- If `p ∤ m` and `p ^ k • y = 0`, then `y = a • (m • y)` for some integer `a`. -/
lemma exists_inv_smul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) {T : Type*} [AddCommGroup T]
    (k : ℕ) : ∃ a : ℤ, ∀ y : T, (p ^ k : ℕ) • y = 0 → a • (m • y) = y := by
  have hcop : Nat.Coprime m (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hpm))
  refine ⟨Nat.gcdA m (p ^ k), fun y hy => ?_⟩
  have hb := Nat.gcd_eq_gcd_ab m (p ^ k)
  rw [hcop, Nat.cast_one] at hb
  have hy' : ((p ^ k : ℕ) : ℤ) • y = 0 := by rw [natCast_zsmul]; exact hy
  have e1 : ((m : ℤ) * Nat.gcdA m (p ^ k)) • y = Nat.gcdA m (p ^ k) • (m • y) := by
    rw [mul_comm, mul_smul, natCast_zsmul]
  have e2 : (((p ^ k : ℕ) : ℤ) * Nat.gcdB m (p ^ k)) • y = 0 := by
    rw [mul_comm, mul_smul, hy', smul_zero]
  calc Nat.gcdA m (p ^ k) • (m • y)
      = ((m : ℤ) * Nat.gcdA m (p ^ k) + ((p ^ k : ℕ) : ℤ) * Nat.gcdB m (p ^ k)) • y := by
        rw [add_smul, e1, e2, add_zero]
    _ = y := by rw [← hb, one_smul]

/-- An additive map sends `Sylp p A` into `Sylp p B`. -/
def sylpMap (p : ℕ) {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    Sylp p A →+ Sylp p B where
  toFun y := ⟨f y, by
    obtain ⟨k, hk⟩ := y.2
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

/-- **(Q1)** of `C52_odd_parts.md`: if `g ∘ f = m •` and `f ∘ g = m •` and the prime `p` does not
divide `m`, then `Sylp p A ≃+ Sylp p B`. -/
theorem Q1 {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (g : B →+ A) (m : ℕ)
    (hgf : ∀ a, g (f a) = m • a) (hfg : ∀ b, f (g b) = m • b) (p : ℕ) (hp : p.Prime)
    (hpm : ¬ p ∣ m) : Nonempty (Sylp p A ≃+ Sylp p B) := by
  refine ⟨AddEquiv.ofBijective (sylpMap p f) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, k, hk⟩ hy
    have h0 : f y = 0 := congrArg Subtype.val hy
    obtain ⟨a, ha⟩ := exists_inv_smul hp hpm (T := A) k
    ext
    show y = 0
    rw [← ha y hk, ← hgf, h0, map_zero, smul_zero]
  · rintro ⟨z, k, hk⟩
    obtain ⟨a, ha⟩ := exists_inv_smul hp hpm (T := B) k
    refine ⟨⟨g (a • z), k, ?_⟩, ?_⟩
    · rw [← map_nsmul, smul_comm, hk, smul_zero, map_zero]
    · ext
      show f (g (a • z)) = z
      rw [hfg, smul_comm, ha z hk]

/-- Transport of `Sylp p` along an additive equivalence. -/
def sylpCongr (p : ℕ) {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    Sylp p A ≃+ Sylp p B where
  toFun := sylpMap p e.toAddMonoidHom
  invFun := sylpMap p e.symm.toAddMonoidHom
  left_inv y := by ext; simp [sylpMap]
  right_inv y := by ext; simp [sylpMap]
  map_add' := map_add _

/-- The `p`-part of a product (auxiliary for (Q2)). -/
def sylpProd (p : ℕ) (A B : Type*) [AddCommGroup A] [AddCommGroup B] :
    Sylp p (A × B) ≃+ Sylp p A × Sylp p B where
  toFun y := (sylpMap p (AddMonoidHom.fst A B) y, sylpMap p (AddMonoidHom.snd A B) y)
  invFun z := ⟨(z.1.1, z.2.1), by
    have h1 : ((z.1.1, 0) : A × B) ∈ Sylp p (A × B) := by
      obtain ⟨k, hk⟩ := z.1.2
      exact ⟨k, by simp [hk]⟩
    have h2 : ((0, z.2.1) : A × B) ∈ Sylp p (A × B) := by
      obtain ⟨k, hk⟩ := z.2.2
      exact ⟨k, by simp [hk]⟩
    simpa using add_mem h1 h2⟩
  left_inv y := by ext <;> rfl
  right_inv z := by ext <;> rfl
  map_add' _ _ := by ext <;> rfl

/-- `Sylp p ℤ = ⊥` for `p ≠ 0` (auxiliary for (Q2)). -/
lemma sylp_int_eq_bot {p : ℕ} (hp : p ≠ 0) : Sylp p ℤ = ⊥ := by
  ext y
  simp only [AddSubgroup.mem_bot]
  constructor
  · rintro ⟨k, hk⟩
    rw [nsmul_eq_mul] at hk
    rcases mul_eq_zero.mp hk with h | h
    · exact absurd (by exact_mod_cast h) (pow_ne_zero k hp)
    · exact h
  · rintro rfl; exact zero_mem _

/-- **(Q2)** of `C52_odd_parts.md`: for abelian groups `A`, `B` and every prime `p`,
`Sylp p (A × B) ≃+ Sylp p A × Sylp p B`, and `Sylp p ℤ = ⊥`. (The first part holds for every `p`,
see `sylpProd`.) -/
theorem Q2 (A B : Type*) [AddCommGroup A] [AddCommGroup B] (p : ℕ) (hp : p.Prime) :
    Nonempty (Sylp p (A × B) ≃+ Sylp p A × Sylp p B) ∧ Sylp p ℤ = ⊥ :=
  ⟨⟨sylpProd p A B⟩, sylp_int_eq_bot hp.ne_zero⟩

/-- Removing a factor without `p`-part. -/
def sylpProdBotRight (p : ℕ) (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (hB : Sylp p B = ⊥) : Sylp p (A × B) ≃+ Sylp p A :=
  (sylpProd p A B).trans
    { toFun := Prod.fst
      invFun := fun y => (y, 0)
      left_inv := fun z => by
        have : z.2 = 0 := by
          ext
          have : (z.2 : B) ∈ (⊥ : AddSubgroup B) := hB ▸ z.2.2
          exact AddSubgroup.mem_bot.mp this
        ext <;> simp [this]
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- Removing a factor without `p`-part, on the left. -/
def sylpProdBotLeft (p : ℕ) (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (hA : Sylp p A = ⊥) : Sylp p (A × B) ≃+ Sylp p B :=
  (sylpCongr p (AddEquiv.prodComm)).trans (sylpProdBotRight p B A hA)

/-- The transfer lemma for quotients: maps `φ`, `ψ` compatible with the submodules whose composites
are `m •`, with `p ∤ m`, give `Sylp p (M ⧸ P) ≃+ Sylp p (N ⧸ Q)`. -/
theorem sylpQuotTransfer {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (P : Submodule ℤ M) (Q : Submodule ℤ N) (φ : M →ₗ[ℤ] N) (ψ : N →ₗ[ℤ] M)
    (hφ : P ≤ Q.comap φ) (hψ : Q ≤ P.comap ψ) (m : ℕ) (h1 : ∀ x, ψ (φ x) = m • x)
    (h2 : ∀ y, φ (ψ y) = m • y) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    Nonempty (Sylp p (M ⧸ P) ≃+ Sylp p (N ⧸ Q)) := by
  refine Q1 (P.mapQ Q φ hφ).toAddMonoidHom (Q.mapQ P ψ hψ).toAddMonoidHom m ?_ ?_ p hp hpm
  · intro a
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      simp only [LinearMap.toAddMonoidHom_coe, Submodule.mapQ_apply, h1]
      rfl
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      simp only [LinearMap.toAddMonoidHom_coe, Submodule.mapQ_apply, h2]
      rfl

/-- Reduction modulo `d i` in each coordinate. -/
def redMod {ι : Type*} (d : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] ((i : ι) → ZMod (d i)) where
  toFun v i := (v i : ZMod (d i))
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

/-- The cokernel of a diagonal map `v ↦ (i ↦ d i * v i)` is `Π i, ZMod (d i)`. -/
def diagQuotEquiv {ι : Type*} (d : ι → ℕ) (D : (ι → ℤ) →ₗ[ℤ] (ι → ℤ))
    (hD : ∀ v i, D v i = (d i : ℤ) * v i) :
    ((ι → ℤ) ⧸ LinearMap.range D) ≃ₗ[ℤ] ((i : ι) → ZMod (d i)) := by
  have hsurj : Function.Surjective (redMod d) := fun z =>
    ⟨fun i => ((z i).cast : ℤ), by funext i; simp [redMod]⟩
  have hker : LinearMap.range D = LinearMap.ker (redMod d) := by
    ext w
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨v, rfl⟩
      funext i
      simp only [redMod, LinearMap.coe_mk, AddHom.coe_mk, hD, Pi.zero_apply]
      exact (CharP.intCast_eq_zero_iff (ZMod (d i)) (d i) _).mpr (dvd_mul_right _ _)
    · intro hw
      have hdiv : ∀ i, (d i : ℤ) ∣ w i := fun i =>
        (CharP.intCast_eq_zero_iff (ZMod (d i)) (d i) _).mp (congrFun hw i)
      refine ⟨fun i => w i / d i, ?_⟩
      funext i
      rw [hD]
      exact Int.mul_ediv_cancel' (hdiv i)
  exact (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective _ hsurj)

/-- Splitting a product over a type according to a decidable predicate. -/
def piSplit {α : Type*} (P : α → Prop) [DecidablePred P] (β : α → Type*)
    [∀ a, AddCommGroup (β a)] :
    ((a : α) → β a) ≃+ ((a : {x // P x}) → β a) × ((a : {x // ¬ P x}) → β a) where
  toEquiv := Equiv.piEquivPiSubtypeProd P β
  map_add' _ _ := rfl

/-- `Sylp p (ZMod 0) = ⊥`-type statement for a product of `ZMod (d i)` with all `d i = 0`. -/
lemma sylp_pi_zmod_zero {ι : Type*} (d : ι → ℕ) (hd : ∀ i, d i = 0) {p : ℕ} (hp : p ≠ 0) :
    Sylp p ((i : ι) → ZMod (d i)) = ⊥ := by
  have key : ∀ (N : ℕ), N = 0 → ∀ (c : ℕ), c ≠ 0 → ∀ z : ZMod N, c • z = 0 → z = 0 := by
    rintro N rfl c hc z hz
    change (c : ℤ) • (z : ℤ) = 0 at hz
    rcases smul_eq_zero.mp hz with h | h
    · exact absurd (by exact_mod_cast h) hc
    · exact h
  ext y
  simp only [AddSubgroup.mem_bot]
  constructor
  · rintro ⟨k, hk⟩
    funext i
    exact key (d i) (hd i) _ (pow_ne_zero k hp) (y i) (congrFun hk i)
  · rintro rfl; exact zero_mem _

end OddParts
