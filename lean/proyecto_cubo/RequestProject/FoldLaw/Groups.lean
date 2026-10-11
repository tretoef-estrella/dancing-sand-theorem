module

public import RequestProject.BaiCounts.Layers
public import RequestProject.CubeLaplacian.Basic

/-!
# `C51_theorem_DW.md`: auxiliary facts on finite abelian groups

Auxiliary lemmas for the proofs of (DW′) and (R) of `C51_theorem_DW.md` (no new definition):

* the layers of the cyclic groups `ZMod (2 ^ e)` and of `ℤ`;
* a finite abelian `2`-group is a finite product of groups `ZMod (2 ^ e_j)` with `e_j ≥ 1`;
* for a finite abelian group `T`, `ℓ_0(T) = ℓ_0(Syl2 T)` (the odd part does not count).
-/

@[expose] public section

noncomputable section

namespace FoldLaw

open BaiCounts CubeLaplacian

/-- `ℓ_0(ℤ/2^e) = 2` for `e ≥ 1` (auxiliary for (DW′) of `C51_theorem_DW.md`). -/
lemma l0_zmod {e : ℕ} (he : 1 ≤ e) : l0 (ZMod (2 ^ e)) = 2 := by
  refine l0_of_surj (PadicInt.toZModPow (p := 2) e).toAddMonoidHom
    (ZMod.ringHom_surjective _) fun x hx => ?_
  have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) e) := hx
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
  push_cast at hx'
  exact (dvd_pow_self (2 : ℤ_[2]) (by omega)).trans hx'

/-- `ℓ_1(ℤ/2^e) = 2` for `e ≥ 2` (auxiliary for (DW′) of `C51_theorem_DW.md`). -/
lemma l1_zmod {e : ℕ} (he : 2 ≤ e) : l1 (ZMod (2 ^ e)) = 2 := by
  refine l1_of_surj (PadicInt.toZModPow (p := 2) e).toAddMonoidHom
    (ZMod.ringHom_surjective _) fun x hx => ?_
  have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) e) := hx
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
  push_cast at hx'
  exact (show (4 : ℤ_[2]) = 2 ^ 2 by norm_num) ▸ (pow_dvd_pow 2 he).trans hx'

/-- `ℓ_0(ℤ/2) = 2` (auxiliary for (DW′) of `C51_theorem_DW.md`). -/
lemma l0_zmod_two : l0 (ZMod 2) = 2 := l0_zmod (e := 1) le_rfl

/-- `ℓ_1(ℤ/2) = 1` (auxiliary for (DW′) of `C51_theorem_DW.md`). -/
lemma l1_zmod_two : l1 (ZMod 2) = 1 :=
  l1_of_two_smul _ (by decide)

/-- `ℓ_0(ℤ) = 2` (auxiliary for (R) of `C51_theorem_DW.md`). -/
lemma l0_int : l0 ℤ = 2 := by
  unfold l0
  rw [card_quot_of_surj (Int.castAddHom (ZMod 2)) ZMod.intCast_surjective _ fun x => ?_]
  · simp
  · rw [mem_twoPow, Int.coe_castAddHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, by simp [mul_comm]⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, by simp [mul_comm]⟩

/-- Structure of finite abelian `2`-groups (auxiliary for (DW′) of `C51_theorem_DW.md`): a finite
abelian group in which every element is killed by a power of `2` is a finite product of groups
`ZMod (2 ^ f i)` with every `f i ≥ 1`. -/
lemma two_group_structure (S : Type*) [AddCommGroup S] [Finite S]
    (hS : ∀ x : S, ∃ k : ℕ, (2 ^ k : ℕ) • x = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → ℕ), (∀ i, 1 ≤ f i) ∧
      Nonempty (S ≃+ ((i : ι) → ZMod (2 ^ f i))) := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' S
  let e' := e.trans (DirectSum.addEquivProd _)
  have hpow : ∀ i, ∃ f, 1 ≤ f ∧ n i = 2 ^ f := by
    intro i
    obtain ⟨k, hk⟩ := hS (e'.symm (Pi.single i 1))
    have h1 := congrArg (fun y => e' y i) hk
    simp only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.zero_apply, Pi.smul_apply,
      Pi.single_eq_same, nsmul_eq_mul, mul_one] at h1
    have h2 : ((2 ^ k : ℕ) : ZMod (n i)) = 0 := by exact_mod_cast h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    obtain ⟨f, -, hnf⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    refine ⟨f, ?_, hnf⟩
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := hn i; simp at hnf; omega
    · exact h
  choose f hf1 hf using hpow
  exact ⟨ι, hι, f, hf1, ⟨e'.trans (AddEquiv.piCongrRight fun i =>
    (ZMod.ringEquivCongr (hf i)).toAddEquiv)⟩⟩

/-- Bézout for `2 ^ K` and an odd `m` (auxiliary for (R) of `C51_theorem_DW.md`). -/
lemma bezout_two_pow {m : ℕ} (hm : Odd m) (K : ℕ) : ∃ u v : ℤ, u * 2 ^ K + v * m = 1 := by
  have h2 : IsCoprime (2 : ℤ) (m : ℤ) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Nat.isCoprime_iff_coprime]
    exact Nat.coprime_two_left.2 hm
  exact h2.pow_left

/-- For a finite abelian group `T`, `ℓ_0(Syl2 T) = ℓ_0(T)`: the odd part of `T` does not count
(auxiliary for (R) of `C51_theorem_DW.md`). -/
lemma l0_syl2 (T : Type*) [AddCommGroup T] [Finite T] : l0 (Syl2 T) = l0 T := by
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card T) Nat.card_pos.ne'
  have hNx : ∀ x : T, (Nat.card T : ℤ) • x = 0 := fun x => by
    rw [natCast_zsmul, card_nsmul_eq_zero']
  have hsyl : ∀ K : ℕ, a ≤ K → ∀ (v : ℤ) (z : T), (v * m) • z ∈ Syl2 T := fun K hK v z => by
    refine ⟨K, ?_⟩
    rw [← natCast_zsmul, smul_smul]
    have : ((2 ^ K : ℕ) : ℤ) * (v * m) = (2 ^ (K - a) * v) * (Nat.card T : ℤ) := by
      rw [hN, show K = (K - a) + a by omega, pow_add]; push_cast
      rw [show K - a + a - a = K - a by omega]; ring
    rw [this, mul_smul, hNx, smul_zero]
  have hsplit : ∀ (K : ℕ) (u v : ℤ), u * 2 ^ K + v * m = 1 → ∀ x : T,
      x = (u * 2 ^ K) • x + (v * m) • x := fun K u v h x => by
    rw [← add_smul, h, one_smul]
  let φ : Syl2 T →+ T ⧸ twoPow T 1 := (QuotientAddGroup.mk' _).comp (Syl2 T).subtype
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    obtain ⟨u, v, huv⟩ := bezout_two_pow hm (a + 1)
    refine ⟨⟨(v * m) • x, hsyl (a + 1) (by omega) v x⟩, ?_⟩
    simp only [φ, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq]
    refine ⟨(u * 2 ^ a) • x, ?_⟩
    have h1 : (2 ^ 1 : ℕ) • ((u * 2 ^ a) • x) = (u * 2 ^ (a + 1)) • x := by
      rw [← natCast_zsmul, smul_smul]; congr 1; push_cast; ring
    rw [h1, eq_neg_add_iff_add_eq, add_comm]
    exact (hsplit (a + 1) u v huv x).symm
  refine card_quot_of_surj φ hφ _ fun y => ?_
  simp only [φ, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, mem_twoPow]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.1, by rw [← hz]; rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨k, hk⟩ := y.2
    obtain ⟨u, v, huv⟩ := bezout_two_pow hm (k + a + 1)
    refine ⟨⟨(v * m) • z, hsyl (k + a + 1) (by omega) v z⟩, Subtype.ext ?_⟩
    have h0 : (u * 2 ^ (k + a + 1)) • (y : T) = 0 := by
      rw [show u * 2 ^ (k + a + 1) = (u * 2 ^ (a + 1)) * ((2 ^ k : ℕ) : ℤ) by push_cast; ring,
        mul_smul, natCast_zsmul, hk, smul_zero]
    have h1 : (2 ^ 1 : ℕ) • ((v * m) • z) = (v * m) • (y : T) := by
      rw [← hz, smul_comm]
    show (2 ^ 1 : ℕ) • ((v * m) • z) = (y : T)
    rw [h1]
    conv_rhs => rw [hsplit (k + a + 1) u v huv (y : T), h0, zero_add]

end FoldLaw
