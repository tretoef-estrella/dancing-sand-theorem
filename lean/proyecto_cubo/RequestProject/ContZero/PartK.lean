module

public import RequestProject.ContZero.Defs

/-!
# `C49b_congruence_and_the_data_at_zero.md`: Part K — congruences in `Bf ℤ_[2]`

* (K1) `Cong.refl`, `Cong.symm`, `Cong.trans`, `Cong.of_agree`, `Cong.mono`, `Cong.add`,
  `Cong.sub`, `Cong.mul`, `Cong.smul`, collected in `K1`;
* (K2) `Cong.tw00`, …, `Cong.vprime`, collected in `K2`;
* (K3) the matrix versions `MCong.refl`, …, `MCong.vsplit`, `MCong.reindex`, collected in `K3`;
* (K4) `K4`; (K5) `K5`; (K6) `K6`.
-/

@[expose] public section

noncomputable section

namespace ContZero

open FormalOps FormalDance Finset

/-! ### (K1) -/

section K1

variable {M : ℕ}

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: `Cong M` is reflexive. -/
theorem Cong.refl (M : ℕ) (x : Bf ℤ_[2]) : Cong M x x :=
  ⟨0, Agree.of_eq (by simp)⟩

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: `Cong M` is symmetric. -/
theorem Cong.symm {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M y x := by
  obtain ⟨z, hz⟩ := h
  refine ⟨-z, fun m f hf => ?_⟩
  have := hz m f hf
  simp only [Bf.coef_sub, Bf.coef_smul, Bf.coef_neg] at this ⊢
  linear_combination -this

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: `Cong M` is transitive. -/
theorem Cong.trans {x y w : Bf ℤ_[2]} (h : Cong M x y) (h' : Cong M y w) : Cong M x w := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨z', hz'⟩ := h'
  refine ⟨z + z', fun m f hf => ?_⟩
  have e1 := hz m f hf
  have e2 := hz' m f hf
  simp only [Bf.coef_sub, Bf.coef_smul, Bf.coef_add] at e1 e2 ⊢
  linear_combination e1 + e2

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: `Agree x y → Cong M x y`. -/
theorem Cong.of_agree {x y : Bf ℤ_[2]} (h : Agree x y) : Cong M x y :=
  ⟨0, fun m f hf => by
    have := h m f hf
    simp only [Bf.coef_sub, Bf.coef_smul, Bf.coef_zero, this]; ring⟩

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: `Cong M x y → M' ≤ M → Cong M' x y`. -/
theorem Cong.mono {M' : ℕ} {x y : Bf ℤ_[2]} (h : Cong M x y) (hM : M' ≤ M) : Cong M' x y := by
  obtain ⟨z, hz⟩ := h
  refine ⟨(2 : ℤ_[2]) ^ (M - M') • z, fun m f hf => ?_⟩
  have := hz m f hf
  simp only [Bf.coef_sub, Bf.coef_smul] at this ⊢
  rw [this, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hM]

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with `+`. -/
theorem Cong.add {x x' y y' : Bf ℤ_[2]} (hx : Cong M x x') (hy : Cong M y y') :
    Cong M (x + y) (x' + y') := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨z', hz'⟩ := hy
  refine ⟨z + z', fun m f hf => ?_⟩
  have e1 := hz m f hf
  have e2 := hz' m f hf
  simp only [Bf.coef_sub, Bf.coef_smul, Bf.coef_add] at e1 e2 ⊢
  linear_combination e1 + e2

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with `−`. -/
theorem Cong.sub {x x' y y' : Bf ℤ_[2]} (hx : Cong M x x') (hy : Cong M y y') :
    Cong M (x - y) (x' - y') := by
  obtain ⟨z, hz⟩ := hx
  obtain ⟨z', hz'⟩ := hy
  refine ⟨z - z', fun m f hf => ?_⟩
  have e1 := hz m f hf
  have e2 := hz' m f hf
  simp only [Bf.coef_sub, Bf.coef_smul] at e1 e2 ⊢
  linear_combination e1 - e2

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with `*`. -/
theorem Cong.mul {x x' y y' : Bf ℤ_[2]} (hx : Cong M x x') (hy : Cong M y y') :
    Cong M (x * y) (x' * y') := by
  obtain ⟨z1, h1⟩ := hx
  obtain ⟨z2, h2⟩ := hy
  refine ⟨z1 * y + x' * z2, ?_⟩
  have e := (h1.mul (Agree.refl y)).add ((Agree.refl x').mul h2)
  rw [Bf.smul_mul, Bf.mul_smul, ← smul_add] at e
  have hrw : x * y - x' * y' = (x - x') * y + x' * (y - y') := by noncomm_ring
  rw [hrw]
  exact e

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with scalars of `ℤ_[2]`. -/
theorem Cong.smul (a : ℤ_[2]) {x x' : Bf ℤ_[2]} (hx : Cong M x x') :
    Cong M (a • x) (a • x') := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨a • z, fun m f hf => ?_⟩
  have := hz m f hf
  simp only [Bf.coef_sub, Bf.coef_smul] at this ⊢
  linear_combination a * this

/-- (K1) of `C49b_congruence_and_the_data_at_zero.md`, for finite sums. -/
lemma Cong.sum {ι : Type*} (s : Finset ι) {x y : ι → Bf ℤ_[2]}
    (h : ∀ i ∈ s, Cong M (x i) (y i)) : Cong M (∑ i ∈ s, x i) (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.refl M 0
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- **(K1)** of `C49b_congruence_and_the_data_at_zero.md`: `Cong M` is reflexive, symmetric and
transitive; `Agree x y → Cong M x y`; `Cong M x y → M' ≤ M → Cong M' x y`; and if `Cong M x x'`
and `Cong M y y'` then `Cong M (x + y) (x' + y')`, `Cong M (x - y) (x' - y')`,
`Cong M (x * y) (x' * y')` and `Cong M (a • x) (a • x')` for `a : ℤ_[2]`. -/
theorem K1 (M : ℕ) :
    Equivalence (Cong M) ∧
    (∀ x y : Bf ℤ_[2], Agree x y → Cong M x y) ∧
    (∀ (M' : ℕ) (x y : Bf ℤ_[2]), Cong M x y → M' ≤ M → Cong M' x y) ∧
    (∀ x x' y y' : Bf ℤ_[2], Cong M x x' → Cong M y y' →
      Cong M (x + y) (x' + y') ∧ Cong M (x - y) (x' - y') ∧ Cong M (x * y) (x' * y') ∧
      ∀ a : ℤ_[2], Cong M (a • x) (a • x')) :=
  ⟨⟨Cong.refl M, Cong.symm, Cong.trans⟩, fun _ _ => Cong.of_agree,
    fun _ _ _ h hM => h.mono hM,
    fun _ _ _ _ hx hy => ⟨hx.add hy, hx.sub hy, hx.mul hy, fun a => hx.smul a⟩⟩

end K1

/-! ### (K2) -/

section K2

variable {M : ℕ}

/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: an additive map commuting with
scalars of `ℤ_[2]` and preserving `Agree` preserves `Cong M`. -/
lemma Cong.map {φ : Bf ℤ_[2] → Bf ℤ_[2]} (hsub : ∀ x y, φ (x - y) = φ x - φ y)
    (hsmul : ∀ (a : ℤ_[2]) x, φ (a • x) = a • φ x) (hag : ∀ x y, Agree x y → Agree (φ x) (φ y))
    {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (φ x) (φ y) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨φ z, by rw [← hsub, ← hsmul]; exact hag _ _ hz⟩

/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: `tw00` is additive. -/
lemma tw00_sub' (x y : Bf ℤ_[2]) : tw00 (x - y) = tw00 x - tw00 y := by ext q f; simp; ring
/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: `tw11` is additive. -/
lemma tw11_sub' (x y : Bf ℤ_[2]) : tw11 (x - y) = tw11 x - tw11 y := by ext q f; simp; ring
/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: `tw10` is additive. -/
lemma tw10_sub' (x y : Bf ℤ_[2]) : tw10 (x - y) = tw10 x - tw10 y := by ext q f; simp; ring
/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: `tw01` is additive. -/
lemma tw01_sub' (x y : Bf ℤ_[2]) : tw01 (x - y) = tw01 x - tw01 y := by
  ext q f; rcases q with _ | q <;> simp; ring
/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: `vplus` is additive. -/
lemma vplus_sub' (x y : Bf ℤ_[2]) : vplus (x - y) = vplus x - vplus y := by ext q f; simp
/-- Proof of (K2) of `C49b_congruence_and_the_data_at_zero.md`: `vprime` is additive. -/
lemma vprime_sub' (x y : Bf ℤ_[2]) : vprime (x - y) = vprime x - vprime y := by ext q f; simp

/-- (K2) of `C49b_congruence_and_the_data_at_zero.md`: congruence for `tw00`. -/
theorem Cong.tw00 {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (tw00 x) (tw00 y) :=
  Cong.map tw00_sub' tw00_smul (fun _ _ h => h.tw00) h
/-- (K2) of `C49b_congruence_and_the_data_at_zero.md`: congruence for `tw11`. -/
theorem Cong.tw11 {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (tw11 x) (tw11 y) :=
  Cong.map tw11_sub' tw11_smul (fun _ _ h => h.tw11) h
/-- (K2) of `C49b_congruence_and_the_data_at_zero.md`: congruence for `tw10`. -/
theorem Cong.tw10 {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (tw10 x) (tw10 y) :=
  Cong.map tw10_sub' tw10_smul (fun _ _ h => h.tw10) h
/-- (K2) of `C49b_congruence_and_the_data_at_zero.md`: congruence for `tw01`. -/
theorem Cong.tw01 {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (tw01 x) (tw01 y) :=
  Cong.map tw01_sub' tw01_smul (fun _ _ h => h.tw01) h
/-- (K2) of `C49b_congruence_and_the_data_at_zero.md`: congruence for `vplus`. -/
theorem Cong.vplus {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (vplus x) (vplus y) :=
  Cong.map vplus_sub' vplus_smul (fun _ _ h => h.vplus) h
/-- (K2) of `C49b_congruence_and_the_data_at_zero.md`: congruence for `vprime`. -/
theorem Cong.vprime {x y : Bf ℤ_[2]} (h : Cong M x y) : Cong M (vprime x) (vprime y) :=
  Cong.map vprime_sub' vprime_smul (fun _ _ h => h.vprime) h

/-- **(K2)** of `C49b_congruence_and_the_data_at_zero.md`: if `Cong M x y`, then
`Cong M (tw00 x) (tw00 y)`, and the same for `tw11`, `tw10`, `tw01`, `vplus` and `vprime`. -/
theorem K2 {x y : Bf ℤ_[2]} (h : Cong M x y) :
    Cong M (tw00 x) (tw00 y) ∧ Cong M (tw11 x) (tw11 y) ∧ Cong M (tw10 x) (tw10 y) ∧
    Cong M (tw01 x) (tw01 y) ∧ Cong M (vplus x) (vplus y) ∧ Cong M (vprime x) (vprime y) :=
  ⟨h.tw00, h.tw11, h.tw10, h.tw01, h.vplus, h.vprime⟩

end K2

/-! ### (K3) -/

section K3

variable {M : ℕ} {n : Type*}

/-- Proof of (K3) of `C49b_congruence_and_the_data_at_zero.md`: `MCong M` is entrywise `Cong M`. -/
lemma mcong_iff {G H : Matrix n n (Bf ℤ_[2])} :
    MCong M G H ↔ ∀ s s', Cong M (G s s') (H s s') := by
  constructor
  · rintro ⟨Z, hZ⟩ s s'
    exact ⟨Z s s', hZ s s'⟩
  · intro h
    choose Z hZ using h
    exact ⟨fun s s' => Z s s', fun s s' => hZ s s'⟩

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: `MCong M` is reflexive. -/
theorem MCong.refl (M : ℕ) (G : Matrix n n (Bf ℤ_[2])) : MCong M G G :=
  mcong_iff.2 fun _ _ => Cong.refl M _

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: `MCong M` is symmetric. -/
theorem MCong.symm {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) : MCong M H G :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').symm

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: `MCong M` is transitive. -/
theorem MCong.trans {G H K : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) (h' : MCong M H K) :
    MCong M G K :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').trans (mcong_iff.1 h' s s')

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: `MAgree G H → MCong M G H`. -/
theorem MCong.of_magree {G H : Matrix n n (Bf ℤ_[2])} (h : MAgree G H) : MCong M G H :=
  mcong_iff.2 fun s s' => Cong.of_agree (h s s')

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: `MCong M G H → M' ≤ M → MCong M' G H`. -/
theorem MCong.mono {M' : ℕ} {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) (hM : M' ≤ M) :
    MCong M' G H :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').mono hM

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with `+`. -/
theorem MCong.add {G G' H H' : Matrix n n (Bf ℤ_[2])} (hG : MCong M G G') (hH : MCong M H H') :
    MCong M (G + H) (G' + H') :=
  mcong_iff.2 fun s s' => (mcong_iff.1 hG s s').add (mcong_iff.1 hH s s')

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with `−`. -/
theorem MCong.sub {G G' H H' : Matrix n n (Bf ℤ_[2])} (hG : MCong M G G') (hH : MCong M H H') :
    MCong M (G - H) (G' - H') :=
  mcong_iff.2 fun s s' => (mcong_iff.1 hG s s').sub (mcong_iff.1 hH s s')

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with the matrix product. -/
theorem MCong.mul [Fintype n] {G G' H H' : Matrix n n (Bf ℤ_[2])} (hG : MCong M G G')
    (hH : MCong M H H') : MCong M (G * H) (G' * H') :=
  mcong_iff.2 fun s s' => by
    simp only [Matrix.mul_apply]
    exact Cong.sum _ fun j _ => (mcong_iff.1 hG s j).mul (mcong_iff.1 hH j s')

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: compatibility with scalars of `ℤ_[2]`. -/
theorem MCong.smul (a : ℤ_[2]) {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) :
    MCong M (a • G) (a • H) :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').smul a

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: congruence for the pivot block `twP`. -/
theorem MCong.twP {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) : MCong M (twP G) (twP H) :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').tw10
/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: congruence for the block `twC`. -/
theorem MCong.twC {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) : MCong M (twC G) (twC H) :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').tw11
/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: congruence for the block `twB`. -/
theorem MCong.twB {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) : MCong M (twB G) (twB H) :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').tw00
/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: congruence for the block `twD`. -/
theorem MCong.twD {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) : MCong M (twD G) (twD H) :=
  mcong_iff.2 fun s s' => (mcong_iff.1 h s s').tw01

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: congruence for the V-split `vsplit`. -/
theorem MCong.vsplit {G H : Matrix n n (Bf ℤ_[2])} (h : MCong M G H) :
    MCong M (vsplit G) (vsplit H) :=
  mcong_iff.2 fun q q' => by
    unfold FormalDance.vsplit
    split_ifs
    · exact mcong_iff.1 h _ _
    · exact (mcong_iff.1 h _ _).vprime
    · exact (mcong_iff.1 h _ _).vplus
    · exact Cong.refl M _

/-- (K3) of `C49b_congruence_and_the_data_at_zero.md`: congruence for reindexing along
`e : n' ≃ n`. -/
theorem MCong.reindex {n' : Type*} (e : n' ≃ n) {G H : Matrix n n (Bf ℤ_[2])}
    (h : MCong M G H) :
    MCong M (fun j j' => G (e j) (e j')) (fun j j' => H (e j) (e j')) :=
  mcong_iff.2 fun j j' => mcong_iff.1 h (e j) (e j')

/-- **(K3)** of `C49b_congruence_and_the_data_at_zero.md`: for `Fintype n` with
`DecidableEq n`, `MCong M` is reflexive, symmetric and transitive; `MAgree G H → MCong M G H`;
`MCong M G H → M' ≤ M → MCong M' G H`; it is compatible with `+`, `−`, `*` (matrix product) and
scalars of `ℤ_[2]`; if `MCong M G H` then `MCong M (twP G) (twP H)`, the same for `twC`, `twB`,
`twD`, and `MCong M (vsplit G) (vsplit H)`; and for `e : n' ≃ n`,
`MCong M G H → MCong M (fun j j' => G (e j) (e j')) (fun j j' => H (e j) (e j'))`. -/
theorem K3 (n : Type*) [Fintype n] [DecidableEq n] (M : ℕ) :
    Equivalence (MCong (n := n) M) ∧
    (∀ G H : Matrix n n (Bf ℤ_[2]), MAgree G H → MCong M G H) ∧
    (∀ (M' : ℕ) (G H : Matrix n n (Bf ℤ_[2])), MCong M G H → M' ≤ M → MCong M' G H) ∧
    (∀ G G' H H' : Matrix n n (Bf ℤ_[2]), MCong M G G' → MCong M H H' →
      MCong M (G + H) (G' + H') ∧ MCong M (G - H) (G' - H') ∧ MCong M (G * H) (G' * H')) ∧
    (∀ (a : ℤ_[2]) (G H : Matrix n n (Bf ℤ_[2])), MCong M G H → MCong M (a • G) (a • H)) ∧
    (∀ G H : Matrix n n (Bf ℤ_[2]), MCong M G H →
      MCong M (twP G) (twP H) ∧ MCong M (twC G) (twC H) ∧ MCong M (twB G) (twB H) ∧
      MCong M (twD G) (twD H) ∧ MCong M (vsplit G) (vsplit H)) ∧
    (∀ {n' : Type*} (e : n' ≃ n) (G H : Matrix n n (Bf ℤ_[2])), MCong M G H →
      MCong M (fun j j' => G (e j) (e j')) (fun j j' => H (e j) (e j'))) :=
  ⟨⟨MCong.refl M, MCong.symm, MCong.trans⟩, fun _ _ => MCong.of_magree,
    fun _ _ _ h hM => h.mono hM,
    fun _ _ _ _ hG hH => ⟨hG.add hH, hG.sub hH, hG.mul hH⟩,
    fun a _ _ h => h.smul a,
    fun _ _ h => ⟨h.twP, h.twC, h.twB, h.twD, h.vsplit⟩,
    fun e _ _ h => h.reindex e⟩

end K3

/-! ### (K4)–(K6) -/

/-- **(K4)** of `C49b_congruence_and_the_data_at_zero.md` (inverses): if `MAgree (P * Q) 1`,
`MAgree (Q * P) 1`, `MAgree (P' * Q') 1`, `MAgree (Q' * P') 1` and `MCong M P P'`, then
`MCong M Q Q'`. (Only `MAgree (Q * P) 1` and `MAgree (P' * Q') 1` are used by the proof; the
other two hypotheses of the file are kept, as written.) -/
theorem K4 {n : Type*} [Fintype n] [DecidableEq n] {M : ℕ} {P Q P' Q' : Matrix n n (Bf ℤ_[2])}
    (_h1 : MAgree (P * Q) 1) (h2 : MAgree (Q * P) 1) (h3 : MAgree (P' * Q') 1)
    (_h4 : MAgree (Q' * P') 1) (hP : MCong M P P') : MCong M Q Q' := by
  obtain ⟨Z, hZ⟩ := hP.symm
  refine ⟨Q * Z * Q', ?_⟩
  have e1 : MAgree Q (Q * (P' * Q')) := by
    have := (MAgree.refl Q).mul h3.symm
    rwa [mul_one] at this
  have e2 : MAgree Q' ((Q * P) * Q') := by
    have := h2.symm.mul (MAgree.refl Q')
    rwa [one_mul] at this
  have e3 : MAgree (Q - Q') (Q * (P' * Q') - (Q * P) * Q') := e1.sub e2
  have e4 : Q * (P' * Q') - (Q * P) * Q' = Q * (P' - P) * Q' := by noncomm_ring
  have e5 : MAgree (Q * (P' - P) * Q') (Q * ((2 : ℤ_[2]) ^ M • Z) * Q') :=
    ((MAgree.refl Q).mul hZ).mul (MAgree.refl Q')
  rw [Matrix.mul_smul, Matrix.smul_mul] at e5
  rw [e4] at e3
  exact e3.trans e5

/-- **(K5)** of `C49b_congruence_and_the_data_at_zero.md` (halving): if
`MCong (M + 1) ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H)` then `MCong M G H`. -/
theorem K5 {n : Type*} {M : ℕ} {G H : Matrix n n (Bf ℤ_[2])}
    (h : MCong (M + 1) ((2 : ℤ_[2]) • G) ((2 : ℤ_[2]) • H)) : MCong M G H := by
  obtain ⟨Z, hZ⟩ := h
  refine ⟨Z, fun s s' m f hf => ?_⟩
  have := hZ s s' m f hf
  simp only [Matrix.sub_apply, Matrix.smul_apply, Bf.coef_sub, Bf.coef_smul] at this ⊢
  have h2 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  linear_combination this

/-- **(K6)** of `C49b_congruence_and_the_data_at_zero.md` (one clean move): if `CleanStep G G'`,
`CleanStep H H'` and `MCong (M + 1) G H`, then `MCong M G' H'`. -/
theorem K6 {n : Type*} [Fintype n] [DecidableEq n] {M : ℕ} {G G' H H' : Matrix n n (Bf ℤ_[2])}
    (hG : CleanStep G G') (hH : CleanStep H H') (hGH : MCong (M + 1) G H) : MCong M G' H' := by
  obtain ⟨Q, h1, h2, h3⟩ := hG
  obtain ⟨Q', h1', h2', h3'⟩ := hH
  have hQ : MCong (M + 1) Q Q' := K4 h1 h2 h1' h2' hGH.twP
  have hD : MCong (M + 1) (twD G - twB G * Q * twC G) (twD H - twB H * Q' * twC H) :=
    hGH.twD.sub ((hGH.twB.mul hQ).mul hGH.twC)
  exact K5 (((MCong.of_magree h3).symm.trans hD).trans (MCong.of_magree h3'))

end ContZero
