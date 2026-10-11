module

public import RequestProject.MainTheorem.Group

/-!
# `C33_the_main_theorem.md`: Part M — the Main Theorem (the Dancing Sand Theorem)

Encodings (namespace `MainTheorem`):

* `ℤ_[2] = PadicInt 2`; `CubeLaplacian.K n` is the torsion of the cokernel of the Laplacian of
  `Q_n` and `CubeLaplacian.Syl2` its `2`-Sylow subgroup (C17); the isomorphisms are additive
  equivalences `≃+`, stated as `Nonempty (… ≃+ …)` (explicit `M1equiv`, `M2equiv` are also given).
* The multiplicities are C31's `FamDec.m lam n = (FamDec.L n).count lam`; the multiplicity form is
  a product over `Σ lam : Fin (n + 1), Fin (FamDec.m lam n)` (the `FamDec.m lam n` copies of the
  family `lam`), the list form a product over the positions `Fin (FamDec.L n).length`.
* The group of the family `λ` at shift `i` is `XFam λ i` of (G0).
-/

@[expose] public section

namespace MainTheorem

open Families

/-! ### (M3) -/

/-- **(M3)** of `C33_the_main_theorem.md` (Part M), first item: for `n ≥ 1`,
`FamDec.m λ n ≠ 0 → 1 ≤ λ ∧ λ ≤ n ∧ λ % 2 = n % 2`.  From C31 (M3). -/
theorem M3_support (n : ℕ) (hn : 1 ≤ n) (lam : ℕ) (h : FamDec.m lam n ≠ 0) :
    1 ≤ lam ∧ lam ≤ n ∧ lam % 2 = n % 2 :=
  FamDec.M3 n hn lam (List.count_pos_iff.1 (Nat.pos_of_ne_zero h))

/-- **(M3)** of `C33_the_main_theorem.md` (Part M), second item: for `n ≥ 1` and `λ` with
`FamDec.m λ n ≠ 0`, `(n − λ) / 2 = 0 ↔ λ = n`. -/
theorem M3_shift (n : ℕ) (hn : 1 ≤ n) (lam : ℕ) (h : FamDec.m lam n ≠ 0) :
    (n - lam) / 2 = 0 ↔ lam = n := by
  have := M3_support n hn lam h
  omega

/-- **(M3)** of `C33_the_main_theorem.md` (Part M), third item: `FamDec.m n n = 1` (C31 (L2)); the
hypothesis `1 ≤ n` is kept as in the file but is not needed. -/
theorem M3_self (n : ℕ) (hn : 1 ≤ n) : FamDec.m n n = 1 := FamDec.L2 n hn

/-- **(M3)** of `C33_the_main_theorem.md` (Part M), third item: `FamDec.m 0 n = 0` for `n ≥ 1`
(C31 (L1)). -/
theorem M3_zero (n : ℕ) (hn : 1 ≤ n) : FamDec.m 0 n = 0 := FamDec.L1 n hn

/-! ### (M1) -/

/-- Every family of the multiplicity form has `λ ≥ 1` (auxiliary for (M1) of
`C33_the_main_theorem.md`). -/
lemma one_le_of_sigma (n : ℕ) (hn : 1 ≤ n) (q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) :
    1 ≤ (q.1 : ℕ) :=
  (M3_support n hn q.1 (Nat.pos_iff_ne_zero.1 (Nat.zero_lt_of_lt q.2.2))).1

/-- **(M1)** of `C33_the_main_theorem.md` (Part M), explicit equivalence: for `n ≥ 1`,
`ℤ_[2] × Syl2 (K n) ≃+ Π_{q : Σ λ : Fin (n + 1), Fin (m λ n)} XFam q.1 ((n − q.1) / 2)`. -/
noncomputable def M1equiv (n : ℕ) (hn : 1 ≤ n) :
    ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) → XFam q.1 ((n - q.1) / 2)) :=
  (Families.T3 n).some.trans
    (AddEquiv.piCongrRight fun q => (G2equiv q.1 (one_le_of_sigma n hn q) _).toAddEquiv)

/-- **(M1)** of `C33_the_main_theorem.md` (Part M; the Dancing Sand Theorem, multiplicity form):
for every `n ≥ 1`,
`ℤ_[2] × Syl2 (K n) ≅ Π_{q : Σ λ : Fin (n + 1), Fin (FamDec.m λ n)} XFam q.1 ((n − q.1) / 2)`.
From C32 `T3` and (G2). -/
theorem M1 (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (FamDec.m lam n)) → XFam q.1 ((n - q.1) / 2))) :=
  ⟨M1equiv n hn⟩

/-! ### (M2) -/

/-- **(M2)** of `C33_the_main_theorem.md` (Part M), explicit equivalence: for `n ≥ 1`,
`ℤ_[2] × Syl2 (K n) ≃+ Π_{j : Fin (L n).length} XFam λ_j ((n − λ_j) / 2)`, `λ_j = (L n).get j`. -/
noncomputable def M2equiv (n : ℕ) (hn : 1 ≤ n) :
    ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((j : Fin (FamDec.L n).length) →
        XFam ((FamDec.L n).get j) ((n - (FamDec.L n).get j) / 2)) :=
  (Families.T2 n).some.trans
    (AddEquiv.piCongrRight fun j =>
      (G2equiv _ (FamDec.M3 n hn _ (List.get_mem _ j)).1 _).toAddEquiv)

/-- **(M2)** of `C33_the_main_theorem.md` (Part M; list form): for every `n ≥ 1`,
`ℤ_[2] × Syl2 (K n) ≅ Π_{j : Fin (L n).length} XFam ((L n).get j) ((n − (L n).get j) / 2)`.
From C32 `T2`, C31 (M3) and (G2). -/
theorem M2 (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((j : Fin (FamDec.L n).length) →
        XFam ((FamDec.L n).get j) ((n - (FamDec.L n).get j) / 2))) :=
  ⟨M2equiv n hn⟩

end MainTheorem
