# C31 — Theorem 3.6 (the family decomposition) and Lemma 3.7

Piece C31 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §1.2 «Multiplicities», §3.3 Theorem 3.6 and its proof, Lemma 3.7). Folder `RequestProject/FamDec/`, namespace `FamDec`.

## Setting (reused, not redefined)

- C18 (`DPLattice`): `DPLattice`, `one`, `V`, `tensorV`.
- C19 (`WeylFilt`): `Hom.id`, `Hom.comp`.
- C20 (`Doubling`): `phi`, `Iso`, `Iso.trans`, `Iso.symm`, `Iso.phi`, `D3`, `OddUnits`.
- C21 (`Twist`): `C3_hyp`.
- C22 (`Lemma35`): `dsum`.
- C23 (`Tensor2`): `dsumIso`, `tensorVIso`.
- C24 (`Lemma35b`): `Iso.refl`, `dsumComm`, `dsumAssoc`, `lemma35Iso`.
- C27 (`Cocycle`): `zeroL`, `HasDeltaFilt`, `HasNablaFilt`.
- C28 (`Lift2`): `H1`, `H2`, `H3`, `OneAddTwoUnit`, `Z1`.
- C29 (`Filt`): `T`, `tpow`, `T_zero`, `T_odd`, `T_even`, `tpow_zero`, `tpow_succ`, `T1`.
- C30 (`Step36`): `A1`, `K1`, `K2`, `K3`, `K4a`–`K4e`, `dsumList`, `dsumList_nil`, `dsumList_cons` and the explicit isomorphisms behind them.

`A` is a commutative ring with `[IsDomain A] [CharZero A] [OddUnits A]`, `B` a commutative ring, `φ : A →+* B`, and the hypotheses of (A1) of C30: `H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A`, `h2 : (2 : B) = 0`. «`X ≅ Y`» is `Nonempty (Doubling.Iso X Y)` (an explicit `Iso` is also fine).

## Part M — the multiplicities (§1.2 of the paper)

The formal sums `Σ_λ c_λ [λ]` of the paper are encoded as lists of natural numbers (a symbol `[λ]` with coefficient `c` is `c` copies of `λ` in the list; the order does not matter).

**(M1)** `Vdot : ℕ → List ℕ`, by well-founded recursion, with these equations as theorems:
- `Vdot 0 = [1]`;
- `Vdot (2l + 1) = [2l + 2]`;
- `Vdot (2l + 2) = [2l + 1, 2l + 1] ++ (Vdot l).map (fun ν => 2ν + 1)`.

(The recursion is well founded: `Vdot (2l + 2)` calls `Vdot l`, and `l < 2l + 2`.)

**(M2)** `L : ℕ → List ℕ` with `L 0 = [0]` and `L (n + 1) = (L n).flatMap Vdot`; `m λ n := (L n).count λ`.

**(M3)** Support: for `n ≥ 1` every `λ ∈ L n` has `1 ≤ λ ≤ n` and `λ ≡ n (mod 2)`. Also `λ ∈ L 0 ↔ λ = 0`.

**(M4)** `L n` is a permutation of `(List.range (n + 1)).flatMap (fun λ => List.replicate (m λ n) λ)` (`List.Perm`), for every `n`.

## Part P — permutations and nested sums

**(P1)** If `L₁ ~ L₂` (`List.Perm`) then `dsumList L₁ ≅ dsumList L₂` (by induction on the permutation, with C24 `dsumComm`, `dsumAssoc` and C23 `dsumIso`).

**(P2)** For `f : ℕ → DPLattice A`, `g : ℕ → List (DPLattice A)` and `L : List ℕ`: if `f λ ≅ dsumList (g λ)` for every `λ ∈ L`, then `dsumList (L.map f) ≅ dsumList (L.flatMap g)` (from C30 (K4a), (K4b)).

## Part D — the decomposition

**(D1)** For every `λ`: `tensorV (T A λ) ≅ dsumList ((Vdot λ).map (T A))`, under the hypotheses of (A1) of C30.

*Proof.* Strong induction on `λ`.
- `λ = 0`: `tensorV (one A) ≅ V A ≅ phi (one A) = T A 1` (C30 (K1)), and `dsumList [T A 1] ≅ T A 1` (C30 (K4e)).
- `λ = 2l + 1`: `tensorV (T A (2l + 1)) = tensorV (phi (T A l)) = T A (2l + 2)` (C29 `T_odd`, `T_even`), and (K4e).
- `λ = 2l + 2`: `tensorV (T A (2l + 2)) = tensorV (tensorV (phi (T A l)))`, which by C30 (A1) (with C29 (T1) for `T A l`) is isomorphic to `dsum (dsum (phi (T A l)) (phi (T A l))) (phi (tensorV (T A l)))`. By induction (`l < 2l + 2`), `tensorV (T A l) ≅ dsumList ((Vdot l).map (T A))`; apply C20 `Iso.phi`, then C30 (K4d), and `phi (T A ν) = T A (2ν + 1)` (C29 `T_odd`). Assemble with (K4a), (K4e), C23 `dsumIso` and C24 `dsumAssoc`.

**(D2)** Theorem 3.6, list form: for every `n`, `tpow A n ≅ dsumList ((L n).map (T A))`.

*Proof.* Induction on `n`. `n = 0`: `tpow A 0 = one A = T A 0` and (K4e). Step: `tpow A (n + 1) = tensorV (tpow A n)` (C29 `tpow_succ`); C23 `tensorVIso`, C30 (K4c), then (D1) and (P2) give `dsumList ((L n).flatMap (fun λ => (Vdot λ).map (T A)))`, which is `dsumList ((L (n + 1)).map (T A))` (`List.flatMap` and `List.map` commute).

**(D3)** Theorem 3.6, multiplicity form: for every `n`,
  `tpow A n ≅ dsumList ((List.range (n + 1)).flatMap (fun λ => List.replicate (m λ n) (T A λ)))`,
i.e. `V^{⊗n} ⊗ A ≅ ⊕_{λ ≤ n} T(λ)^{m_λ(n)}`. (From (D2), (M4) and (P1).)

## Part L — Lemma 3.7

For `n ≥ 1`:
- **(L1)** `m 0 n = 0`;
- **(L2)** `m n n = 1`;
- **(L3)** `m 1 n = 2 ^ ((n − 1) / 2)` for odd `n`;
- **(L4)** `m 2 n = 2 ^ ((n − 2) / 2)` for even `n`.

*Proof (paper).* In `Vdot λ` the produced symbols are `1`, `λ + 1` for `λ` odd, `λ − 1` for `λ` even `≥ 2`, and `2ν + 1` (odd); `0` is never produced (L1). `λ + 1` is the largest element of `Vdot λ`, with count `1`, and `L n` has the single top element `n` (L2). `2` is produced only by `Vdot 1`, so `m 2 (n + 1) = m 1 n`. `1` is produced by `Vdot 0` and by the term `[2l + 1, 2l + 1]` of `Vdot 2` (`l = 0`), and by `(Vdot l).map (2·+1)` only if `0 ∈ Vdot l`, which never happens; so `m 1 (n + 1) = m 0 n + 2 m 2 n = 2 m 2 n` for `n ≥ 1`, with `m 1 1 = 1`.

## Part Z — the case of the paper

**(Z1)** (D1), (D2), (D3) for `A = ℤ_[2]`, `B = ZMod 2`, `φ = PadicInt.toZMod` (the hypotheses by C28 (Z1) and C21 `C3_hyp`, as in C30 (Z1)).

## Notes

- Nothing is cited. Part M and Part L are combinatorics on lists; Part P is reindexing; Part D assembles C29 and C30.
- Brute force (`chkC31.py`, 833 checks, 0 failures): the list rule `Vdot` against the formal-sum rule of §1.2 (`λ ≤ 300`); the characters `ch(V ⊗ T(λ)) = Σ_{μ ∈ Vdot λ} ch T(μ)` (`λ ≤ 200`, with `ch T` from the definition of `T`); `Σ_{λ ∈ L n} rank T(λ) = 2^n` and `Σ_{λ ∈ L n} ch T(λ) = (e + e^{−1})^n` (`n ≤ 22`); (M3) for `n ≤ 60`; (M4) for `n ≤ 22`; Lemma 3.7 for `n ≤ 60`. Controls: a rule `Vdot (2l+2) = [2l+1] ++ …` fails the ranks; a rule without the map `2·+1` fails the characters; `m 1 n = 2^{(n+1)/2}` fails. All three fire.
