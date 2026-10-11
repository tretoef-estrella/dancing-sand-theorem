# C32 — Theorem 3.8 (the groups of the families)

Piece C32 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §3.4 Theorem 3.8, the first paragraph of the proof of Proposition 4.3 in §4.3, and §2.1–§2.2 Corollary 2.3). Folder `RequestProject/Families/`, namespace `Families`.

The piece joins the two halves already formalized: the lattices `T(λ)` of C29–C31 (where the operator of the cube lives) and the tower `T(ds)` of C13 (where the dance and the Smith form of C13–C16 live). The paper passes from one to the other in one sentence of the proof of Proposition 4.3 («the floor grading of `T(λ)` is the grading of Propositions 4.1–4.2»); here that sentence becomes an explicit isomorphism.

## Setting (reused, not redefined)

- C11 (`Payment`): `Sys`, `slotLof`, `slotEmb`, `G`, `NΦ`, `flΦ`, `embΦ`, `FΦ`.
- C12 (`Split`): `NVΦ`, `flVΦ`, `embVΦ`, `FVΦ`, `NΨ`, `flΨ`, `embΨ`, `FΨ`, `theta`, `thetaInv` and their properties.
- C13 (`Dance`): `Idx`, `fl`, `F`, `SysT`, `pσ`, `κσ`, `sigma`.
- C14 (`Windows`): `Ids`.
- C16 (`FamilyGroup`): `X` (the group of the tower over `ℤ_[2]`).
- C17 (`CubeLaplacian`): `G`, `lap`, `K`, `Syl2`, (D2).
- C18 (`DPLattice`): `DPLattice`, `Hom`, `H`, `one`, `V`, `tensorV`, `tensorPow`, `C1`, `C1equiv`, `C2`.
- C20 (`Doubling`): `phi`, `phi_data`, `Iso`, `OddUnits`.
- C21 (`Twist`): `C3_hyp`.
- C22 (`Lemma35`): `dsum`.
- C28 (`Lift2`): `H1`, `H2`, `H3`, `OneAddTwoUnit`, `Z1`.
- C29 (`Filt`): `T`, `T_zero`, `T_odd`, `T_even`, `tpow`, `tpow_zero`, `tpow_succ`.
- C30 (`Step36`): `dsumList`, `dsumList_nil`, `dsumList_cons`.
- C31 (`FamDec`): `Vdot`, `L`, `m`, `M3`, `M4`, `D2`, `D3`, `Z1`.

`A` is a commutative ring with `[IsDomain A] [CharZero A] [OddUnits A]` (the context of C29 `T`). «`X ≅ Y`» is `Nonempty (… ≃ₗ[A] …)` or `Nonempty (… ≃+ …)` as written; an explicit equivalence is also fine.

## Part B0 — the digit list of a family

**(B0)** `ds : ℕ → List Bool`, by well-founded recursion, with these equations as theorems:
- `ds 0 = []`;
- `ds (2l + 1) = false :: ds l`;
- `ds (2l + 2) = true :: ds l`.

**(B0b)** For every `λ`: `λ + 1 = 2 ^ (ds λ).length + Σ_{t ∈ Windows.Ids (ds λ)} 2 ^ t`. (So `k = (ds λ).length` and `I = Ids (ds λ)` are the `k` and `I` of the paper: `λ + 1 = 2^k + Σ_{t∈I} 2^t`.)

## Part B1 — the lattice `T(λ)` is the tower `T(ds λ)`

**(B1)** For every `λ` there is an `A`-linear equivalence
  `Θ λ : ((T A λ).ι → A) ≃ₗ[A] (⨁ _ : Dance.Idx (ds λ), A)`
such that
- (a) `Θ λ ∘ₗ (T A λ).Fd 1 = Dance.F A (ds λ) ∘ₗ Θ λ`;
- (b) (weights become floors) for every basis index `j` of `T A λ` and every `q : Dance.Idx (ds λ)`: if `2 * (Dance.fl (ds λ) q : ℤ) + (T A λ).wt j ≠ λ` then `Θ λ (Pi.single j 1) q = 0`.

*Sketch.* Strong induction on `λ`, following the recursion of `T` and `ds`.
- `λ = 0`: `T A 0 = one A` (one basis vector of weight `0`) and `Idx [] = Unit` with floor `0`, `F A [] = 0`, `(one A).Fd 1 = 0`.
- `λ = 2l + 1`: `T A λ = phi (T A l)`, basis `Fin 2 × (T A l).ι` (C20 `phi_data`), with `Fd 1 (b_0 n) = b_1 n`, `Fd 1 (b_1 n) = 2 b_0 (Fd 1 n)`; the tower is `Idx (ds l) × Fin 2` with `FΦ` (C11). Send `b_e n` to `Θ l n` placed with `e` (`embΦ e`). Weights: `wt(b_e n) = 2 wt(n) + (1 if e = 0 else −1)`, floor `2 fl + e`; `2(2 fl + e) + 2 wt + (1 − 2e) = 2(2 fl + wt) + 1 = 2l + 1`.
- `λ = 2l + 2`: `T A λ = tensorV (phi (T A l))`, basis `Fin 2 × (Fin 2 × (T A l).ι)`, with `Fd 1 = F_V ⊗ 1 + 1 ⊗ F^Φ`; this is C12's tensor model `NVΦ` with `FVΦ` after sending `b_a ⊗ b_e n` to `Θ l n` placed at `(·, a, e)`. Then compose with C12's change of basis `theta` (`A_n = b_0 b_0 n`, `B_n = b_0 b_1 n − b_1 b_0 n`, `C_n = b_1 b_0 n`, `Dd_n = b_1 b_1 n`), which carries `FVΦ` to `FΨ` (C12, Part A) and the floor `flVΦ` to `flΨ`.

## Part B2 — the group of a family is the group of its tower

For `α ≥ 1`, `i : ℕ`, the operator `σ^{(α)}_i = F + 2^α (D + i)` of §3.4 on `T(λ)` is, since `2D = λ − H` on `T(λ)`,
  `sigL A λ α i := (T A λ).Fd 1 + (2 ^ (α − 1) : A) • (((λ : A) + 2 * i) • LinearMap.id − H (T A λ))`.

**(B2)** For every `λ`, `α ≥ 1` and `i`:
  `((T A λ).ι → A) ⧸ LinearMap.range (sigL A λ α i) ≃ₗ[A] Dance.SysT A (ds λ) (Fin 1) ⧸ LinearMap.range (Dance.sigma A (ds λ) α i)`.

(From (B1): `SysT A ds (Fin 1) = ⨁ q : Fin 1 × Idx ds, A` is `⨁ _ : Idx ds, A`, and `Dance.sigma A ds α i = G (fl ds) (F A ds) (pσ α i) κσ` adds `2 · 2^{α−1}(i + fl q)` on the coordinate `q`, which is `2^{α−1}(λ + 2i − wt)` by (B1)(b).)

**(B2Z)** For `A = ℤ_[2]`: `((T ℤ_[2] λ).ι → ℤ_[2]) ⧸ LinearMap.range (sigL ℤ_[2] λ α i) ≃ₗ[ℤ_[2]] FamilyGroup.X (ds λ) α i`.

## Part Q — from Theorem 3.6 to the product of cokernels

**(Q0)** For every `n`: `tpow A n = DPLattice.tensorPow A n`.

**(Q1)** For every list `Ls : List (DPLattice A)` there is an `A`-linear equivalence
  `((dsumList Ls).ι → A) ≃ₗ[A] ((j : Fin Ls.length) → (Ls.get j).ι → A)`
carrying `(dsumList Ls).Fd 1` to `Ls.get j`'s `Fd 1` and `H (dsumList Ls)` to `H (Ls.get j)`, componentwise (in the form of the hypotheses `hF`, `hH` of C18 `C1`).

**(Q2)** Every `Doubling.Iso X Y` gives an `A`-linear equivalence `(X.ι → A) ≃ₗ[A] (Y.ι → A)` commuting with `Fd 1` and with `H` (from the fields `comm_F`, `comm_H` of C18 `Hom`).

## Part T — Theorem 3.8

Over `A` with the hypotheses of C30 (A1) (`φ : A →+* B`, `H1 φ`, `H2 φ`, `H3 A`, `OneAddTwoUnit A`, `(2 : B) = 0`):

**(T1)** (list form) For every `n`:
  `((G n → A) ⧸ LinearMap.range (lap A n)) ≃ₗ[A] ((j : Fin (L n).length) → Dance.SysT A (ds ((L n).get j)) (Fin 1) ⧸ LinearMap.range (Dance.sigma A (ds ((L n).get j)) 1 ((n − (L n).get j) / 2)))`.

(From C31 (D2), (Q0)–(Q2), C18 `C1` with `M j = T A ((L n).get j)`, and on each summand `F + n − H = sigL A λ 1 ((n − λ)/2)`, because `n = λ + 2 · ((n − λ)/2)` by C31 (M3) (and `L 0 = [0]`); then (B2) on each factor.)

**(T2)** (Theorem 3.8 of the paper, `A = ℤ_[2]`) For every `n`:
  `ℤ_[2] × Syl2 (K n) ≃+ ((j : Fin (L n).length) → FamilyGroup.X (ds ((L n).get j)) 1 ((n − (L n).get j) / 2))`.

**(T3)** (multiplicity form) For every `n`:
  `ℤ_[2] × Syl2 (K n) ≃+ ((q : Σ lam : Fin (n + 1), Fin (m lam n)) → FamilyGroup.X (ds q.1) 1 ((n − q.1) / 2))`,
that is, `ℤ_2 ⊕ Syl_2 K(Q_n) ≅ ⊕_λ X^{(1)}(λ, (n − λ)/2)^{m_λ(n)}`. (From (T2) and C31 (M4): a permutation of the list reindexes the product.)

## Notes

- Nothing is cited. Part B1 is a reindexing plus C12's change of basis; Part T assembles C18 `C1`/`C2`, C31 and (B2).
- `(n − λ) / 2` is natural-number subtraction and division; on the support (C31 (M3)) it is exact.
- Brute force (`chkC32.py`, 2 343 checks, 0 failures), with an independent lattice model of `T(λ)` and an independent tower model, comparing 2-adic Smith forms: (B0b) for `λ ≤ 2000`; ranks and the multiset of floors `(λ − wt)/2` against the tower floors, `λ ≤ 40`; (B2) for `λ ≤ 12`, `α ∈ {1, 2, 3}`, `i ≤ 4`; Theorem 3.8 against the Smith form of the Laplacian of `Q_n`, `1 ≤ n ≤ 8`, in the list and the multiplicity forms (with exactly one infinite exponent, the `ℤ_2`). Controls: digits with `false`/`true` swapped fail (B2); shift `n − λ` instead of `(n − λ)/2` fails Theorem 3.8; a tower with `2^{α−1}` instead of `2^α` fails (B2) at `α = 2`. All three fire.
