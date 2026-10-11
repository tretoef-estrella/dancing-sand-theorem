# The arms of the even families (paper v8 §10.7, Theorem 10.22, first part; Corollary 10.21, cleanliness)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §10.7: the proof of Corollary 10.21 («Cleanliness») and the first paragraph of the proof of Theorem 10.22 («The arms are congruent»).

§10.7 proves the fold law on the even families. Both sides of an even family are glued systems of size `2` (C39 A4_even, C39b V6):
- the first side has arms `Ψ_{i+1}` and `Ψ_i`;
- the second side has arms `U := Ψ_{i+1}(Ψ_{i+1} − 2)/2` and `U' := Ψ_i(Ψ_i + 2)/2`.

C50 proved that gluing commutes with the dance when the two arms dance congruently modulo `2` (`GlueDance.PairRel`). C50b proved that two good covariant systems that are congruent modulo `2` dance congruently modulo `2` (`DanceMod2.D1`).

This piece puts the four arms into that frame:
- (P) `Ψ_i` and `Ψ_{i+1}` are covariant systems at the same positions `y = f + ⌈i/2⌉`;
- (H) for every good system `Γ`, the systems `Γ(Γ ± 2)/2` exist and are good;
- (A), (C) both pairs of arms are congruent modulo `2`;
- (E) so both pairs dance congruently modulo `2`.

The congruence of the halves (C) is proved modulo `4` in the commutative ring `RA (ZMod (2 ^ 2))` of C50b. There, with `a₁ = a₀ + 2δ`,
  `a₁(a₁ − 2) − a₀(a₀ + 2) = 4a₀δ + 4δ² − 4δ − 4a₀ = 0`.
The paper's argument (`U − U' ≡ [Ψ, Y_0] = 4[D, Y_0]`) is the same fact: the commutator lives in `4·(…)`, which the reduction modulo `4` of C50b kills.

Folder `RequestProject/ArmsEven/`, namespace `ArmsEven`. Nothing of the project is redefined.

## Setting (reused, without changing them)

- C40 `FormalOps`: `Bf`. C40b `FormalDance`: `MAgree`, `CleanStep`, `DanceRel`.
- C46 `Smith2`: `XiOpZ`.
- C47 `RingK`: `KRep`, `Kr`, `oS`, `Dn`, `covSys`, `prodFun`, `thetaSys`, `theta`, (K3_const), (K3_add), (K3_smul), (K6), (R2), (S1), (S3), (S5), (T1), (T1_mul), (T1_add), (T1_smul), (T1_one), (T2), (T3).
- C48 `Cleanliness`: `InK`, `PayA`, `CoefB`, `Good`, `G0`, (O1), (O2), `Kr_shift_add`, and the proof of (W2), (W4_strong) (the halving by (S3)).
- C48b `DanceXi`: `finOneDnEmpty`.
- C49 `FoldOdd`: `KF`, `kJ`, `PsiF`, `ShInvF`, `shInvC`, (F5), `coef_KF`, `kJ_zero`, `kJ_one`.
- C50 `GlueDance`: `PairRel`.
- C50b `DanceMod2`: `RA`, `red4`, `kap`, `Cong2`, (R1), (K1), (K2), `K2_mul`, `K2_add`, `K2_sub`, `K2_one`, `RA.four_eq_zero`, `red4_eq_zero_iff`, (D1).

Throughout, `A := ℤ_[2]`, and `Sys := Finset ℕ → ℕ → ℤ_[2] → ℤ_[2]`. Write `e∅ : Dn ∅ := ⟨∅, Finset.empty_subset _⟩`.

## Definitions (new)

- `uSys : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] := fun Δ m _ => if Δ = ∅ ∧ m = 0 then 1 else 0` (the unit system).
- `eI (i : ℕ) : ℕ := (i + 2) / 2 - (i + 1) / 2` (it is `1` for even `i`, `0` for odd `i`).
- `GPsi (e j : ℕ) : Finset ℕ → ℕ → ℤ_[2] → ℤ_[2] := fun Δ m y => if Δ = ∅ then (if m = 0 then 4 * (y + (e : ℤ_[2])) else kJ j m) else 0`.
  The operator `Ψ_j` with payment `4(y + e)`, written in positions shifted by `e` from its own.

## Part P — the positions

- **(P1)** For every `c e j : ℕ`:
  `covSys ∅ 0 (c : ℤ_[2]) (GPsi e j) e∅ e∅ = Smith2.XiOpZ 2 (c + e) (kJ j 1) (fun m _ => kJ j m)`.
- **(P2)** For every `i : ℕ`, with `c := (i + 1) / 2`:
  `covSys ∅ 0 (c : ℤ_[2]) (GPsi 0 i) e∅ e∅ = PsiF i` and `covSys ∅ 0 (c : ℤ_[2]) (GPsi (eI i) (i + 1)) e∅ e∅ = PsiF (i + 1)`.
- **(P3)** For every `e j : ℕ`: `Good (GPsi e j)`.

## Part A — the first arms

- **(A1)** For every `i : ℕ`: `Cong2 (GPsi (eI i) (i + 1)) (GPsi 0 i)`.

## Part H — the halves are good

- **(H1)** For every `Γ` with `Good Γ`, every `h : ℕ` and every `ε : ℤ_[2]` with `ε = 1 ∨ ε = -1`:
  `∃ Γ' : Sys, Good Γ' ∧ ∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y`.
- **(H2)** Under the hypotheses of (H1), if `∀ Δ m y, 2 * Γ' Δ m y = prodFun h Γ (Γ + (2 * ε) • uSys) Δ m y`, then for every `P : Finset ℕ` and `c : ℤ_[2]`:
  `(2 : ℤ_[2]) • covSys P h c Γ' = covSys P h c Γ * (covSys P h c Γ + (2 * ε) • (1 : Matrix (Dn P) (Dn P) (Bf ℤ_[2])))`.

## Part C — the halves are congruent

- **(C1)** For every `Γ₀ Γ₁ : Sys` with `InK Γ₀`, `InK Γ₁` and `Cong2 Γ₁ Γ₀`, every `h : ℕ`, and every `U U' : Sys` with
  `hU : ∀ Δ m y, 2 * U Δ m y = prodFun h Γ₁ (Γ₁ + (-2 : ℤ_[2]) • uSys) Δ m y` and
  `hU' : ∀ Δ m y, 2 * U' Δ m y = prodFun h Γ₀ (Γ₀ + (2 : ℤ_[2]) • uSys) Δ m y`:
  `Cong2 U U'`.

## Part E — the arms of an even family

- **(E1)** For every `i : ℕ`, with `c := (i + 1) / 2`, `Γ₁ := GPsi (eI i) (i + 1)` and `Γ₀ := GPsi 0 i`:
  `∃ U U' : Sys, Good U ∧ Good U' ∧ Cong2 Γ₁ Γ₀ ∧ Cong2 U U' ∧`
  `(∀ Δ m y, 2 * U Δ m y = prodFun 0 Γ₁ (Γ₁ + (-2 : ℤ_[2]) • uSys) Δ m y) ∧`
  `(∀ Δ m y, 2 * U' Δ m y = prodFun 0 Γ₀ (Γ₀ + (2 : ℤ_[2]) • uSys) Δ m y) ∧`
  `(2 : ℤ_[2]) • covSys ∅ 0 (c : ℤ_[2]) U e∅ e∅ = PsiF (i + 1) * (PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧`
  `(2 : ℤ_[2]) • covSys ∅ 0 (c : ℤ_[2]) U' e∅ e∅ = PsiF i * (PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2]))`.
- **(E2)** For every `i : ℕ` and every `ds : List Bool`, with `c`, `Γ₁`, `Γ₀` as in (E1):
  `∃ U U' : Sys, Good U ∧ Good U' ∧ Cong2 U U' ∧`
  `(2 : ℤ_[2]) • covSys ∅ 0 (c : ℤ_[2]) U e∅ e∅ = PsiF (i + 1) * (PsiF (i + 1) - (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧`
  `(2 : ℤ_[2]) • covSys ∅ 0 (c : ℤ_[2]) U' e∅ e∅ = PsiF i * (PsiF i + (2 : ℤ_[2]) • (1 : Bf ℤ_[2])) ∧`
  `(∃ Xk Yk, GlueDance.PairRel ds 1 (fun _ _ => PsiF (i + 1)) (fun _ _ => PsiF i) Xk Yk) ∧`
  `∃ Uk U'k, GlueDance.PairRel ds 1 (fun _ _ => covSys ∅ 0 (c : ℤ_[2]) U e∅ e∅) (fun _ _ => covSys ∅ 0 (c : ℤ_[2]) U' e∅ e∅) Uk U'k`.

## Proof sketch

- (P1): `Bf.ext`, `covSys_coef` with `D = D' = ∅` (`∅ ⊆ ∅`, `∅ \ ∅ = ∅`, `oS ∅ = 0`, `2 ^ 0 = 1`). At `m = 0`: `4 * (f + c + e) = 2 ^ 2 * (f + (c + e))`. At `m = 1`: `kJ j 1`. For `m ≥ 2`: `kJ j m`. Compare with the definition of `XiOpZ`.
- (P2): (P1), then C49 (F5), `PsiF j = XiOpZ 2 ((j + 1) / 2) (kJ j 1) (fun m _ => kJ j m)`. For `j = i`, `e = 0`. For `j = i + 1`, `(i + 1) / 2 + eI i = (i + 2) / 2` (`omega`).
- (P3): copy C48 (O1). At `(∅, 0)` the function `fun y => 4 * (y + e)` is in `Kr`, by `KRep` `⟨4 * e, X, 1, …⟩`, or by C47 (K3_add) of a constant and C48 O1's `2 ^ 2 * y`. The other coefficients are constants (K3_const) or `0`. `PayA`: `4 * (y + e) = 4 * (y + e)`. `CoefB`: `IsUnit (kJ j 1)` (C49 F5).
- (A1): at `Δ ≠ ∅` both are `0`. At `(∅, 0)`: `4 * (y + eI i) - 4 * y = 2 * (2 * eI i)`. At `(∅, m)`, `m ≥ 1`: `kJ (i + 1) m - kJ i m = 2 * ((-1) ^ i * shInvC m)`. This is because `KF (i + 1) - KF i = ((-1) ^ i - (-1) ^ (i + 1)) • ShInvF = (2 * (-1) ^ i) • ShInvF` (definition of `KF`; `coef` of a scalar multiple and of `ShInvF = cst shInvC`).
- (H1): as in C48 `W4_strong`, halve by C47 (S3) coefficientwise.
  - `InK (Γ + (2 ε) • uSys)` by C47 (T2), the clauses for sums, scalar multiples and the unit system.
  - `thetaSys (prodFun h Γ (Γ + (2 ε) • uSys)) = thetaSys Γ * (thetaSys Γ + thetaSys ((2 ε) • uSys))` by C47 (T3).
  - `thetaSys ((2 ε) • uSys) = 0`, because `theta` of a constant `c` is `inl (red c)` (C47 S1) and `red 2 = 0`.
  - `thetaSys Γ * thetaSys Γ = 0` by C47 (R2), whose only surviving entry is `θ(Γ ∅ 0)²`. That entry is `0` by C47 (S5), since the constant term `r.a = Γ ∅ 0 0` is even (`PayA` at `y = 0`; `KRep.eval 0 = r.a` because `X ∣ p`).
  - So every coefficient `prodFun … Δ m` has `theta = 0`. By (S3) it is `fun y => 2 * ψ y` with `ψ ∈ Kr`; choose `Γ' Δ m := ψ`.
  - `PayA Γ'`: at `(∅, 0)`, `prodFun h Γ Γ₂ ∅ 0 y = Γ ∅ 0 y * (Γ ∅ 0 y + 2 ε)`. With `Γ ∅ 0 y = 4 z` this is `8 z (2 z + ε)`, so `Γ' ∅ 0 y = 4 (z (2 z + ε))` (no `2`-torsion).
  - `CoefB Γ'`: at `(∅, 1)`, `prodFun h Γ Γ₂ ∅ 1 y = Γ ∅ 0 y * Γ ∅ 1 y + Γ ∅ 1 y * (Γ ∅ 0 (y - 2 ^ h) + 2 ε)` (only `Δ₁ = ∅`, `a ∈ {0, 1}`). It equals `2 * (2 (z η + η z') + ε η)` with `η = Γ ∅ 1 y` a unit. So `Γ' ∅ 1 y = 2(…) + ε η`, a unit, because `ε η` is a unit and `2(…)` is in the maximal ideal (`PadicInt` is local: unit plus non-unit; or `isUnit_iff` with the norm).
- (H2): C47 (T1_smul), (T1_mul), (T1_add), (T1_smul), (T1_one). `(2 : ℤ_[2]) • Γ' = prodFun h Γ (Γ + (2 ε) • uSys)` as functions, and `(2 ε) • 1 = covSys P h c ((2 ε) • uSys)`.
- (C1): in `RA (ZMod (2 ^ 2))` (C50b R1).
  - Put `a₀ := kap Γ₀`. Then `kap Γ₁ = a₀ + 2 δ` with `δ Δ m := red4 (z Δ m 0)`, `z` chosen from `Cong2 Γ₁ Γ₀`.
  - `kap (Γ + k • uSys) = kap Γ + (red4 k) • 1` (C50b K2_add; `kap (k • uSys) = red4 k • kap uSys`, and `kap uSys = 1` by C50b K2_one).
  - By C50b `K2_mul` (it needs `InK` of the second factor; `InK (Γ + k • uSys)` by C47 T2):
    `kap (prodFun h Γ₁ (Γ₁ - 2u)) - kap (prodFun h Γ₀ (Γ₀ + 2u)) = (a₀ + 2δ)(a₀ + 2δ - 2) - a₀(a₀ + 2) = 4(a₀δ + δ² - δ - a₀) = 0` (`RA.four_eq_zero`).
  - Both products are in `InK` (C47 T2), so by C50b (K1) their values at every `y` reduce modulo `4` like their values at `0`. Hence `red4 (2 * U Δ m y - 2 * U' Δ m y) = 0`, so `2 (U - U') = 4 w` (`red4_eq_zero_iff`), and `U - U' = 2 w` (no `2`-torsion in `ℤ_[2]`).
- (E1): (P3), (A1), (H1) with `ε = -1` for `Γ₁` and `ε = 1` for `Γ₀`, (C1), (H2) at `P = ∅`, `h = 0` and the entry `e∅ e∅`. Rewrite with (P2): the entry of `(2 ε) • 1` at `e∅ e∅` is `(2 ε) • (1 : Bf ℤ_[2])`, and `(-2 : ℤ_[2]) • 1 = -(2 • 1)`. The matrices on `Dn ∅` have the single index `e∅`.
- (E2): (E1), then C50b (D1) twice, with `r = 1`, `h = 0`, `P = ∅` (`∀ t ∈ ∅, t < 0` is vacuous) and `e = DanceXi.finOneDnEmpty`, as in C48b (T3).
  - First with `Γ = Γ₁`, `Γ'' = Γ₀`, `X = fun _ _ => PsiF (i + 1)`, `Y = fun _ _ => PsiF i`. The hypothesis `hX : X = fun j j' => covSys ∅ 0 c Γ₁ (e j) (e j')` holds by (P2), since `e j = e∅` for every `j : Fin 1`.
  - Then with `Γ = U`, `Γ'' = U'`.

## Checks before formalization

`chkC50c.py` (exact rationals with odd denominators; `kJ` from the definitions of C49, `dfi m = 1/(2m − 1)!!`; `prodFun` written from its Lean definition; good systems with random K-functions `a + 2 p(2y)/q(2y)`, payment `a ≡ 0 (mod 4)`, coefficient of `F` with `a` odd):
- **(P2):** `covSys ∅ 0 c` of `GPsi 0 i` and `GPsi (eI i) (i+1)` against the coefficients of `PsiF i`, `PsiF (i+1)`, for `i ≤ 11`, `m ≤ 9`, four floors (960 checks).
- **(A1):** `i ≤ 11`, `m ≤ 13`, three `y` (504 checks); `kJ i m` are `2`-adic integers (504); `kJ i 1` is odd (12).
- **(H1):** 25 random good systems, `h = 0, 1, 2`, `ε = ±1`, `Δ ⊆ {0, 1}`, `m ≤ 3`, four `y`: the product is even, and its half is constant modulo `4` in `y`, has payment `≡ 0 (mod 4)` and odd coefficient of `F` (5 100 checks). The same for the arms `GPsi` (816).
- **(C1):** 20 random good `Γ₀` with `Γ₁ = Γ₀ + 2E`, `h = 0, 1`, and the arms of `i ≤ 7`: `U − U'` is even (3 072 checks).

Result: 10 968 checks, 0 failures (`logs/chkC50c.log`; script md5 `21ba281e8f10a5ce2b701736814719f3`). Controls, four of four fire:
- the wrong shift for `Ψ_{i+1}` (`1 − eI i`) breaks (P2) (12 of 12);
- an odd payment makes the product not even (12 of 12);
- a coefficient of `F` equal to `2y + 1` (not in `𝒦`) makes the half non-constant modulo `4` (12 of 12);
- `Γ₁ = Γ₀ + E` off `(∅, 0)`, `(∅, 1)` (not congruent modulo `2`) makes `U − U'` odd somewhere (12 of 12).

The first run reported 36 failures. They were rows of a control that my script counted by mistake. Its fourth control could not fire, because the non-`𝒦` coefficient was shared by both arms. Both are fixed; the run above is the second.
