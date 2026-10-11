# The Smith form of the dance matrix (Theorem 7.10, §6–§7.5)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §6 (Lemma 6.1, Theorem O, Corollary 6.3, Lemma 6.4, Theorem 6.5) and §7.5 (Lemma 7.9, Theorem 7.10). This piece applies the certified abstract results of pieces C2–C9 to the final matrix `M` of the dance, identified with the closed form in piece C14, and obtains its 2-adic determinantal divisors, i.e. its Smith exponents at 2.

This file reuses, without changing them:
- piece C14 (`RequestProject/Windows/`): `Windows.Ids`, `Windows.Dset`, `Windows.finalMatrix`, `Windows.theorem_D_ii`, `Windows.theorem_D_iii`, `Windows.card_Ids`;
- piece C5 (`RequestProject/Divisors/`): `Divisors.minor`, `Divisors.minorVals`, `Divisors.dd`, `Divisors.lemma_A1`, `Divisors.theorem_B_without_M`;
- piece C4 (`RequestProject/GoldenMatching/`): `GoldenMatching.cHat`, `GoldenMatching.xVal`, `GoldenMatching.U`, `GoldenMatching.Lr`, `GoldenMatching.Fr`, `GoldenMatching.corollary_D`;
- piece C2 (`RequestProject/SmithBounds/`): `SmithBounds.lemma_A1` (tropical bound), `SmithBounds.theorem_U`;
- piece C3 (`RequestProject/Rulers/`): `Rulers.oE`, `Rulers.kappa`, `Rulers.ruler`, `Rulers.proposition_5_2`, `Rulers.proposition_5_4_b`;
- pieces C1, C7, C9: `AntitonicFit.ifit`, `TheoremF.dancer`, `TheoremF.xHseq`, `CellFloor.yhatSharp`, `CellFloor.theorem_B_floor`, `CellFloor.theorem_C_floor`, `CellFloor.lemma_7_9_I1`, `CellFloor.lemma_7_9_I2`, `CellFloor.lemma_7_9_I3`;
- piece C6: `Houses.lemma_A'_cost`, `Houses.lemma_A'_clock`.

## Setting

Let `ds : List Bool` with `k := length ds ≥ 1`, `I := Windows.Ids ds`, `m := |I| = mCount ds`, `N := 2^m`, `K := 2^k`. Let `α ≥ 1` (a natural number, cast to `ℤ` where needed) and `i ∈ ℕ`. Write
  `M := Windows.finalMatrix ℤ ds α i : Matrix (Fin N) (Fin N) ℤ`
(indexed by slots, through `Fin (2 ^ mCount ds)`).

**Dancers in o-order.** `TheoremF.dancer I p := {t ∈ I : bit rank(t) of p = 1}` lists the subsets of `I` in o-order as `p = 0, …, N − 1` (piece C7, Lemma 0b–0c). The slot order of C14 reads the bits the other way round: `Windows.Dset ds s` uses bit `m − 1 − rank(t)` of `s`. So for `p < N` let `sl(p) < N` be the number whose bit `m − 1 − j` equals bit `j` of `p` (`j < m`): the bit reversal of `p` on `m` bits. Define the matrix in o-order
  `Mo p q := M (sl p) (sl q)`  (`p, q : Fin N`).

**Clocks.** For `i ≥ 1` put `μ := i − 1`, `C := α K + κ(μ, K)` (`κ = Rulers.kappa`), and
  `x j := GoldenMatching.xVal k I α μ (TheoremF.dancer I j)`  (`j ∈ ℕ`),   `ŷ := AntitonicFit.ifit N x`.
For `i = 0` put `ŷ^♯ := CellFloor.yhatSharp I k (K − 1) α` (the integer fit, on `N − 1` positions, of `j ↦ TheoremF.xHseq I k (K − 1) α (j + 1)`).

## Part P — the o-order

**(P1)** `sl` is a bijection of `{0, …, N − 1}` (an involution), and `Windows.Dset ds (sl p) = TheoremF.dancer I p` for every `p < N`.

**(P2)** For every `r`, `Divisors.dd Mo r = Divisors.dd M r`. More generally, for any `n`, any permutation `σ` of `Fin n` and any `M : Matrix (Fin n) (Fin n) ℤ`, `Divisors.dd (M.submatrix σ σ) r = Divisors.dd M r` (a simultaneous permutation of rows and columns; permutation matrices have determinant `±1`, which is odd, so this is a case of `Divisors.lemma_A1`).

*Proof.* (P1) by the definitions of `Dset`, `dancer` and `Windows.card_Ids`; reversing `m` bits twice is the identity. (P2) `M.submatrix σ σ = P M Pᵀ` with `P` the permutation matrix of `σ`, `det P = ±1`. ∎

## Part Q — the Smith form at 2 of an integer matrix

**(Q1) Existence.** For every `n` and every `A : Matrix (Fin n) (Fin n) ℤ` there are `P, Q : Matrix (Fin n) (Fin n) ℤ` with `det P`, `det Q` odd, a number `ρ ≤ n`, exponents `e : ℕ → ℕ` non-decreasing on `[0, ρ)` and odd integers `u j`, such that `P A Q` is diagonal with entries `u j · 2^{e j}` for `j < ρ` and `0` for `ρ ≤ j < n`. (Classical: the Smith normal form over `ℤ`, or the elimination with a pivot of least 2-valuation over `ℤ_{(2)}`, clearing denominators by odd integers.)

**(Q2) The divisors of a diagonal matrix with zeros.** In the situation of (Q1), `Divisors.dd A r = Σ_{j<r} e j` for every `r ≤ ρ`, and every `r × r` minor of `A` is `0` for `r > ρ` (so `det A ≠ 0 ⟺ ρ = n`).

*Proof.* (Q2) from `Divisors.lemma_A1` (invariance under `P`, `Q` with odd determinant) and the computation of `Divisors.lemma_A2`, extended to diagonal matrices with trailing zeros (a minor of a diagonal matrix is zero unless its row and column sets coincide, and then it is the product of the chosen diagonal entries). ∎

## Part S — the case `i ≥ 1` (Theorem 7.10)

**(S1) The entries.** For `i ≥ 1` and `p, q < N`:
- if `TheoremF.dancer I q ⊄ TheoremF.dancer I p`, then `Mo p q = 0`;
- if `TheoremF.dancer I q ⊆ TheoremF.dancer I p`, then `Mo p q ≠ 0` and `2^n ∣ Mo p q`, `2^{n+1} ∤ Mo p q` for the natural number `n` with
  `(n : ℤ) = C + GoldenMatching.cHat k I α μ (dancer I p) (dancer I q)`.

**(S2) The divisors (Theorem 7.10, `i ≥ 1`).** For `i ≥ 1` and every `r ≤ N`:
  `Divisors.dd M r = r · C + Σ_{j ∈ [N − r, N)} ŷ j`   (in `ℤ`),
`det M ≠ 0`, and `ŷ` is non-increasing on `[0, N)`.

**(S3) The Smith form (Theorem 7.10, `i ≥ 1`).** For `i ≥ 1` there are `P, Q` over `ℤ` with `det P`, `det Q` odd and odd integers `u j` such that `P M Q` is diagonal with entries `u j · 2^{C + ŷ(N − 1 − j)}`, `j < N`: **the Smith exponents of `M` at 2 are `C + ŷ_D`, `D ⊆ I`.**

*Proof.* (S1): by (P1) and `Windows.theorem_D_ii`, `Mo p q = 0` off the nested pairs, and on a nested pair `Windows.theorem_D_iii` (with `0 < i + o_D` since `i ≥ 1`) gives `Mo p q ≠ 0` with `v_2(Mo p q) = 1 − K + o(Δ) + δ(Δ) + Σ_{d ∈ [o_D, o_{D'} + K)} (α + v_2(i + d))`, which `Rulers.proposition_5_2` rewrites as `α K + κ(i − 1, K) + R_μ(D) − R_{μ+K}(D') + γ(Δ) = C + cHat`. Then, paper §6–§7.5:
- *Ceiling* (Corollary 6.3): by (S1), `GoldenMatching.corollary_D` applies to `M' a b := Mo (p a) (p b)` on subsets (`p a` the o-position of `a`; anything off the subsets of `I`), with `μ := i − 1`; so for every `r ≤ N` the minor with rows the last `r` dancers and columns the first `r` has 2-valuation exactly `r C + GoldenMatching.U k I α μ r` and is non-zero, and `U k I α μ r = Σ_{j ∈ [N − r, N)} x j`. Hence `dd M r ≤ r C + Σ_{[N−r, N)} x` and (case `r = N`) `det M ≠ 0`.
- *Floor* (Lemma 6.1, Theorem 7.4): every `r × r` minor of `Mo` is a signed sum over bijections inside the support `{b ⊆ a}`; each term has 2-valuation at least `r C + Σ ĉ(a, β a)` by (S1), so by `SmithBounds.lemma_A1` every minor is divisible by `2^{r C + T(r)}`, `T(r)` the least normalized cost of an `r`-matching. By Lemma 7.5 (`Houses.lemma_A'_cost`) the normalized costs are those of the penalty cell `Cell(H; P_r, P_c)`, `H = (I, k, μ mod K, α)`, `P_r = r_k(μ)`, `P_c = r_k(μ + K)`, and by `Houses.lemma_A'_clock` the clocks of that cell are `x`; `CellFloor.theorem_B_floor` gives `T(r) ≥ Σ_{[N − r, N)} ŷ`. Hence `dd M r ≥ r C + Σ_{[N−r, N)} ŷ`.
- *Monotonicity* (Lemma 7.9): `CellFloor.lemma_7_9_I1`/`lemma_7_9_I2` give that `ŷ` is non-increasing on `[0, N)`.
- *Conclusion* (Theorem 6.5): apply (Q1) to `M`; `det M ≠ 0` forces `ρ = N`, and by (Q2) `Divisors.dd M r = Σ_{j<r} e j`. So `Divisors.theorem_B_without_M` applies with `N`, `x`, `C` and `e`: its hypothesis (F) is the floor, (U) is the ceiling; it gives `dd M r = r C + Σ_{[N − r, N)} ŷ` (S2) and `e j = C + ŷ(N − 1 − j)` (S3). With (P2) the statements for `Mo` and for `M` are the same. ∎

## Part Z — the case `i = 0`

**(Z1)** For `i = 0`, `det M = 0`: the row of the slot `sl(0)` (the dancer `∅`) is zero, since every entry of that row is either off the nested pairs or carries the factor `π_0(0) = 0` (`Deficit.Mc` with `D = ∅`, `i = 0` has the factor `d = 0` in its window `[0, o_{D'} + K)`). If `I = ∅` (so `N = 1`), `M = 0`.

**(Z2) The divisors (Theorem 7.10, `i = 0`).** For `i = 0`, `I ≠ ∅` and every `r ≤ N − 1`:
  `Divisors.dd M r = r · α K + Σ_{j ∈ [N − 1 − r, N − 1)} ŷ^♯ j`,
and `ŷ^♯` is non-increasing on `[0, N − 1)`.

**(Z3) The Smith form (Theorem 7.10, `i = 0`).** For `i = 0` and `I ≠ ∅` there are `P, Q` over `ℤ` with `det P`, `det Q` odd and odd integers `u j` such that `P M Q` is diagonal with entries `u j · 2^{α K + ŷ^♯(N − 2 − j)}` for `j < N − 1` and `0` for `j = N − 1`: **the Smith exponents of `M` at 2 are `∞` (once) and `α K + ŷ^♯_D`, `D ≠ ∅`.**

*Proof.* Paper §7.5, the case `i = 0`. On nested pairs with `D ≠ ∅`, `Windows.theorem_D_iii` (now `0 < i + o_D` because `D ≠ ∅`) and `Rulers.proposition_5_4_b` give `v_2 = α K + R^♯(D) − R^♯(D') + γ(Δ)`, the normalized cost `CellFloor.costSharp` of the house `H^♯ = (I, k, K − 1, α)` (rows shifted by one: row `a` is the dancer `a + 1`). For `r ≤ N − 1` the rows `L_r` avoid `∅` and the columns `F_r` avoid `I`, so the ceiling (the minor of the last `r` rows and the first `r` columns, by Theorem O as in `GoldenMatching.corollary_D`, now with every term non-zero because no window of a row `D ≠ ∅` contains `d = 0`) and the floor (`SmithBounds.lemma_A1` with `CellFloor.theorem_C_floor`; a minor containing the zero row is `0`) hold for `r ≤ N − 1`, with the clocks `ŷ^♯` on `N − 1` positions; `CellFloor.lemma_7_9_I3` gives integrality and monotonicity of `ŷ^♯`. Then (Q1) for `M` has `ρ = N − 1` (the minor of size `N − 1` is non-zero, `det M = 0`), (Q2) gives `dd M r = Σ_{j<r} e j` for `r ≤ N − 1`, and `Divisors.theorem_B_without_M` on `N − 1` positions, with `C := α K` and the clocks of `H^♯` without the first dancer, gives (Z2) and (Z3). ∎

## Notes on the statements

- `Divisors.dd M r` is the least `padicValInt 2` of a non-zero `r × r` minor (piece C5); `(Z2)` only claims it for `r ≤ N − 1`, where non-zero minors exist.
- The hypothesis `k ≥ 1` (`1 ≤ length ds`) is used through `Windows.theorem_D_iii`. `α ≥ 1` is used by `CellFloor.theorem_B_floor` / `theorem_C_floor`.
- (Q1) is the only general fact not yet in the project; it is classical (Smith normal form). If Mathlib's Smith normal form for submodules of free modules over a PID is used to prove it, say so in a docstring.
- (S3) and (Z3) are the paper's statement «the Smith exponents of `M` at 2 are …»; (S2) and (Z2) are its determinantal form (piece C5, Corollary A3).

## Checks before formalization

`chkC15.py` (exact rationals, the dance of C13 as in `chkC14.py`; Smith exponents at 2 by elimination with a pivot of least 2-valuation; for `N ≤ 4` also every determinantal divisor by enumerating all minors), on all digit lists with `length + (number of ones) ≤ 6`, `α ∈ {1, 2, 3}`, `i ∈ {0, 1, 2, 3}`: (P1), (P2), the exponents of (S3) and (Z3), the divisors of (S2) and (Z2), `det M ≠ 0` for `i ≥ 1` and `det M = 0` for `i = 0`, and the monotonicity of the fits hold with 0 failures. Controls that must fail, and do: `κ(i, K)` in place of `κ(i − 1, K)`; the natural clocks `x` in place of the pooled `ŷ`; the clocks of `i = 1` in place of `ŷ^♯` at `i = 0`.
