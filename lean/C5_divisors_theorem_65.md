# Determinantal divisors at the prime 2, and Theorem 6.5

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §6.1 (the determinantal divisors) and §6.3 Theorem 6.5. Part A is the standard link between the 2-adic determinantal divisors of an integer matrix and the exponents of its Smith form, which the paper uses in one sentence («`d_r(M)` … is `e_1 + ⋯ + e_r`; so `r ↦ d_r` is convex with integer increments, and the increments are the exponents»). Part B is Theorem 6.5 in the abstract form in which its proof uses it. This file is self-contained, except that Part B reuses the integer antitonic fit `AntitonicFit.ifit` of piece C1 and may use `SmithBounds.lemma_6_4` of piece C2.

## Part A — 2-adic determinantal divisors

**Setting.** Let `n ≥ 0` and let `M` be an `n × n` matrix over `ℤ` with `det M ≠ 0`. For `0 ≤ r ≤ n`, an `r × r` **minor** of `M` is `det M[A, B]` for subsets `A, B ⊆ {0, …, n − 1}` of size `r`, rows and columns taken in increasing order. Define the **2-adic determinantal divisor**
  `dd_r(M) := min { v_2(det M[A, B]) : |A| = |B| = r, det M[A, B] ≠ 0 }`,
where `v_2` is the 2-adic valuation on non-zero integers (`padicValInt 2`). The set is non-empty because `det M ≠ 0` (Laplace expansion). In particular `dd_0(M) = 0` and `dd_n(M) = v_2(det M)`.

**Lemma A1 (invariance).** If `P`, `Q` are `n × n` integer matrices with `det P` and `det Q` odd, then `dd_r(P M Q) = dd_r(M)` for every `0 ≤ r ≤ n`.

*Proof.* By the Cauchy–Binet formula, every `r × r` minor of `P M Q` is an integer combination of `r × r` minors of `M`, so `dd_r(PMQ) ≥ dd_r(M)`. Let `P' := adj(P)`, `Q' := adj(Q)`; then `P' (PMQ) Q' = (det P)(det Q) M`, and the same argument gives `dd_r((det P)(det Q) M) ≥ dd_r(PMQ)`. Multiplying a matrix by an odd integer `c` multiplies each `r × r` minor by `c^r`, which does not change its 2-adic valuation, so `dd_r((det P)(det Q) M) = dd_r(M)`. ∎

**Lemma A2 (diagonal matrices).** Let `e_0 ≤ e_1 ≤ ⋯ ≤ e_{n−1}` be natural numbers and `u_0, …, u_{n−1}` odd integers, and let `D := diag(u_0 2^{e_0}, …, u_{n−1} 2^{e_{n−1}})`. Then `dd_r(D) = e_0 + ⋯ + e_{r−1}` for every `0 ≤ r ≤ n`.

*Proof.* A minor `det D[A, B]` is non-zero only if `A = B`, and then it is `Π_{i∈A} u_i 2^{e_i}`, of valuation `Σ_{i∈A} e_i`. The least such sum over `|A| = r` is the sum of the `r` smallest `e_i`, which are `e_0, …, e_{r−1}` because `e` is non-decreasing. ∎

**Corollary A3 (exponents are the increments).** If `P M Q = D` with `P, Q, D` as in Lemmas A1–A2, then `dd_r(M) = e_0 + ⋯ + e_{r−1}` for every `r`, and `e_r = dd_{r+1}(M) − dd_r(M)` for `0 ≤ r < n`. In particular `r ↦ dd_r(M)` is convex: `dd_{r+1} − dd_r ≤ dd_{r+2} − dd_{r+1}`.

## Part B — Theorem 6.5, abstract form

**Setting.** Let `N ≥ 0`, `x_0, …, x_{N−1}` integers, `ŷ := ifit(x)` their integer antitonic fit (piece C1, `AntitonicFit.ifit`), and, as in piece C2,
  `U(r) := Σ_{j=N−r}^{N−1} x_j`,  `Y(r) := Σ_{j=N−r}^{N−1} ŷ_j`  (`0 ≤ r ≤ N`).
Let `C` be an integer and `e_0 ≤ e_1 ≤ ⋯ ≤ e_{N−1}` integers, and put
  `d̂(r) := (e_0 + ⋯ + e_{r−1}) − r·C`  (`0 ≤ r ≤ N`).

(In the paper, `e` are the Smith exponents of `M^{(α)}(λ, i)`, `C = αK + κ(m, K)`, and `d̂(r) = d_r(M) − rC` are the normalized divisors, by Corollary A3. The hypothesis (F) below is `d̂ ≥ T ≥ Y` — Lemma 6.1 with Theorem 7.8 — and (U) is Corollary 6.3; they are assembled in a later piece.)

**Theorem B (Theorem 6.5).** Suppose
- (F) `Y(r) ≤ d̂(r)` for every `0 ≤ r ≤ N`;
- (U) `d̂(r) ≤ U(r)` for every `0 ≤ r ≤ N`;
- (M) `ŷ` is non-increasing on `{0, …, N − 1}`.

Then `d̂(r) = Y(r)` for every `0 ≤ r ≤ N`, and `e_i = C + ŷ_{N−1−i}` for every `0 ≤ i < N`.

*Proof (from the paper).* `d̂(0) = 0` and the increments `d̂(r+1) − d̂(r) = e_r − C` are non-decreasing, so `d̂` is convex; with (U), Lemma 6.4 (piece C2, `SmithBounds.lemma_6_4`) gives `d̂(r) ≤ Y(r)`, and with (F), `d̂ = Y`. Then `e_r − C = d̂(r+1) − d̂(r) = Y(r+1) − Y(r) = ŷ_{N−1−r}`. ∎

(Hypothesis (M) is the one of the paper, proved there as Lemma 7.9, a later piece. It is in fact redundant here: from `d̂ = Y` and `e` non-decreasing, `ŷ_{N−1−r} = e_r − C` is non-decreasing in `r`, so `ŷ` is non-increasing. We keep (M) as in the paper; Lean may state the theorem without it, saying so, and should also prove: **Corollary B′.** Under (F) and (U) alone, `ŷ` is non-increasing.)

## Checks before formalization

`lean/chkC5.py` (log `logs/chkC5.log`, 4 s, 50 MB): **0 failures** — Lemma A1 1 650 cases, Corollary A3 1 140, Lemma A2 3 000, Theorem B 1 039. Lemma A1 on random non-singular integer matrices of size `n ≤ 4` with random `P, Q` of odd determinant, every `r`; Corollary A3 against the Smith form computed by `sympy` (`smith_normal_form` over `ℤ`): `dd_r(M)` equals the sum of the `r` smallest 2-adic exponents; Lemma A2 on random diagonal matrices of size `n ≤ 5`; Theorem B on every non-decreasing integer sequence `e` in a window around `C + ŷ`, for random `x` of length `N ≤ 5`. Corollary B′ is checked as «(F) and (U) never hold when `ŷ` is not non-increasing». Controls, each of which must fail somewhere: Lemma A1 with `det P` even; Lemma A2 without sorting `e`; Theorem B without `e` non-decreasing. Controls fire 510, 598 and 3 132 times. (A first control, «Theorem B without (M)», could not fail, since (M) is redundant; it was replaced by the check of Corollary B′ before the first run.)
