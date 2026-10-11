# Bounds for determinantal divisors: the tropical bound, the unique least term, convexity, Theorem U

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §6.1 Lemma 6.1, the valuation argument of Corollary 6.3, §6.3 Lemma 6.4, §7.2 Theorem 7.4 (Theorem U). The statements are given here in the abstract form in which the paper's proofs use them; nothing about the hypercube is needed. This file is self-contained, except that Part C uses the antitonic fit `fit` and the integer fit `ifit` of the previous piece (`C1_antitonic_fits.md`, already formalized in this project as `AntitonicFit.fit` and `AntitonicFit.ifit`, with consequence (L) as `AntitonicFit.consequence_L`).

## Part A — Lemma 6.1 (tropical bound), abstract form

**Setting.** Let `R` be a commutative ring and `π ∈ R`. Let `M` be a square matrix over `R` indexed by a finite type `n`. Let `supp` be a relation on `n` (the **support**) such that `M a b = 0` whenever `¬ supp a b`, and let `c : n → n → ℕ` (the **costs**) with `π^{c(a,b)} ∣ M a b` for every `a, b`.

Let `A, B` be finite sets of indices with `|A| = |B| = r`, and let `M[A, B]` be the `r × r` submatrix (rows `A`, columns `B`, in any fixed order on each). An **`A→B` matching** is a bijection `β : A → B` with `supp a (β a)` for every `a ∈ A`; its cost is `Σ_{a∈A} c(a, β a)`.

**Lemma A (tropical bound).**
- (A1) If `T ∈ ℕ` satisfies `T ≤ cost(β)` for every `A→B` matching `β`, then `π^T ∣ det M[A, B]`.
- (A2) If there is no `A→B` matching, then `det M[A, B] = 0`.

*Proof.* `det M[A, B]` is a signed sum, over the bijections `β : A → B`, of `Π_{a∈A} M a (β a)`. If some arrow of `β` is outside the support, the product is `0`. Otherwise `β` is a matching and the product is divisible by `Π_a π^{c(a,β a)} = π^{cost(β)}`, hence by `π^T`. ∎

## Part B — the unique least term (the argument of Corollary 6.3)

**Lemma B (unique least term).** Let `p ≥ 2` be an integer, `s` a finite set, `t : s → ℤ`, `i₀ ∈ s` and `v ∈ ℕ`. Suppose
- `p^v ∣ t(i₀)` and `p^{v+1} ∤ t(i₀)`;
- `p^{v+1} ∣ t(i)` for every `i ∈ s`, `i ≠ i₀`.

Then `p^v ∣ Σ_{i∈s} t(i)` and `p^{v+1} ∤ Σ_{i∈s} t(i)`.

*Proof.* `Σ t = t(i₀) + Σ_{i≠i₀} t(i)`; the second sum is divisible by `p^{v+1}`. ∎

**Corollary B′ (the natural minor).** In the setting of Part A with `R = ℤ` and `π = p ≥ 2`: suppose that for every `A→B` matching `β` the product `Π_a M a (β a)` has exact `p`-adic valuation `cost(β)` (i.e. `p^{cost(β)}` divides it and `p^{cost(β)+1}` does not), and that there is exactly one matching `β₀` of least cost `T`. Then `p^T ∣ det M[A, B]` and `p^{T+1} ∤ det M[A, B]`.

*Proof.* Lemma A for the terms outside the support, and Lemma B for the signed terms of the matchings (signs `±1` do not change divisibility). ∎

## Part C — Lemma 6.4 (convexity)

**Setting.** Let `x = (x_0, …, x_{N−1})` be integers, `ŷ := ifit(x)` its integer antitonic fit (as in C1), and for `0 ≤ r ≤ N`
- `U(r) := Σ_{j=N−r}^{N−1} x_j` (the sum of the last `r` entries),
- `Y(r) := Σ_{j=N−r}^{N−1} ŷ_j`.

A function `d : {0, …, N} → ℤ` is **convex** if `d(r+1) − d(r) ≤ d(r+2) − d(r+1)` for every `r` with `r + 2 ≤ N`.

**Lemma C0.** `Y(N) = U(N)`. More generally, if `r` is such that `N − r` is the first position of a level set of `fit(x)` (or `r = 0`), then `Y(r) = U(r)`.

*Proof.* By (L) of C1 the sums of `x` and of `ŷ` agree on every level set, and the positions `N − r, …, N − 1` are then a union of level sets. ∎

**Lemma 6.4 (convexity).** Let `d : {0, …, N} → ℤ` be convex with `d(0) = 0` and `d(r) ≤ U(r)` for every `0 ≤ r ≤ N`. Then `d(r) ≤ Y(r)` for every `0 ≤ r ≤ N`.

*Proof (from the paper).* Read the positions from the end. On every level set of `fit(x)` the sums of `x` and of `ŷ` agree (C0), so `Y = U` at the two ends `r_0 < r_1 = r_0 + p` of each level set, counted from the end (`r` counts positions from the end: the level set occupies the positions `N − r_1, …, N − r_0 − 1`). Inside a level set with sum `S = pq + ρ` (`0 ≤ ρ < p`, `q = ⌊S/p⌋`), `ŷ` takes the value `q + 1` at its first `ρ` positions and `q` at its last `p − ρ` positions; so, counted from the end, `Y` increases by `q` on the first `p − ρ` steps and by `q + 1` on the last `ρ` steps. Argue by induction over the level sets from the end; assume `d(r_0) ≤ Y(r_0)`. Suppose `d(r^*) > Y(r^*)` for some `r_0 < r^* < r_1`.
- If `r^* ≤ r_0 + p − ρ`: some increment of `d` in `(r_0, r^*]` is at least `q + 1` (since `d(r^*) − d(r_0) > Y(r^*) − Y(r_0) = (r^* − r_0)q` and increments are integers), hence, by convexity, so is every later one; then `d(r_1) ≥ d(r^*) + (r_1 − r^*)(q + 1) > Y(r^*) + (r_1 − r^*)(q + 1) ≥ Y(r_1) = U(r_1)`, contradicting `d(r_1) ≤ U(r_1)`.
- If `r^* > r_0 + p − ρ`: then `d(r_1) − d(r^*) < Y(r_1) − Y(r^*) = (r_1 − r^*)(q + 1)`, so some increment of `d` in `(r^*, r_1]` is at most `q`, hence, by convexity, so is every earlier one, and `d(r^*) ≤ d(r_0) + (r^* − r_0)q ≤ Y(r_0) + (r^* − r_0)q ≤ Y(r^*)`, a contradiction. (Here `Y(r^*) − Y(r_0) ≥ (r^* − r_0)q` because every increment of `Y` inside the level set is `q` or `q + 1`.)

At the end of the level set, `d(r_1) ≤ U(r_1) = Y(r_1)`, which starts the next step. ∎

Note: the order matters. The lemma is false if, on each level set, the integer fit is replaced by `⌊S/p⌋` everywhere (the sum is then too small when `ρ > 0`), and false without convexity. (Replacing it by «floors first, ceilings last» makes `Y` larger and the lemma weaker, not false.)

## Part D — Theorem 7.4 (Theorem U), abstract form

**Setting.** Positions `0, 1, …, N−1` (in the paper: the dancers in o-order; the mirror `D ↦ I ∖ D` reverses the order, so it is `j ↦ N − 1 − j`). Let `arr` be a relation on positions (the **arrows**; in the paper `b ⊆ a`, loops included), `c(a, b) ∈ ℝ` a cost on each arrow, and `ŷ_0, …, ŷ_{N−1}` real numbers. An **`r`-matching** is a set `Rows` of `r` positions together with an injective map `β : Rows → {0, …, N−1}` such that `arr a (β a)` for every `a ∈ Rows`; its cost is `Σ_{a∈Rows} c(a, β a)`.

**Theorem 7.4 (Theorem U).** Suppose there are real functions `v` («rows») and `w` («columns») on the positions such that
- (U1) `v` and `w` are non-increasing: `v(j+1) ≤ v(j)` and `w(j+1) ≤ w(j)` for `j + 1 < N`;
- (U2) `v(j) − w(N − 1 − j) = ŷ_j` for every position `j`;
- (U3) `v(a) − w(b) ≤ c(a, b)` for every arrow `arr a b`.

Then every `r`-matching costs at least `Y(r) := Σ_{j=N−r}^{N−1} ŷ_j`.

*Proof.* Let `C := β(Rows)`, a set of `r` positions. By (U3) the cost is at least `Σ_{Rows} v − Σ_C w`. By (U1), `Σ_{Rows} v ≥ Σ_{j=N−r}^{N−1} v(j)` (the `r` smallest values of a non-increasing function are its last `r`) and `Σ_C w ≤ Σ_{j=0}^{r−1} w(j)` (its `r` largest values are its first `r`). The map `j ↦ N − 1 − j` sends `{N − r, …, N − 1}` onto `{0, …, r − 1}`, so by (U2) `Σ_{j=N−r}^{N−1} v(j) − Σ_{j=0}^{r−1} w(j) = Σ_{j=N−r}^{N−1} (v(j) − w(N − 1 − j)) = Y(r)`. ∎

**Lemma D0 (the two sum facts).** Let `f` be non-increasing on `{0, …, N−1}` and let `S` be a set of `r ≤ N` positions. Then `Σ_{j=N−r}^{N−1} f(j) ≤ Σ_{j∈S} f(j) ≤ Σ_{j=0}^{r−1} f(j)`.

## Checks before formalization

`lean/chkC2.py` (log `logs/chkC2.log`, 49 s): Lemma A on 7 127 random minors (and 1 889 with empty support), Lemma B on 20 000 random sums, Lemma 6.4 on every integer sequence of length `≤ 6` in small ranges and every admissible convex `d` (10 727 266 pairs), Theorem U on 1 087 random instances (every `r`-matching enumerated): **0 failures**. Controls, each of which must fail somewhere: `π^{T+1}` in Lemma A (fails 2 295 times), two least terms in Lemma B (20 000), Lemma 6.4 with all floors (1 582 611) and without convexity (10 319), Theorem U without (U1) for `w` (2 301).
