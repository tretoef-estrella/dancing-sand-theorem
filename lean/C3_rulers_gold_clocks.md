# Rulers, gold and clocks: the valuation identities of §5

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §5: Lemma 5.1, Propositions 5.2, 5.3, 5.4. Everything here is an identity between integers built from binary digits; no matrix appears. Proposition 5.2 is stated as the identity that turns the valuation formula of Theorem D (proved in a later piece) into the cost form; Proposition 5.4 is the same at the shift `i = 0`. This file is self-contained.

## Setting

All numbers are natural numbers unless said otherwise; differences are taken in `ℤ`.
- `s_2(x)` is the number of ones in the binary expansion of `x ≥ 0`; `v_2(x)` is the 2-adic valuation of `x ≥ 1`.
- `κ(a, b) := s_2(a) + s_2(b) − s_2(a + b)` (the number of carries in `a + b`; it is `≥ 0`).
- `φ(x) := x + v_2(x)` for `x ≥ 1`.

**A family.** Fix `k ≥ 0` and a set `I ⊆ {0, 1, …, k − 1}`. Put `K := 2^k`, and `λ + 1 := K + o_I`, where for `E ⊆ I`, `o_E := Σ_{t∈E} 2^t`. For `t ∈ I`:
- `next(t) := min{u ∈ I ∪ {k} : u > t}`;
- `h_t := next(t) − t ≥ 1`.

Put `t_1 := min I`, or `t_1 := k` if `I = ∅`. The subsets `D ⊆ I` are the **dancers**. For `E ⊆ I`, put `h(E) := Σ_{t∈E} h_t` and `G(E) := Σ_{t∈E} (h_t − 1)`.

**The deficit.** For `∅ ≠ Δ ⊆ I`, `δ(Δ) := k − |Δ| − min Δ`; `δ(∅) := 0`.

**The gold.** For `∅ ≠ Δ ⊆ I`, `γ(Δ) := Σ_{u ∈ I ∖ Δ, u > min Δ} h_u` (the gaps of `I` above `min Δ` that `Δ` skips); `γ(∅) := 0`.

**The rulers.** Fix an integer `α ≥ 1`. For `μ ≥ 0` and `E ⊆ I`:
- `R_μ(E) := Σ_{t∈E} (h_t − α 2^t) − κ(μ, o_E)`;
- `R^♯(E) := Σ_{t∈E} (h_t − α 2^t) − κ(K − 1, o_E)`.

**The clocks.** For a shift `i ≥ 0` and a dancer `D` with `(i, D) ≠ (0, ∅)`:
- `ξ_D := λ + 1 − 2 o_D` (a positive integer, Lemma 5.0);
- the **raw clock** `u_i(D) := φ(ξ_D) + κ(i + o_D − 1, ξ_D) + h(D)`.

For `i ≥ 1` put `m := i − 1` and, with `α = 1` in the rulers, `x_D := R_m(D) − R_{m+K}(I ∖ D)`. For `i = 0`, with `α = 1`, `x^♯_D := R^♯(D) − R^♯(I ∖ D)`.

## Statements

**Lemma 5.0.** For every dancer `D`, `ξ_D ≥ 1`. For `b ⊆ a ⊆ I`, `o_{a∖b} = o_a − o_b` and `K − o_{a∖b} ≥ 1`.

**Lemma 5.1.** For `Δ ⊆ I`:
- (a) `δ(Δ) = G(Δ) + γ(Δ)`;
- (b) `γ(Δ) = 0` if and only if `Δ = ∅` or `Δ = {t ∈ I : t ≥ min Δ}` (a **tail** of `I`).

*Proof.* (a) `k − min Δ = Σ_{t ∈ I, t ≥ min Δ} h_t` (the gaps telescope up to `k`). The digits `t ≥ min Δ` of `I` are those of `Δ` and those counted in `γ(Δ)`. (b) Each `h_u ≥ 1`. ∎

**Lemma (Legendre sums).** For `μ ≥ 0` and `x ≤ y`:
- `Σ_{d=x}^{y−1} v_2(μ + 1 + d) = (y − x) − s_2(μ + y) + s_2(μ + x)`;
- for `1 ≤ x ≤ y`, `Σ_{d=x}^{y−1} v_2(d) = (y − x) − s_2(y − 1) + s_2(x − 1)`.

(From Legendre's formula `v_2(z!) = z − s_2(z)`.)

**Proposition 5.2 (the cost form).** Let `b ⊆ a ⊆ I`, `Δ := a ∖ b`, `α ≥ 1`, `i ≥ 1` and `m := i − 1`. Then
  `1 − K + o_Δ + δ(Δ) + Σ_{d=o_a}^{o_b+K−1} (α + v_2(i + d)) = αK + κ(m, K) + R_m(a) − R_{m+K}(b) + γ(Δ)`.

(The left side is the valuation of the entry `M_{ab}` given by Theorem D; the sum has `K + o_b − o_a ≥ 1` terms.)

*Proof.* By the Legendre sum, with `x = o_a`, `y = o_b + K` and `o_Δ = o_a − o_b`, the left side is `1 + δ(Δ) + α(K + o_b − o_a) − s_2(m + K + o_b) + s_2(m + o_a)`. By Lemma 5.1(a), `δ(Δ) = G(a) − G(b) + γ(Δ)`. Since `κ(μ, o_E) = s_2(μ) + |E| − s_2(μ + o_E)` (the digits of `o_E` are the elements of `E`), `R_μ(E) = G(E) − α o_E + s_2(μ + o_E) − s_2(μ)`. Substituting, the difference of the two sides is `1 + αK + s_2(m) − s_2(m + K) − (αK + κ(m, K)) = 0`, because `s_2(K) = 1`. ∎

**Proposition 5.3 (the clocks).** Let `α = 1`, `i ≥ 1`, `m := i − 1`. For every dancer `D`,
  `u_i(D) = k + K + κ(m, K) + x_D`.

*Proof.* Put `E := I ∖ D`, `ξ := ξ_D = K + o_E − o_D`, and `ψ(F) := Σ_{t∈F} (h_t − 2^t)`.

*Step 1 (`i = 1`): `u_1(D) = φ(λ + 1) + 2ψ(D)`.* Let `μ := ξ − 1 = λ − 2o_D`. Since `K − 1 = o({0,…,k−1} ∖ I) + o_I`, we have `μ = o({0,…,k−1} ∖ I) + 2o_E`. Adding `2^{t+1}` (`t ∈ E`) to `o({0,…,k−1} ∖ I)` carries through the positions `t + 1, …, next(t) − 1`, which lie outside `I`, and stops at `next(t)`. That position is set neither in `o({0,…,k−1} ∖ I)` nor by any other `t`, and the stretches `[t + 1, next(t)]` of different `t` are disjoint. Hence `s_2(μ) = (k − |I|) + |E| − G(E)`. Now `φ(ξ) = ξ + v_2(ξ)` and `s_2(ξ) = s_2(μ) + 1 − v_2(ξ)`, and `κ(o_D, ξ) = |D| + s_2(ξ) − s_2(K + o_E) = |D| + s_2(ξ) − 1 − |E|`. So `u_1(D) = ξ + s_2(μ) + |D| − |E| + h(D) = K + o_I − 2o_D + k − |I| + 2|D| + G(D) − G(E)`. On the other side, `φ(λ + 1) = K + o_I + t_1` and `2ψ(D) = 2G(D) + 2|D| − 2o_D`. The difference of the two sides is `k − |I| − G(D) − G(E) − t_1 = k − t_1 − Σ_{t∈I} h_t = 0`.

*Step 2.* From `κ(a, b) = s_2(a) + s_2(b) − s_2(a + b)`, `κ(m + o_D, ξ) − κ(o_D, ξ) = κ(m, o_D + ξ) − κ(m, o_D)`, so `u_i(D) = u_1(D) + κ(m, K + o_E) − κ(m, o_D)`.

*Step 3.* `x_D = ψ(D) − κ(m, o_D) − ψ(E) + κ(m + K, o_E)`, and `κ(m, K + o_E) + κ(K, o_E) = κ(m, K) + κ(m + K, o_E)` (both sides are `s_2(m) + s_2(K) + s_2(o_E) − s_2(m + K + o_E)`), with `κ(K, o_E) = 0`. Hence `u_i(D) − k − K − κ(m, K) − x_D = φ(λ + 1) + ψ(I) − k − K`, and `ψ(I) = (k − t_1) − o_I`, so this is `0`. ∎

**Proposition 5.4 (the shift `i = 0`).**
- (a) For `E ⊆ I`, `κ(K − 1, o_E) = k − min E` if `E ≠ ∅`, and `0` if `E = ∅`.
- (b) For `∅ ≠ D ⊆ I`, `b ⊆ D`, `Δ := D ∖ b` and `α ≥ 1`: `1 − K + o_Δ + δ(Δ) + Σ_{d=o_D}^{o_b+K−1} (α + v_2(d)) = αK + R^♯(D) − R^♯(b) + γ(Δ)`.
- (c) For `α = 1` and `∅ ≠ D ⊆ I`: `u_0(D) = k + K + x^♯_D`.

*Proof.* (a) For `E ≠ ∅`, `K − 1 + o_E = K + (o_E − 1)` and `s_2(o_E − 1) = |E| − 1 + min E`, so `κ(K − 1, o_E) = k + |E| − 1 − s_2(o_E − 1) = k − min E`; for `E = ∅` both sides are `0`. (b) As in Proposition 5.2, `R^♯(E) = G(E) − α o_E + s_2(K − 1 + o_E) − k`, and, for `D ≠ ∅`, `s_2(K − 1 + o_D) = 1 + s_2(o_D − 1)`. The second Legendre sum, with `x = o_D ≥ 1` and `y = o_b + K`, gives the left side `= 1 + δ(Δ) + α(K + o_b − o_D) − s_2(K − 1 + o_b) + s_2(o_D − 1)`. With `δ(Δ) = G(D) − G(b) + γ(Δ)`, the difference of the two sides is `0`. (c) In `u_i(D)` the first argument of `κ` is `i + o_D − 1`: it is `o_D − 1` at `i = 0` and `o_D` at `i = 1`, while `ξ` is unchanged. And `κ(o_D − 1, ξ) − κ(o_D, ξ) = v_2(o_D) − v_2(o_D + ξ) = min D − min E`, where `E = I ∖ D` and `v_2(K + o_E) = min E` (with `min ∅ := k`). So `u_0(D) = u_1(D) + min D − min E = k + K + ψ(D) − ψ(E) + min D − min E`, and by (a) `x^♯_D = ψ(D) − (k − min D) − ψ(E) + (k − min E)` is the same. ∎

## Checks before formalization

`lean/chkC3.py` (log `logs/chkC3.log`): every `k ≤ 6`, every `I ⊆ {0, …, k−1}`, every pair `b ⊆ a ⊆ I`, `α ≤ 3`, `i ≤ 17`. Checked, with **0 failures**: Lemma 5.0; Lemma 5.1 (a) and (b) on 1 093 sets `Δ`; Proposition 5.2 on 278 511 cases; Proposition 5.3 on 18 581; Proposition 5.4 (a) on 1 093, (b) on 16 002 and (c) on 966. Controls, each of which must fail somewhere: Lemma 5.1(a) without the gold (fails 645 times); Proposition 5.2 with the ruler `R_m` on both sides (11 016); Proposition 5.3 without `κ(m, K)` (401).
