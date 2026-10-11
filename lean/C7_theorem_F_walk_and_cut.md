# Theorem F, first half: the walk, (Λ) and the strict (Cut) (§7.4, steps 1–3)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §7.4, Theorem 7.8, steps 1–3 of its proof. The potential `V` of Theorem 7.8 (properties (E), (M), (G), steps 4–8) is **not** part of this file; it comes in the next piece.

This file reuses, without changing them:
- piece C1 (`RequestProject/AntitonicFit/`): `AntitonicFit.fit`, `AntitonicFit.ifit`, `AntitonicFit.toR`, `AntitonicFit.concat`, `AntitonicFit.mirror`, `AntitonicFit.IsCut`, `AntitonicFit.IsStrictCut`, and Lemmas 7.2 and 7.3 there;
- piece C3 (`RequestProject/Rulers/`): `Rulers.oE`, `Rulers.ruler`;
- piece C4 (`RequestProject/GoldenMatching/`): `GoldenMatching.rank`;
- piece C6 (`RequestProject/Houses/`): `Houses.bit`, `Houses.JH`, `Houses.xH`, `Houses.typ`, `Houses.kap`, `Houses.sat`, `Houses.tau`, `Houses.d1`, and Lemmas A0, A, B, C there.

## Setting

A **house** is `H = (I, k, ℓ, α)` with `I ⊆ {0, …, k − 1}` (a `Finset ℕ`), `ℓ < 2^k`, and an integer `α ≥ 1`. Write `N := 2^{|I|}`.

**Dancers in o-order.** For `0 ≤ p < N`, the dancer at position `p` is
  `dancer_I(p) := {t ∈ I : bit_{j(t)}(p) = 1}`, where `j(t) := #{u ∈ I : u < t}` is the index of `t` in the increasing enumeration of `I`.
So the binary digits of `p` say which elements of `I` the dancer contains, the least element of `I` being digit `0`.

**The sequences of a house.** For `0 ≤ p < N`:
- `x_H(p) := Houses.xH I k ℓ α (dancer_I(p))` (the base clocks, §7.3), an integer;
- `J_H(p) := Houses.JH k ℓ (dancer_I(p))`;
- `ŷ_H := ifit_N(x_H)` (the integer fit), and `fit_N(x_H)` the real fit (of `toR x_H`).

## Part 0 — dancers

**Lemma 0.** Let `I` be any `Finset ℕ`, `N = 2^{|I|}`.
- (0a) For `p < N`, `dancer_I(p) ⊆ I`.
- (0b) For `p < q < N`, `o(dancer_I(p)) < o(dancer_I(q))` (with `o = Rulers.oE`).
- (0c) Every `D ⊆ I` is `dancer_I(p)` for exactly one `p < N`; and `GoldenMatching.rank I (dancer_I(p)) = p`.
- (0d) For `p < N`, `dancer_I(N − 1 − p) = I ∖ dancer_I(p)`.
- (0e) If `I ≠ ∅`, `c := max I`, `I' := I ∖ {c}` and `M := 2^{|I'|}` (so `N = 2M`), then for `p < M`: `dancer_I(p) = dancer_{I'}(p)` and `dancer_I(M + p) = dancer_{I'}(p) ∪ {c}`.

*Proof.* `p ↦ dancer_I(p)` sends the binary digits of `p` to elements of `I`, keeping their order, so `o(dancer_I(p))` is `p` with its digit `j` moved to position `t_j`: this is strictly increasing, and it is a bijection onto the subsets of `I`. Complementing every digit of `p < N` gives `N − 1 − p`. The element `c` is the top digit `j = |I'|`. ∎

**Lemma 0f.** For a house, `x_H` is antisymmetric on `[0, N)`: `x_H(N − 1 − p) = −x_H(p)`. And `J_H(0) = 0`, since `dancer_I(0) = ∅` and `ℓ < 2^k`.

*Proof.* (0d) and Lemma A0 of C6. ∎

## Part 1 — Theorem F1 (Theorem 7.8: (Λ) and (Cut))

**Theorem F1.** For every house `H = (I, k, ℓ, α)` (`α ≥ 1`):
- (Λ) for every `p < N`: `|ŷ_H(p)| ≤ α (2^k − 1)`;
- (Cut) if `b < N` is the first position with `J_H(b) = 1` (that is, `J_H(b) = 1` and `J_H(p) = 0` for every `p < b`), then `x_H` has a **strict cut** at `b` and a strict cut at `N − b` (in the sense of `AntitonicFit.IsStrictCut N (toR x_H)`). Note `0 < b` by Lemma 0f.

## Part 2 — Theorem F0 (the walk, step 1)

Let `H = (I, k, ℓ, α)` be a house with `I ≠ ∅`, and `c := max I`, `I' := I ∖ {c}`, `M := 2^{|I'|}`, `H' := (I', c, ℓ mod 2^c, α)` (a house). Write `x' := x_{H'}`, `J' := J_{H'}` (sequences of length `M`) and
  `d(p) := Houses.d1 I k ℓ α c (dancer_{I'}(p))` for `p < M`,
that is `d(p) = −τ − [T = 1] κ J'(p) + [T = 0] κ J'(M − 1 − p)`, with `T, κ, τ` the data of the window `[c, k)` of `H` (C6).

**Theorem F0.** For every such house:
- (W0) for `p < M`: `x_H(p) = x'(p) + d(p)`;
- (W1) `d` is non-increasing on `[0, M)`; and if `0 < p < M` and `d(p − 1) ≠ d(p)`, then `J'` is not identically zero on `[0, M)` and `p = b'` or `p = M − b'`, where `b'` is the first position with `J'(b') = 1`;
- (W2) for `p < M`: `fit_M(x' + d)(p) = fit_M(x')(p) + d(p)` and `ifit_M(x' + d)(p) = ifit_M(x')(p) + d(p)`;
- (W3) with `Z_1 := fit_M(x') + d` and `X_1 := ifit_M(x') + d` (sequences of length `M`), for every `p < N`:
  `fit_N(x_H)(p) = concat_M(max(Z_1, 0), min(mirror_M(Z_1), 0))(p)` and
  `ŷ_H(p) = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))(p)`,
  with `concat`, `mirror` as in C1 (`mirror_M(u)(j) = −u(M − 1 − j)`).

*Proof of F0 and F1 (from the paper), by induction on `|I|`.* F1 and F0 are proved together: F0 for `H` uses (Cut) for `H'`, and F1 for `H` uses F0 for `H`.

For `I = ∅` there is one dancer, `x = ŷ = 0`, (Λ) is `0 ≤ α(2^k − 1)`, and `J_H(0) = 0` so (Cut) is empty.

Let `I ≠ ∅`, with `H'` as above and F1 known for `H'`.

1. **The walk (F0).** (W0) is (C6) of C6 with (0e). The sequence `d` is integer, non-increasing, and changes only at the first dancer with `J' = 1` and at its mirror (`J'` is an up-set of the o-order by Lemma A0 of C6 and (0b); `J' ∘ mirror` is a down-set). These are strict cuts of `x'`, by (Cut) for `H'`. So, by Lemma 7.2(b) of C1 (in the form `lemma_7_2_b3_b2`), the real fit of `x' + d` is `fit(x') + d`, with the level sets of `fit(x')`, and its integer fit is `ifit(x') + d`: this is (W2). The full sequence `x_H` is antisymmetric (Lemma 0f) with first half `x' + d`, so by Lemma 7.3 of C1 (`lemma_7_3_fit`, `lemma_7_3_ifit`) we get (W3).

2. **(Λ).** `d ≤ −τ + [T = 0]κ = α2^c − h + κ ≤ α2^c`, since `κ ≤ h` (here `h := k − c`). With (Λ) for `H'`, `X_1 ≤ α(2^c − 1) + α2^c ≤ α(2^k − 1)`; so `0 ≤ max(X_1, 0) ≤ α(2^k − 1)`, and the second half follows by antisymmetry (W3).

3. **(Cut).** By Lemma C of C6 ((C3), (C4)), `J_H` on the two halves is: `[T = 1]·sat·J'` on the first and `sat·([T = 1] + [T = 0] J')` on the second. So either `J_H ≡ 0`, or one of:
   (a) `T = 1`, `sat = 1`, `J' ≢ 0`: the boundary `b` of `J_H` is the boundary `b'` of `J'` in the first half. Saturation of type `1` means `κ = h`, so `τ = −α2^c` and `d = α2^c − hJ'`. Just before `b`, `J' = 0` and `X_1 = ŷ' + α2^c ≥ α > 0` by (Λ) for `H'`; so the real fit `Z_1` of the first half is positive before `b`, and by Lemma 7.3, `fit(x_H)_{<b} = (Z_1)_{<b}`. The first half is cut at `b` (step 1), so `(Z_1)_{<b} = fit((x_H)_{<b})`, and Lemma 7.2(c) gives the cut. It is strict: on the first half `fit(x_H) = max(Z_1, 0)`, and `Z_1 = fit(x') + d` with `fit(x')` non-increasing and `d` dropping by `h ≥ 1` at `b`; so if `b^−` is the position before `b`, `Z_1(b^−) ≥ Z_1(b) + h` and `Z_1(b^−) > 0`; so `max(Z_1, 0)` drops strictly at `b`.
   (b) `T = 1`, `sat = 1`, `J' ≡ 0`: the boundary is the middle `b = M`, and `X_1(M − 1) = ŷ'(M − 1) + α2^c ≥ α > 0`; so `Z_1 > 0`, `fit(x_H)` restricted to the first half is `Z_1`, and Lemma 7.2(c) gives the cut at `M`. It is strict: `fit(x_H)` is `Z_1(M − 1) > 0` at `M − 1` and `min(mirror(Z_1)(0), 0) ≤ 0` at `M`.
   (c) `T = 0`, `sat = 1`, `J' ≢ 0`: the boundary is `b = M + b'`. Saturation of type `0` means `κ = h` and `τ = h − α2^c`. The second half of the clocks is `x' + d_2` with `d_2(p) = τ − [T = 0]κJ'(p) + [T = 1]κJ'(M − 1 − p)` (Lemma C of C6, (C2)), non-increasing and changing only at cuts of `x'`; so the second half is cut at `b'`, and its integer fit is `X_2 = ifit(x') + d_2`. Here `X_2(b') = ŷ'(b') + τ − κ = ŷ'(b') − α2^c ≤ −α < 0`, so the real fit `Z_2` of the second half is negative from `b'` on, `fit(x_H)_{≥b} = (Z_2)_{≥b'} = fit((x_H)_{≥b})`, and Lemma 7.2(c) gives the cut. It is strict: `b' > 0` (as `J'(0) = 0`), on the second half `fit(x_H) = min(Z_2, 0)` (Lemma 7.3), and `Z_2 = fit(x') + d_2` drops by at least `κ = h ≥ 1` at `b'`, where it is negative; so `min(Z_2, 0)` drops strictly at `b`.
   (d) Otherwise `sat = 0`, or `T = 0` and `J' ≡ 0`; then `J_H ≡ 0`, and there is nothing to prove.
   In each case the cut at `N − b` is strict by antisymmetry (Lemma A3 of C1: for an antisymmetric sequence, cut at `b` iff cut at `N − b`, and strict iff strict). ∎

## Checks before formalization

`lean/chkC7.py` (log `logs/chkC7.log`): exhaustive for every `k ≤ 6`, every `I ⊆ {0, …, k − 1}`, every `ℓ < 2^k`, `α ∈ {1, 2, 3}`, in exact rational arithmetic (the fit by the pool-adjacent-violators algorithm, the integer fit by C1's rule). Result (13 s, 11 MB): **0 failures** — Lemma 0 (bijection, o-order, mirror, halves) on all 127 index sets; antisymmetry, (Λ) and `J_H(0) = 0` in 16 383 houses; (Cut) strict at `b` and at `N − b` in all 8 001 houses with `J_H ≢ 0`; (W0)–(W3) in all 16 002 houses with `I ≠ ∅`. Controls, each of which must fail somewhere: (Λ) with `2^k − 2` in place of `2^k − 1` (fires 272 times); the cut moved to `b + 1` (1 911); (W3) without the `max`/`min` (1 106).
