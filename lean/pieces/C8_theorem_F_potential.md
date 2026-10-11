# Theorem F, second half: the potential `V` with (E), (M), (G) (§7.4, steps 4–8)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §7.4, Theorem 7.8, steps 4–8 of its proof. Steps 1–3 ((Λ), the strict (Cut), the walk) are already formalized in piece C7.

This file reuses, without changing them:
- piece C1 (`RequestProject/AntitonicFit/`): `AntitonicFit.ifit`, and its lemmas;
- piece C3 (`RequestProject/Rulers/`): `Rulers.oE`, `Rulers.h`, `Rulers.gamma`, `Rulers.ruler`;
- piece C4 (`RequestProject/GoldenMatching/`): `GoldenMatching.rank`;
- piece C6 (`RequestProject/Houses/`): `Houses.JH`, `Houses.RH`, `Houses.xH`, `Houses.cHatH`, `Houses.typ`, `Houses.kap`, `Houses.sat`, `Houses.tau`, `Houses.d1`, and Lemmas A0, C1–C7;
- piece C7 (`RequestProject/TheoremF/`): `TheoremF.dancer`, `TheoremF.xHseq`, `TheoremF.JHseq`, `TheoremF.dWalk`, Lemma 0 (0a–0e), Lemma 0f, Theorems F0 and F1.

## Setting

A **house** is `H = (I, k, ℓ, α)` with `I ⊆ {0, …, k − 1}`, `ℓ < 2^k` and an integer `α ≥ 1`; `N := 2^{|I|}`. Positions `p < N` index the dancers `dancer_I(p)` (C7). Write `x_H(p)`, `J_H(p)` for the C7 sequences, `ŷ_H := ifit_N(x_H)`, and for positions `p, q < N`
  `ĉ_H(p, q) := Houses.cHatH I k ℓ α (dancer_I(p)) (dancer_I(q))`, i.e. `R_H(a) − R_H(b) + γ(a ∖ b)` with `a = dancer_I(p)`, `b = dancer_I(q)`.
An **arrow** `p → q` is a pair of positions with `dancer_I(q) ⊊ dancer_I(p)`; then `q < p` (Lemma 0b of C7, since `o_b < o_a`).

A **potential** for `H` is a function `V : ℕ → ℤ` (only positions `< N` matter) with
- (E) `V(p) − V(N − 1 − p) = ŷ_H(p)` for every `p < N`;
- (M) `V(q) ≤ V(p)` whenever `p ≤ q < N` (non-increasing in o-order);
- (G) `V(p) − V(q) ≤ ĉ_H(p, q)` for every arrow `p → q`.

For the recursion: `I ≠ ∅`, `c := max I`, `I' := I ∖ {c}`, `M := 2^{|I'|}` (so `N = 2M`), `h := k − c`, `H' := (I', c, ℓ mod 2^c, α)`; `T := typ_c`, `κ := kap_c`, `τ := tau_c` (the data of the window `[c, k)` of `H`, C6); `x', J', ŷ'` the sequences of `H'`; `d := dWalk` (C7), and `X_1(p) := ŷ'(p) + d(p)` for `p < M`.

## Part 1 — the inherited potential (step 4)

Let `V'` be a potential for `H'`. Define `v'` on positions `p < M` by
  `v'(p) := V'(p) − [T = 1] κ J'(p)`,  `v'(M + p) := τ + V'(p) − [T = 0] κ J'(p)`.

**Lemma P.** For every house with `I ≠ ∅` and every potential `V'` for `H'`:
- (P1) for every arrow `p → q` in the same half (both `< M`, or both `≥ M`): `v'(p) − v'(q) + h ≤ ĉ_H(p, q)`; for every arrow `p → q` with `p ≥ M > q`: `v'(p) − v'(q) ≤ ĉ_H(p, q)`. (There is no arrow with `p < M ≤ q`.)
- (P2) for `p < M`: `v'(p) − v'(N − 1 − p) = X_1(p)`; and `v'(M + p) − v'(M − 1 − p) = −X_1(M − 1 − p)`.
- (P3) `v'` is non-increasing on `[0, M)` and on `[M, N)`.
- (P4) `v'(M) − v'(M − 1) = −X_1(M − 1)`, and `−X_1(M − 1) ≤ h − α`.

*Proof (from the paper).* By (C1), (C2) of C6 and Lemma 0e of C7, `v' = R_H + ω` with `ω(D) := (V' − R_{H'})(D ∩ I')`. For an arrow `a → b`, `v'(a) − v'(b) − R_H(a) + R_H(b) = ω(a) − ω(b)`, which is `≤ γ_{I'}((a ∖ b) ∩ I')` by (G) for `V'` (and `0` when `a ∩ I' = b ∩ I'`); then (C5) of C6 compares `γ_I` with `γ_{I'}`: `γ_I(Δ) = γ_{I'}(Δ) + h` when `c ∉ Δ ≠ ∅` (same half; `Δ ≠ ∅` since `b ⊊ a`), and `γ_I(Δ_0 ∪ {c}) = γ_{I'}(Δ_0)`. (P2) is (E) for `V'` plus the formula of `d` (C7, `dWalk_eq`). (P3): `V'` is non-increasing and `J'` is non-decreasing (C7). (P4): `v'(M) − v'(M − 1) = −X_1(M − 1)` by (P2) at `p = M − 1`; and `−X_1(M − 1) = −ŷ'(M − 1) + τ + [T = 1]κJ'(M − 1) − [T = 0]κJ'(0) ≤ α(2^c − 1) + h − α2^c = h − α`, by (Λ) for `H'` (C7), `J'(0) = 0`, `J' ≤ 1`, `κ ≤ h` and `τ = h − α2^c − [T = 1]κ`. ∎

## Part 2 — the junction and the central flat (steps 5–7)

**Lemma N (no central flat, step 6).** If `X_1(M − 1) > 0`, then `v'` is a potential for `H`.

*Proof.* By C7 (W3), `ŷ_H = concat_M(max(X_1, 0), min(mirror_M(X_1), 0))`, and `X_1` is non-increasing on `[0, M)` (**Lemma X**: `ŷ'(p) = V'(p) − V'(M − 1 − p)` by (E) for `V'`, which is non-increasing in `p` by (M) for `V'`, and `d` is non-increasing by (W1) of C7), so `X_1 > 0` on the first half and `ŷ_H = (X_1, mirror(X_1))`. (E) is (P2); (M) is (P3) plus (P4) at the junction; (G) is (P1). ∎

**Lemma F (the central flat, step 7).** If `X_1(M − 1) ≤ 0`, let `f := min {p < M : X_1(p) ≤ 0}` and `F := [f, N − 1 − f]` (positions). Then:
- (F1) `ŷ_H(p) = 0` if and only if `p ∈ F` (for `p < N`);
- (F2) `c_3 := v'(f)` is the maximum of `v'` on `[f, M)` and `c_4 := v'(N − 1 − f)` is the minimum of `v'` on `[M, N − f)`; `c_3 − c_4 = X_1(f) ≤ 0`;
- (F3) the integer interval `[lo, hi]` is non-empty, where `lo := max(c_3, v'(N − f))` and `hi := min(c_4, v'(f − 1))` if `f > 0`, and `lo := c_3`, `hi := c_4` if `f = 0`;
- (F4) for every integer `c_F` with `lo ≤ c_F ≤ hi`, the function `V := c_F` on `F`, `V := v'` elsewhere, is a potential for `H`.

*Proof (from the paper, step 7–8).* (F1): `X_1` is non-increasing, so `{X_1 ≤ 0}` is `[f, M)`, and by (W3) `ŷ_H` is `max(X_1, 0)` on the first half and the mirror on the second. (F2) by (P3) and (P2) at `f`. (F3): `c_3 ≤ c_4`; if `f > 0`, `c_3 ≤ v'(f − 1)` and `v'(N − f) ≤ c_4` by (P3), and `v'(N − f) < v'(f − 1)` because `v'(f − 1) − v'(N − f) = X_1(f − 1) > 0` (P2). (F4), step 8: (E) on `F` both sides are `c_F` and `ŷ_H = 0`; off `F` it is (P2). (M): `V` is constant on `F`, and `v'(f − 1) ≥ c_F ≥ v'(N − f)`. (G) for an arrow `p → q` with an end in `F` (here `q < p`; `F ∩ [0, M) = [f, M)` is a final segment of the first half, `F ∩ [M, N) = [M, N − f)` an initial segment of the second):
- `p ∈ F, p ≥ M`, `q < f`: `c_F ≤ c_4 ≤ v'(p)` and (P1).
- `p ∈ F, p < M`, `q < f`: `c_F ≤ c_4 ≤ v'(M) ≤ v'(M − 1) + h − α ≤ v'(p) + h − α` ((P4), (P3)), and the same-half slack of (P1): `c_F − v'(q) ≤ ĉ_H(p, q) − α`.
- `q ∈ F, q < M`, `p ≥ N − f`: `c_F ≥ c_3 ≥ v'(q)` and (P1).
- `q ∈ F, q ≥ M`, `p ≥ N − f`: `c_F ≥ c_3 ≥ v'(M − 1) ≥ v'(M) − h + α ≥ v'(q) − h + α`, and the slack: `v'(p) − c_F ≤ ĉ_H(p, q) − α`.
- both in `F`, same half: `ĉ_H(p, q) ≥ v'(p) − v'(q) + h ≥ v'(M − 1) − v'(M) + h ≥ α > 0 = V(p) − V(q)` (if both are `< M`: `v'(p) ≥ v'(M − 1)` and `v'(q) ≤ c_3 ≤ c_4 ≤ v'(M)`; if both are `≥ M`: `v'(p) ≥ c_4 ≥ c_3 ≥ v'(M − 1)` and `v'(q) ≤ v'(M)`). Both in `F`, `p ≥ M > q`: `ĉ_H(p, q) ≥ v'(p) − v'(q) ≥ c_4 − c_3 ≥ 0`.
In every case `V(p) − V(q) ≤ ĉ_H(p, q)`. ∎

## Part 3 — Theorem F (Theorem 7.8, the floor)

**Theorem F.** For every house `H = (I, k, ℓ, α)` (`I ⊆ {0, …, k − 1}`, `ℓ < 2^k`, `1 ≤ α`) there is a potential `V` for `H`: (E), (M), (G) hold.

*Proof.* Induction on `|I|`. For `I = ∅`, `V := 0` (one position, `ŷ_H = 0`, no arrows). For `I ≠ ∅`, take a potential `V'` for `H'` (a house: `I' ⊆ {0, …, c − 1}`, `ℓ mod 2^c < 2^c`), and apply Lemma N or Lemma F (with, e.g., `c_F := lo`). ∎

**Corollary F′ (the paper's form, on subsets).** For every house there is `W : Finset ℕ → ℤ` with, for `D, E, a, b ⊆ I`:
- (E) `W(D) − W(I ∖ D) = ŷ_H(rank_I(D))`;
- (M) `o_E ≤ o_F` ⟹ `W(F) ≤ W(E)`;
- (G) `b ⊊ a` ⟹ `W(a) − W(b) ≤ Houses.cHatH I k ℓ α a b`.
(`W(D) := V(rank_I(D))`, with `rank` from C4 and Lemma 0c of C7.)

## Checks before formalization

`lean/chkC8.py` (log `logs/chkC8.log`): exhaustive for every `k ≤ 6`, every `I ⊆ {0, …, k − 1}`, every `ℓ < 2^k`, `α ∈ {1, 2, 3}`, with `V` built by steps 4–7 at every level and `c_F` taken at the low end and, separately, at the high end of its interval; exact rational arithmetic for the fits. It checks (E), (M), (G) for `V`; (P1)–(P4); (F1)–(F3); and, when there is no flat, that `ŷ_H` never vanishes. Controls, each of which must fail somewhere: (P1) with slack `h + 1`; (P4) with `h − α − 1`; `c_F := lo − 1` and `c_F := hi + 1` (break (M) or (G)); (G) without the gold `γ`.
