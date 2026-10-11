# Houses, windows and penalties (§7.3: Lemmas 7.5, 7.6, 7.7)

Source: *The Dancing Sand Theorem* (R. Amichis Luengo, 2026, DOI 10.5281/zenodo.23188299), §7.3. Everything here is an identity between integers built from binary digits; no matrix appears. The file reuses definitions already formalized in this project (piece C3, `RequestProject/Rulers/`): `Rulers.oE`, `Rulers.kappa`, `Rulers.next`, `Rulers.h`, `Rulers.gamma`, `Rulers.ruler`; and piece C4's `GoldenMatching.cHat` appears in Lemma A′. Results of C3 (for instance its Lemma 5.1, or the carry facts it proves) may be used.

## Setting

All numbers are natural numbers unless said otherwise; differences are taken in `ℤ`. For `x ≥ 0` and `u ≥ 0`, `bit_u(x) := ⌊x / 2^u⌋ mod 2`.

A **house** is `H = (I, k, ℓ, α)` with `k ≥ 0`, `I ⊆ {0, …, k − 1}`, `0 ≤ ℓ < 2^k` and an integer `α` (the paper has `α ≥ 1`; nothing below needs it). Put `K := 2^k`. For `E ⊆ I`, `o_E := Σ_{t∈E} 2^t` (`Rulers.oE`), and `h_t`, `next(t)`, `γ` are those of C3 for `(k, I)`.

- **Base ruler.** `R_H(E) := Σ_{t∈E} (h_t − α 2^t) − κ(ℓ, o_E)`; this is `Rulers.ruler k I α ℓ E`.
- **Carry-out set.** `J_H(E) := 1` if `ℓ + o_E ≥ 2^k`, else `0`.
- **Base clocks.** `x_H(D) := R_H(D) − R_H(I ∖ D)`.
- **Base costs.** `ĉ_H(a, b) := R_H(a) − R_H(b) + γ(a ∖ b)`.
- For `μ ≥ 0`, `r_k(μ) := v_2(⌊μ / 2^k⌋ + 1)`: the number of consecutive ones of `μ` starting at bit `k`.

## Part A — the house and its penalties (Lemma 7.5)

**Lemma A0.** For `D ⊆ I`: `x_H(I ∖ D) = −x_H(D)` (antisymmetry). For `E, F ⊆ I` with `o_E ≤ o_F`: `J_H(E) ≤ J_H(F)` (`J_H` is an up-set of the o-order).

**Lemma A (Lemma 7.5).** For every `μ ≥ 0`, with `ℓ := μ mod 2^k` and `H = (I, k, ℓ, α)`, and every `E ⊆ I`:
  `Rulers.ruler k I α μ E = R_H(E) − r_k(μ) · J_H(E)`.
Moreover, for every `m ≥ 0`, exactly one of `r_k(m)` and `r_k(m + K)` is `0`.

*Proof (from the paper).* In the sum `μ + o_E` the low part `ℓ + o_E` produces the carries of `κ(ℓ, o_E)`, and a carry out of bit `k − 1` exactly when `J_H(E) = 1`; that carry then runs through the `r_k(μ)` ones of `μ` that start at bit `k`, and stops. So `κ(μ, o_E) = κ(ℓ, o_E) + r_k(μ) J_H(E)`. For the last claim: `⌊(m + K)/K⌋ = ⌊m/K⌋ + 1`, and of two consecutive integers exactly one is even, i.e. has `v_2(· + 1) = 0`. ∎

**Lemma A′ (the cell is a penalty cell).** For `m ≥ 0`, `ℓ := m mod 2^k`, `H = (I, k, ℓ, α)`, `P_r := r_k(m)`, `P_c := r_k(m + K)` and `a, b, D ⊆ I`:
- `GoldenMatching.cHat k I α m a b = ĉ_H(a, b) − P_r J_H(a) + P_c J_H(b)`;
- `Rulers.ruler k I α m D − Rulers.ruler k I α (m + K) (I ∖ D) = x_H(D) − P_r J_H(D) + P_c J_H(I ∖ D)`.

(These are the costs and the clocks of the **penalty cell** `Cell(H; P_r, P_c)` of the paper; they follow from Lemma A applied to `m` and to `m + K`, which have the same residue `ℓ`.)

## Part B — windows and gates (Lemma 7.6)

Keep a house `H = (I, k, ℓ, α)`. For `t ∈ I`, the **window** of `t` is `W_t := [t, next(t))`, of length `h_t`. Its data:
- the **type** `T_t := bit_t(ℓ)`;
- for `u ≥ 0`, `r_u(ℓ) := v_2(⌊ℓ / 2^u⌋ + 1)`, the number of consecutive ones of `ℓ` starting at bit `u`;
- `κ_t := min(r_t(ℓ), h_t)` if `T_t = 1`, and `κ_t := 1 + min(r_{t+1}(ℓ), h_t − 1)` if `T_t = 0`;
- `sat_t := 1` if `κ_t = h_t`, else `0`;
- `τ_t := h_t − α 2^t − [T_t = 1] κ_t` (an integer).

For `E ⊆ I` and `u ≥ 0`, the **carry into bit `u`** in the sum `ℓ + o_E` is `c_u(E) := 1` if `(ℓ mod 2^u) + (o_E mod 2^u) ≥ 2^u`, else `0`. The **carries made by `W_t`** are `car_t(E) := #{u ∈ [t, next(t)) : c_{u+1}(E) = 1}`.

**Lemma B (Lemma 7.6).** Let `E ⊆ I`, `t ∈ I` and `d := [t ∈ E]`.
- (B1) If `I ≠ ∅`, `c_{min I}(E) = 0`.
- (B2) If `T_t = 1`: `car_t(E) = κ_t` if `d = 1` or `c_t(E) = 1`, and `car_t(E) = 0` otherwise.
- (B3) If `T_t = 0`: `car_t(E) = κ_t` if `d = 1` and `c_t(E) = 1`, and `car_t(E) = 0` otherwise.
- (B4) `c_{next(t)}(E) = 1` if and only if `car_t(E) > 0` and `sat_t = 1`.
- (B5) `R_H(E) = Σ_{t∈E} τ_t − Σ_{t∈I} κ_t · c_t(E) · [(T_t = 1 ∧ t ∉ E) ∨ (T_t = 0 ∧ t ∈ E)]`.
- (B6) `J_H(E) = c_k(E)`.

*Proof (from the paper).* Inside `W_t` the addend `o_E` has at most the bit `t`, and `ℓ` has the bit `T_t` at `t`. If `T_t = 1` and `d + c_t ≥ 1`, bit `t` carries, and the carry runs through the ones of `ℓ` at `t + 1, …`: there are `min(r_t(ℓ), h_t)` carries inside the window (for `d + c_t = 2` the carry out of bit `t` is the same and the run starts at `t + 1`, which gives the same count). If `T_t = 0`, bit `t` carries only when `d = c_t = 1`, and then the carry runs through the `r_{t+1}(ℓ)` ones above `t`. The carry leaves the window exactly when all its positions carry. Below `min I` the addend is zero, so no carry is born there; at and above bit `k` both addends are zero. Finally `κ(ℓ, o_E)` is the total number of carries, which is `Σ_{t∈I} car_t(E)`, and `Σ_{t∈E} κ_t [T_t = 1]` is absorbed into `τ`. ∎

## Part C — the top digit (Lemma 7.7)

Let `I ≠ ∅`, `c := max I`, `I' := I ∖ {c}`, and `H' := (I', c, ℓ mod 2^c, α)` (a house: `I' ⊆ {0, …, c − 1}`). Let `T := T_c`, `κ := κ_c`, `sat := sat_c`, `τ := τ_c` be the data of the window `W_c = [c, k)` of `H`, of length `h := k − c`. Write `R_{H'} = Rulers.ruler c I' α (ℓ mod 2^c)`, `J_{H'}`, `x_{H'}` and `γ' := Rulers.gamma c I'` for the objects of `H'`. For `D_0 ⊆ I'`:
- (C1) `R_H(D_0) = R_{H'}(D_0) − [T = 1] κ J_{H'}(D_0)`;
- (C2) `R_H(D_0 ∪ {c}) = τ + R_{H'}(D_0) − [T = 0] κ J_{H'}(D_0)`;
- (C3) `J_H(D_0) = [T = 1] · sat · J_{H'}(D_0)`;
- (C4) `J_H(D_0 ∪ {c}) = sat · ([T = 1] + [T = 0] J_{H'}(D_0))`;
- (C5) for `Δ ⊆ I` with `c ∉ Δ` and `Δ ≠ ∅`: `γ(Δ) = γ'(Δ) + h`; for `Δ_0 ⊆ I'`: `γ(Δ_0 ∪ {c}) = γ'(Δ_0)`;
- (C6) `x_H(D_0) = x_{H'}(D_0) + d_1(D_0)`, where `d_1(D_0) := −τ − [T = 1] κ J_{H'}(D_0) + [T = 0] κ J_{H'}(I' ∖ D_0)`;
- (C7) `x_H(D_0 ∪ {c}) = −(x_{H'}(I' ∖ D_0) + d_1(I' ∖ D_0))` (the second half is the mirror-negative of the first).

*Proof (from the paper).* The windows of the digits of `I'` are the same in `H` and in `H'` (the predecessor of `c` has `next = c` in both), with the same types and data; the carry into `W_c` is `c_c(E) = J_{H'}(E ∩ I')`. Apply Lemma B to `H` and to `H'`. For `γ`: the digit `c` is skipped by every non-empty `Δ ∌ c`, and is never skipped otherwise. The clocks follow by subtraction, with `I ∖ D_0 = (I' ∖ D_0) ∪ {c}`, and (C7) from Lemma A0. ∎

## Checks before formalization

`lean/chkC6.py` (log `logs/chkC6.log`): every statement, exhaustively, for every `k ≤ 6`, every `I ⊆ {0, …, k − 1}`, every `ℓ < 2^k`, `α ∈ {1, 2}`, every `E, D, D_0, Δ`; Lemma A for every `μ < 4·2^k`; Lemma A′ for every `m < 4·2^k`. Result (208 s, 10 MB): **0 failures** — Lemma A 447 896 cases, the «exactly one zero» claim 43 688, Lemma A′ 8 888 888 costs and 447 896 clocks, Lemma A0 1 279 072, Lemma B 1 204 724 (B1–B6), Lemma C 437 020 (C1–C7). Controls, each of which must fail somewhere: Lemma A with `r_k(μ)` replaced by `bit_k(μ)` (fires 36 596 times); (B3) without the `1 +` in `κ_t` (23 882); (C3) without the factor `sat` (1 564); (C5) without the `+ h` (45 192).
